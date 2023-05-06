//! The rlp decoding transaction list circuit implementation.

// Naming notes:
// - *_be: Big-Endian bytes
// - *_le: Little-Endian bytes

use crate::{
    evm_circuit::util::{constraint_builder::BaseConstraintBuilder, rlc},
    impl_expr,
    table::{KeccakTable, TxFieldTag, TxTable},
    util::{Challenges, SubCircuit, SubCircuitConfig},
    witness,
};
use eth_types::{
    sign_types::SignData, Address, Field, Signature, ToBigEndian, ToLittleEndian, ToScalar, ToWord,
    Transaction, Word,
};
use ethers_core::{types::TransactionRequest, utils::rlp};
use gadgets::{evm_word::r, util::not};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
    poly::Rotation,
};
// use itertools::Itertools;
// use log::error;
// use sign_verify::{AssignedSignatureVerify, SignVerifyChip, SignVerifyConfig};
// use std::marker::PhantomData;

pub use halo2_proofs::halo2curves::{
    group::{
        ff::{Field as GroupField, PrimeField},
        prime::PrimeCurveAffine,
        Curve, Group, GroupEncoding,
    },
    secp256k1::{self, Secp256k1Affine, Secp256k1Compressed},
};
use mock::MockTransaction;

use crate::util::Expr;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RlpDecodeTypeTag {
    SingleByte,  // 0x00 - 0x7f
    NullValue,   // 0x80
    ShortString, // 0x81~0x88 should be enough
    EmptyList,   // 0xc0
    LongList1,   // 0xc1 ~ 0xf7
    LongList2,   // 0xf8
    LongList3,   // 0xf9, 0xFFFF upto (64K)
    // LongList4,   // 0xfa, 0xFFFFFF upto (16M)
    PartialRlp, // for those rlp that is not complete
    RlpDecodeTypeNum,
}
impl_expr!(RlpDecodeTypeTag);

impl<T, const N: usize> std::ops::Index<RlpDecodeTypeTag> for [T; N] {
    type Output = T;

    fn index(&self, index: RlpDecodeTypeTag) -> &Self::Output {
        &self[index as usize]
    }
}

impl<T> std::ops::Index<RlpDecodeTypeTag> for Vec<T> {
    type Output = T;

    fn index(&self, index: RlpDecodeTypeTag) -> &Self::Output {
        &self[index as usize]
    }
}

// single, null, short, long1, long2, long3, long4, partial, length, r_mult
//      1,     0,    0,     0,     0,     0,     0,     0,      1~3,   r^(0~2)
//      0,     1,    0,     0,     0,     0,     0,     0,      1,     r^0
//      0,     0,    1,     0,     0,     0,     0,     0,      1~33,  r^(0~32)
//      0,     0,    1,     0,     0,     0,     0,     0,      2,     r^1
//                   .
//      0,     0,    0,     1,     0,     0,     0,     0,      1~33,  r^(0~32)
//      0,     0,    0,     0,     1,     0,     0,     0,      1~33,  r^(0~32)
//      0,     0,    0,     0,     0,     1,     0,     0,      1~33,  r^(0~32)
//      0,     0,    0,     0,     0,     0,     1,     0,      1~33,  r^(0~32)
//      0,     0,    0,     0,     0,     0,     0,     1,      1~33,  r^(0~32)
#[derive(Clone, Debug)]
struct RlpDecodeTable {
    rlp_type: [Column<Fixed>; RlpDecodeTypeTag::RlpDecodeTypeNum as usize],
    bytes_length: Column<Fixed>, // max 33 bytes
    r_mult: Column<Advice>,
}

// TODO: combine with TxFieldTag in table.rs
/// Marker that defines whether an Operation performs a `READ` or a `WRITE`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RlpTxFieldTag {
    // for legacy tx
    Nonce,
    GasPrice,
    Gas,
    To,
    Value,
    Data,
    SignV,
    SignR,
    SignS,
    Padding,
    // 1559 extra field
    ChainID,
    GasTipCap,
    GasFeeCap,
    AccessList,
}
impl_expr!(RlpTxFieldTag);

impl<T, const N: usize> std::ops::Index<RlpTxFieldTag> for [T; N] {
    type Output = T;

    fn index(&self, index: RlpTxFieldTag) -> &Self::Output {
        &self[index as usize]
    }
}

impl<T> std::ops::Index<RlpTxFieldTag> for Vec<T> {
    type Output = T;

    fn index(&self, index: RlpTxFieldTag) -> &Self::Output {
        &self[index as usize]
    }
}

const LegacyTxFieldNum: usize = RlpTxFieldTag::Padding as usize + 1 as usize;
const Tx1559TxFieldNum: usize = RlpTxFieldTag::AccessList as usize + 1 as usize;

// TODO: combine with TxFieldTag in table.rs
/// Marker that defines whether an Operation performs a `READ` or a `WRITE`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RlpTxTypeTag {
    TxLegacyType,
    Tx1559Type,
}
impl_expr!(RlpTxTypeTag);

const MAX_BYTE_COLUMN: usize = 33;

/// Config for RlpDecoderCircuit
#[derive(Clone, Debug)]
pub struct RlpDecoderCircuitConfig<F: Field> {
    /// tx_id column
    pub tx_id: Column<Advice>,
    /// tx_type column
    pub tx_type: Column<Advice>,
    /// tag column
    pub tag: Column<Advice>,
    /// complete column
    pub complete: Column<Advice>,
    /// rlp types: [single, short, long, very_long, fixed(33)]
    pub rlp_types: [Column<Advice>; RlpDecodeTypeTag::RlpDecodeTypeNum as usize],
    /// rlp_tag_length, the length of this rlp field
    pub rlp_tag_length: Column<Advice>,
    /// remained rows, for n < 33 fields, it is n, for m > 33 fields, it is 33 and next row is
    /// partial, next_length = m - 33
    pub tag_bytes_in_row: Column<Advice>,
    /// r_mult column, (length, r_mult) => @fixed
    pub r_mult: Column<Advice>,
    /// remain_length
    pub rlp_remain_length: Column<Advice>,
    /// value
    pub value: Column<Advice>,
    /// acc_rlc_value
    pub acc_rlc_value: Column<Advice>,
    /// bytes
    pub bytes: [Column<Advice>; MAX_BYTE_COLUMN],
    /// decodable, 0 for decode failed, 1 for success
    pub decodable: Column<Advice>,
    /// valid, 0 for invalid, 1 for valid, should be == decodable at the end of the circuit
    pub valid: Column<Advice>,
    /// dynamic selector for fields
    pub q_fields: [Column<Advice>; LegacyTxFieldNum as usize],
    /// full chip enable
    pub q_enable: Selector,
    /// the begining
    pub q_first: Column<Fixed>,
    /// the end
    pub q_last: Column<Fixed>,
    /// args
    pub args: RlpDecoderCircuitConfigArgs<F>,
}

#[derive(Clone, Debug)]
/// Circuit configuration arguments
pub struct RlpDecoderCircuitConfigArgs<F: Field> {
    /// TxTable
    pub tx_table: TxTable,
    /// KeccakTable
    pub keccak_table: KeccakTable,
    /// Challenges
    pub challenges: Challenges<Expression<F>>,
}

impl<F: Field> SubCircuitConfig<F> for RlpDecoderCircuitConfig<F> {
    type ConfigArgs = RlpDecoderCircuitConfigArgs<F>;

    /// Return a new RlpDecoderCircuitConfig
    fn new(meta: &mut ConstraintSystem<F>, args: Self::ConfigArgs) -> Self {
        let tx_id = meta.advice_column();
        let tx_type = meta.advice_column();
        let tag = meta.advice_column();
        let complete = meta.advice_column();
        let rlp_types = [meta.advice_column(); RlpDecodeTypeTag::RlpDecodeTypeNum as usize];
        let rlp_tag_length = meta.advice_column();
        let tag_bytes_in_row = meta.advice_column();
        let rlp_remain_length = meta.advice_column();
        let r_mult = meta.advice_column();
        let value = meta.advice_column();
        let acc_rlc_value = meta.advice_column();
        let bytes = [meta.advice_column(); 33];
        let decodable = meta.advice_column();
        let valid = meta.advice_column();
        let q_fields = [meta.advice_column(); LegacyTxFieldNum];
        let q_enable = meta.selector();
        let q_first = meta.fixed_column();
        let q_last = meta.fixed_column();

        // common logic
        meta.create_gate("common", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let tx_id = meta.query_advice(tx_id, Rotation::cur());
            let tx_type = meta.query_advice(tx_type, Rotation::cur());
            let tag = meta.query_advice(tag, Rotation::cur());
            let complete_cur = meta.query_advice(complete, Rotation::cur());
            let rlp_types_cur: [Expression<F>; RlpDecodeTypeTag::RlpDecodeTypeNum as usize] =
                rlp_types
                    .iter()
                    .map(|rlp_type| meta.query_advice(*rlp_type, Rotation::cur()))
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
            let rlp_tag_length_cur = meta.query_advice(rlp_tag_length, Rotation::cur());
            let r_mult = meta.query_advice(r_mult, Rotation::cur());
            let tag_bytes_in_row_cur = meta.query_advice(tag_bytes_in_row, Rotation::cur());
            let remain_length = meta.query_advice(rlp_remain_length, Rotation::cur());
            let value = meta.query_advice(value, Rotation::cur());
            let acc_rlc_cur = meta.query_advice(acc_rlc_value, Rotation::cur());
            let bytes = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let decodable = meta.query_advice(decodable, Rotation::cur());
            let valid = meta.query_advice(valid, Rotation::cur());
            let q_fields: Vec<Expression<F>> = q_fields
                .iter()
                .map(|q_col| meta.query_advice(*q_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let q_enable = meta.query_selector(q_enable);

            // cb.require_boolean("q_enable boolean", q_enable);
            cb.require_boolean("field complete boolean", complete_cur.expr());
            q_fields.iter().for_each(|q_col| {
                cb.require_boolean("q_fields boolean", q_col.expr());
            });
            cb.require_boolean("decodable", decodable);
            cb.require_boolean("valid", valid);

            rlp_types_cur.iter().for_each(|rlp_type_cur| {
                cb.require_boolean("rlp_type boolean", rlp_type_cur.expr());
            });

            // length without leading bytes
            cb.condition(rlp_types_cur[RlpDecodeTypeTag::SingleByte].expr(), |cb| {
                cb.require_equal("single length", rlp_tag_length_cur.clone(), 1.expr())
            });
            cb.condition(rlp_types_cur[RlpDecodeTypeTag::NullValue].expr(), |cb| {
                cb.require_equal("empty length", rlp_tag_length_cur.clone(), 0.expr())
            });
            cb.condition(rlp_types_cur[RlpDecodeTypeTag::ShortString].expr(), |cb| {
                cb.require_equal(
                    "single string length",
                    rlp_tag_length_cur.clone(),
                    bytes[0].expr() - 0x80.expr(),
                )
            });
            cb.condition(rlp_types_cur[RlpDecodeTypeTag::EmptyList].expr(), |cb| {
                cb.require_equal("empty list length", rlp_tag_length_cur.clone(), 0.expr())
            });
            cb.condition(rlp_types_cur[RlpDecodeTypeTag::LongList1].expr(), |cb| {
                cb.require_equal(
                    "short length",
                    rlp_tag_length_cur.clone(),
                    bytes[0].expr() - 0xc0.expr(),
                )
            });
            cb.condition(rlp_types_cur[RlpDecodeTypeTag::LongList2].expr(), |cb| {
                cb.require_equal("long length", rlp_tag_length_cur.clone(), bytes[1].expr())
            });
            cb.condition(rlp_types_cur[RlpDecodeTypeTag::LongList3].expr(), |cb| {
                cb.require_equal(
                    "long length",
                    rlp_tag_length_cur.clone(),
                    bytes[1].expr() * 256.expr() + bytes[2].expr(),
                )
            });
            cb.condition(rlp_types_cur[RlpDecodeTypeTag::PartialRlp].expr(), |cb| {
                cb.require_equal(
                    "length = prev_length - prev_bytes_in_row",
                    rlp_tag_length_cur.clone(),
                    meta.query_advice(rlp_tag_length, Rotation::prev())
                        - tag_bytes_in_row_cur.expr(),
                );

                cb.require_zero(
                    "above row is incomplete",
                    meta.query_advice(complete, Rotation::prev()),
                );
            });

            cb.condition(complete_cur.expr(), |cb| {
                cb.require_equal(
                    "complete = 1 => remain_length = bytes_in_row",
                    tag_bytes_in_row_cur.expr(),
                    remain_length.expr(),
                );

                cb.require_equal(
                    "rlp_remain_length = rlp_remain_length.prev - length",
                    remain_length.expr(),
                    meta.query_advice(rlp_remain_length, Rotation::prev())
                        - tag_bytes_in_row_cur.expr(),
                );
            });

            cb.require_equal(
                "rlc = r_mult_cur * rlc_next + rlc(bytes_cur)",
                acc_rlc_cur,
                r_mult * meta.query_advice(acc_rlc_value, Rotation::next())
                    + rlc::expr(
                        bytes.iter().rev().collect::<Vec<_>>().as_ref(),
                        &args.challenges.keccak_input(),
                    ),
            );

            // TODO: lookup rlp_types table
            // TODO: lookup r_mult table
            // TODO: lookup bytes range table
            cb.gate(q_enable)
        });

        // TxListHeader in the first row
        meta.create_gate("txListHeader", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let tx_id = meta.query_advice(tx_id, Rotation::cur());
            let tx_type_cur = meta.query_advice(tx_type, Rotation::cur());
            let tag_cur = meta.query_advice(tag, Rotation::cur());
            let tag_next = meta.query_advice(tag, Rotation::next());
            let complete = meta.query_advice(complete, Rotation::cur());
            let length = meta.query_advice(rlp_tag_length, Rotation::cur());
            let r_mult = meta.query_advice(r_mult, Rotation::cur());
            let remain_length = meta.query_advice(rlp_remain_length, Rotation::cur());
            let value = meta.query_advice(value, Rotation::cur());
            let acc_rlc_value = meta.query_advice(acc_rlc_value, Rotation::cur());
            let bytes = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let decodable = meta.query_advice(decodable, Rotation::cur());
            let valid = meta.query_advice(valid, Rotation::cur());
            let q_first = meta.query_fixed(q_first, Rotation::cur());

            cb.require_zero("0 tx_id", tx_id);
            cb.require_zero("0 tx_type", tx_type_cur.expr());
            cb.require_zero("0 tx_tag", tag_cur);
            cb.require_equal("field completed", complete.expr(), 1.expr());

            // next should be nonce if legacy(0) or chain_id if 1559
            cb.condition(not::expr(tx_type_cur.expr()), |cb| {
                let tx_type_next = meta.query_advice(tx_type, Rotation::next());
                cb.require_equal(
                    "next tx is legacy",
                    tx_type_next,
                    RlpTxTypeTag::TxLegacyType.expr(),
                );
                cb.require_equal("next field is nonce", tag_next, RlpTxFieldTag::Nonce.expr());
            });

            // TODO: enable 1559
            // cb.condition("tx 1559", |cb| {
            //     let next_tx_type = meta.query_advice(tx_type, Rotation::next());
            //     cb.require_equal(
            //         "next tx is 1559",
            //         next_tx_type,
            //         RlpTxTypeTag::Tx1559Type.expr(),
            //     );
            //     cb.require_equal(
            //         "next field is nonce",
            //         next_tag,
            //         RlpTxFieldTag::ChainID.expr(),
            //     );
            // });

            cb.condition(decodable, |cb| {
                // TODO: use look up??
                cb.require_in_set(
                    "list header in [0xf8,0xf9,0xfa]",
                    bytes[0].expr(),
                    vec![248.expr(), 249.expr(), 250.expr()],
                )
            });

            cb.gate(q_first)
        });

        // Nonce
        meta.create_gate("Nonce", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let tag_cur = meta.query_advice(tag, Rotation::cur());
            let complete = meta.query_advice(complete, Rotation::cur());
            let rlp_types = rlp_types
                .iter()
                .map(|rlp_type| meta.query_advice(*rlp_type, Rotation::cur()))
                .collect::<Vec<_>>();
            let bytes = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let decodable = meta.query_advice(decodable, Rotation::cur());
            let q_fields = q_fields
                .iter()
                .map(|q_col| meta.query_advice(*q_col, Rotation::cur()))
                .collect::<Vec<_>>();

            cb.require_equal("nonce tag", tag_cur, RlpTxFieldTag::Nonce.expr());
            cb.require_equal("field completed", complete.expr(), 1.expr());
            // next is gas_price
            cb.require_equal(
                "next field is gas_price",
                meta.query_advice(tag, Rotation::next()),
                RlpTxFieldTag::GasPrice.expr(),
            );

            cb.require_equal(
                "decodable if not null",
                decodable,
                not::expr(rlp_types[RlpDecodeTypeTag::NullValue].expr()),
            );

            // TODO: lookup nonce rlp_type table, should be single or short
            cb.gate(q_fields[RlpTxFieldTag::Nonce].expr() * meta.query_selector(q_enable))
        });

        // gas price
        meta.create_gate("Gas price", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let tag_cur = meta.query_advice(tag, Rotation::cur());
            let complete = meta.query_advice(complete, Rotation::cur());
            let rlp_types = rlp_types
                .iter()
                .map(|rlp_type| meta.query_advice(*rlp_type, Rotation::cur()))
                .collect::<Vec<_>>();

            let bytes = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let decodable = meta.query_advice(decodable, Rotation::cur());
            let q_fields = q_fields
                .iter()
                .map(|q_col| meta.query_advice(*q_col, Rotation::cur()))
                .collect::<Vec<_>>();

            cb.require_equal("gas price tag", tag_cur, RlpTxFieldTag::GasPrice.expr());
            // next is gas_price
            cb.require_equal(
                "next field is gas_limit",
                meta.query_advice(tag, Rotation::next()),
                RlpTxFieldTag::Gas.expr(),
            );

            cb.require_equal(
                "decodable if not null",
                decodable,
                not::expr(rlp_types[RlpDecodeTypeTag::NullValue].expr()),
            );

            cb.gate(q_fields[RlpTxFieldTag::GasPrice].expr() * meta.query_selector(q_enable))
        });

        // Gas
        meta.create_gate("Gas", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let tag_cur = meta.query_advice(tag, Rotation::cur());
            let complete = meta.query_advice(complete, Rotation::cur());
            let rlp_types = rlp_types
                .iter()
                .map(|rlp_type| meta.query_advice(*rlp_type, Rotation::cur()))
                .collect::<Vec<_>>();
            let bytes = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let decodable = meta.query_advice(decodable, Rotation::cur());
            let q_fields = q_fields
                .iter()
                .map(|q_col| meta.query_advice(*q_col, Rotation::cur()))
                .collect::<Vec<_>>();

            cb.require_equal("tag", tag_cur, RlpTxFieldTag::Gas.expr());
            cb.require_equal("field completed", complete.expr(), 1.expr());
            cb.require_equal(
                "next field is To",
                meta.query_advice(tag, Rotation::next()),
                RlpTxFieldTag::To.expr(),
            );

            cb.require_equal(
                "decodable if not null",
                decodable,
                not::expr(rlp_types[RlpDecodeTypeTag::NullValue].expr()),
            );

            cb.gate(q_fields[RlpTxFieldTag::Gas].expr() * meta.query_selector(q_enable))
        });

        // To
        meta.create_gate("To", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let tag_cur = meta.query_advice(tag, Rotation::cur());
            let complete = meta.query_advice(complete, Rotation::cur());
            let bytes = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let decodable = meta.query_advice(decodable, Rotation::cur());
            let q_fields = q_fields
                .iter()
                .map(|q_col| meta.query_advice(*q_col, Rotation::cur()))
                .collect::<Vec<_>>();

            cb.require_equal("tag", tag_cur, RlpTxFieldTag::To.expr());
            cb.require_equal("field completed", complete.expr(), 1.expr());
            cb.require_equal(
                "next field is Value",
                meta.query_advice(tag, Rotation::next()),
                RlpTxFieldTag::Value.expr(),
            );

            // TODO: Lookup fix length 0xa0/0x80
            cb.require_in_set(
                "0xa0 or 0x80",
                bytes[0].expr(),
                vec![160.expr(), 128.expr()],
            );

            cb.gate(q_fields[RlpTxFieldTag::To].expr() * meta.query_selector(q_enable))
        });

        // Value
        meta.create_gate("Value", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let tag_cur = meta.query_advice(tag, Rotation::cur());
            let complete = meta.query_advice(complete, Rotation::cur());
            let bytes = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let decodable = meta.query_advice(decodable, Rotation::cur());
            let q_fields = q_fields
                .iter()
                .map(|q_col| meta.query_advice(*q_col, Rotation::cur()))
                .collect::<Vec<_>>();

            cb.require_equal("tag", tag_cur, RlpTxFieldTag::Value.expr());
            cb.require_equal("field completed", complete.expr(), 1.expr());
            cb.require_equal(
                "next field is Data",
                meta.query_advice(tag, Rotation::next()),
                RlpTxFieldTag::Data.expr(),
            );

            cb.gate(q_fields[RlpTxFieldTag::Value].expr() * meta.query_selector(q_enable))
        });

        // Data
        meta.create_gate("Data", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let tag_cur = meta.query_advice(tag, Rotation::cur());
            let complete = meta.query_advice(complete, Rotation::cur());
            let bytes = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let decodable = meta.query_advice(decodable, Rotation::cur());
            let q_fields = q_fields
                .iter()
                .map(|q_col| meta.query_advice(*q_col, Rotation::cur()))
                .collect::<Vec<_>>();

            cb.require_equal("tag", tag_cur, RlpTxFieldTag::Data.expr());
            cb.require_equal("field completed", complete.expr(), 1.expr());
            cb.require_equal(
                "next field is SignV",
                meta.query_advice(tag, Rotation::next()),
                RlpTxFieldTag::SignV.expr(),
            );

            cb.gate(q_fields[RlpTxFieldTag::Data].expr() * meta.query_selector(q_enable))
        });

        // V
        meta.create_gate("SignV", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let tag_cur = meta.query_advice(tag, Rotation::cur());
            let complete = meta.query_advice(complete, Rotation::cur());
            let bytes = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let decodable = meta.query_advice(decodable, Rotation::cur());
            let q_fields = q_fields
                .iter()
                .map(|q_col| meta.query_advice(*q_col, Rotation::cur()))
                .collect::<Vec<_>>();

            cb.require_equal("tag", tag_cur, RlpTxFieldTag::SignV.expr());
            cb.require_equal("field completed", complete.expr(), 1.expr());
            cb.require_equal(
                "next field is SignR",
                meta.query_advice(tag, Rotation::next()),
                RlpTxFieldTag::SignR.expr(),
            );

            cb.gate(q_fields[RlpTxFieldTag::SignV].expr() * meta.query_selector(q_enable))
        });

        // R
        meta.create_gate("SignR", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let tag_cur = meta.query_advice(tag, Rotation::cur());
            let complete = meta.query_advice(complete, Rotation::cur());
            let bytes = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let decodable = meta.query_advice(decodable, Rotation::cur());
            let q_fields = q_fields
                .iter()
                .map(|q_col| meta.query_advice(*q_col, Rotation::cur()))
                .collect::<Vec<_>>();

            cb.require_equal("tag", tag_cur, RlpTxFieldTag::SignR.expr());
            cb.require_equal("field completed", complete.expr(), 1.expr());

            cb.require_equal(
                "decodable if valid rlp header",
                not::expr(decodable),
                bytes[0].expr() - 0xa0.expr(),
            );

            // next is signS
            cb.require_equal(
                "next field is SignR",
                meta.query_advice(tag, Rotation::next()),
                RlpTxFieldTag::SignS.expr(),
            );

            cb.gate(q_fields[RlpTxFieldTag::SignR].expr() * meta.query_selector(q_enable))
        });

        // S
        meta.create_gate("SignS", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let tag_cur = meta.query_advice(tag, Rotation::cur());
            let complete = meta.query_advice(complete, Rotation::cur());
            let bytes = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let decodable = meta.query_advice(decodable, Rotation::cur());
            let q_fields = q_fields
                .iter()
                .map(|q_col| meta.query_advice(*q_col, Rotation::cur()))
                .collect::<Vec<_>>();

            cb.require_equal("tag", tag_cur, RlpTxFieldTag::SignS.expr());
            cb.require_equal("field completed", complete.expr(), 1.expr());
            // next is a new tx or padding
            cb.require_in_set(
                "next field is Nonce or Padding",
                meta.query_advice(tag, Rotation::next()),
                vec![RlpTxFieldTag::Nonce.expr(), RlpTxFieldTag::Padding.expr()],
            );

            cb.gate(q_fields[RlpTxFieldTag::SignS].expr() * meta.query_selector(q_enable))
        });

        // padding
        meta.create_gate("Padding", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let tag_cur = meta.query_advice(tag, Rotation::cur());
            let complete = meta.query_advice(complete, Rotation::cur());
            let length = meta.query_advice(rlp_tag_length, Rotation::cur());
            let r_mult = meta.query_advice(r_mult, Rotation::cur());
            let remain_length = meta.query_advice(rlp_remain_length, Rotation::cur());
            let value = meta.query_advice(value, Rotation::cur());
            let acc_rlc_value = meta.query_advice(acc_rlc_value, Rotation::cur());
            let bytes = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let decodable = meta.query_advice(decodable, Rotation::cur());
            let q_last = meta.query_fixed(q_last, Rotation::cur());
            let q_fields = q_fields
                .iter()
                .map(|q_col| meta.query_advice(*q_col, Rotation::cur()))
                .collect::<Vec<_>>();

            cb.require_equal("tag", tag_cur, RlpTxFieldTag::Padding.expr());
            cb.require_equal("field completed", complete.expr(), 1.expr());
            // next is a new tx or padding
            cb.require_in_set(
                "next field is Padding or next tx nonce",
                meta.query_advice(tag, Rotation::next()),
                vec![RlpTxFieldTag::Nonce.expr(), RlpTxFieldTag::Padding.expr()],
            );
            cb.require_equal("padding has no r_mult", r_mult, 0.expr());
            cb.require_equal("padding has no length", length, 0.expr());
            cb.require_equal("padding has no remain length", remain_length, 0.expr());
            cb.require_equal("padding has no rlc (all 0)", acc_rlc_value, 0.expr());

            cb.gate(
                q_fields[RlpTxFieldTag::Padding].expr()
                    * not::expr(q_last)
                    * meta.query_selector(q_enable),
            )
        });

        meta.create_gate("end logic", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let complete = meta.query_advice(complete, Rotation::cur());
            let tag_cur = meta.query_advice(tag, Rotation::cur());
            let length = meta.query_advice(rlp_tag_length, Rotation::cur());
            let r_mult = meta.query_advice(r_mult, Rotation::cur());
            let remain_length = meta.query_advice(rlp_remain_length, Rotation::cur());
            let value = meta.query_advice(value, Rotation::cur());
            let acc_rlc_value = meta.query_advice(acc_rlc_value, Rotation::cur());
            let bytes = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let decodable = meta.query_advice(decodable, Rotation::cur());
            let valid = meta.query_advice(valid, Rotation::cur());
            let q_enable = meta.query_selector(q_enable);
            let q_last = meta.query_fixed(q_last, Rotation::cur());

            cb.require_equal("padding at last", tag_cur, RlpTxFieldTag::Padding.expr());
            cb.require_equal("padding has no r_mult", r_mult, 0.expr());
            cb.require_equal("padding has no length", length, 0.expr());
            cb.require_equal("padding has no remain length", remain_length, 0.expr());
            cb.require_equal("padding has no rlc (all 0)", acc_rlc_value, 0.expr());
            cb.require_equal("valid == decodable", valid, decodable);

            cb.gate(q_last)
        });

        Self {
            tx_id,
            tx_type,
            tag,
            complete,
            rlp_types,
            rlp_tag_length,
            tag_bytes_in_row,
            r_mult,
            rlp_remain_length,
            value,
            acc_rlc_value,
            bytes,
            decodable,
            valid,
            q_fields,
            q_enable,
            q_first,
            q_last,
            args,
        }
    }
}

impl<F: Field> RlpDecoderCircuitConfig<F> {
    fn assign_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: u8,
    ) -> Result<AssignedCell<F, F>, Error> {
        todo!()
    }

    /// Get number of rows required.
    pub fn get_num_rows_required(num_tx: usize) -> usize {
        return 0;
    }
}

/// rlp decode Circuit for verifying transaction signatures
#[derive(Clone, Default, Debug)]
pub struct RlpDecoderCircuit<F: Field> {
    /// Max number of supported transactions
    pub max_txs: usize,
    /// Max number of supported calldata bytes
    pub max_calldata: usize,
    /// input bytes
    pub bytes: Vec<u8>,
    /// phantom
    pub _marker: std::marker::PhantomData<F>,
}

impl<F: Field> RlpDecoderCircuit<F> {
    /// Return a new RlpDecoderCircuit
    pub fn new(max_txs: usize, max_calldata: usize, bytes: Vec<u8>) -> Self {
        RlpDecoderCircuit::<F> {
            max_txs,
            max_calldata,
            bytes,
            _marker: std::marker::PhantomData,
        }
    }

    /// Return the minimum number of rows required to prove an input of a
    /// particular size.
    pub fn min_num_rows(txs_len: usize, call_data_len: usize) -> usize {
        0
    }
}

impl<F: Field> SubCircuit<F> for RlpDecoderCircuit<F> {
    type Config = RlpDecoderCircuitConfig<F>;

    fn new_from_block(block: &witness::Block<F>) -> Self {
        Self::new(
            block.circuits_params.max_txs,
            block.circuits_params.max_calldata,
            Vec::<u8>::new(),
        )
    }

    /// Return the minimum number of rows required to prove the block
    fn min_num_rows_block(block: &witness::Block<F>) -> (usize, usize) {
        (
            Self::min_num_rows(
                block.txs.len(),
                block.txs.iter().map(|tx| tx.call_data.len()).sum(),
            ),
            Self::min_num_rows(
                block.circuits_params.max_txs,
                block.circuits_params.max_calldata,
            ),
        )
    }

    /// Make the assignments to the RlpDecodeCircuit
    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn instance(&self) -> Vec<Vec<F>> {
        // The maingate expects an instance column, but we don't use it, so we return an
        // "empty" instance column
        vec![vec![]]
    }
}

#[cfg(any(feature = "test", test, feature = "test-circuits"))]
impl<F: Field> Circuit<F> for RlpDecoderCircuit<F> {
    type Config = (RlpDecoderCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let tx_table = TxTable::construct(meta);
        let keccak_table = KeccakTable::construct(meta);
        let challenges = Challenges::construct(meta);

        let config = {
            let challenges = challenges.exprs(meta);
            RlpDecoderCircuitConfig::new(
                meta,
                RlpDecoderCircuitConfigArgs {
                    tx_table,
                    keccak_table,
                    challenges,
                },
            )
        };

        (config, challenges)
    }

    fn synthesize(
        &self,
        (config, challenges): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        Ok(())
    }
}

trait RlpWitness {
    fn generate_rlp_decoded_witness(&self) -> Vec<u8>;
}

impl RlpWitness for Transaction {
    fn generate_rlp_decoded_witness(&self) -> Vec<u8> {
        // TODO: use offset to split the input bytes
        let mut bytes = Vec::new();
        bytes.extend_from_slice(rlp::encode(&self.nonce).as_ref());
        bytes.extend_from_slice(rlp::encode(&self.gas_price).as_ref());
        bytes.extend_from_slice(rlp::encode(&self.gas).as_ref());
        bytes.extend_from_slice(rlp::encode(&self.to).as_ref());
        bytes.extend_from_slice(rlp::encode(&self.value).as_ref());
        bytes.extend_from_slice(rlp::encode(&self.input.as_ref()).as_ref());
        bytes.extend_from_slice(rlp::encode(&self.v).as_ref());
        bytes.extend_from_slice(rlp::encode(&self.r).as_ref());
        bytes.extend_from_slice(rlp::encode(&self.s).as_ref());
        bytes
    }
}

fn rlp_decode(bytes: Vec<u8>) -> Result<Vec<u8>, Error> {
    match rlp::Rlp::new(&bytes).as_list::<Transaction>() {
        Ok(txlist) => {
            // TODO: check txs.len() <= max_txs
            let mut bytes = Vec::new();
            for tx in txlist {
                let witness = tx.generate_rlp_decoded_witness();
                bytes.extend_from_slice(&witness)
            }
            Ok(bytes)
        }
        Err(e) => rlp_decode_tx_list_manually(&bytes),
    }
}

fn rlp_decode_tx_list_manually(bytes: &Vec<u8>) -> Result<Vec<u8>, Error> {
    let mut bytes = Vec::new();
    bytes.push(0xc8); // empty []

    Ok(bytes)
}

/// Signed transaction in a witness block
#[derive(Debug, Clone)]
pub struct SignedTransaction {
    /// Transaction data.
    pub tx: Transaction,
    /// ECDSA signature on the transaction.
    pub signature: ethers_core::types::Signature,
}

use rlp::{Encodable, RlpStream};

impl Encodable for SignedTransaction {
    fn rlp_append(&self, s: &mut RlpStream) {
        s.begin_list(9);
        s.append(&Word::from(self.tx.nonce));
        s.append(&self.tx.gas_price.unwrap());
        s.append(&Word::from(self.tx.gas));
        if let Some(addr) = self.tx.to {
            s.append(&addr);
        } else {
            s.append(&"");
        }
        s.append(&self.tx.value);
        s.append(&self.tx.input.to_vec());
        s.append(&self.signature.v);
        s.append(&self.signature.r);
        s.append(&self.signature.s);
    }
}

impl From<&Transaction> for SignedTransaction {
    fn from(tx: &Transaction) -> Self {
        Self {
            tx: tx.clone(),
            signature: ethers_core::types::Signature {
                v: tx.v.as_u64(),
                r: tx.r,
                s: tx.s,
            },
        }
    }
}

impl From<MockTransaction> for SignedTransaction {
    fn from(mock_tx: MockTransaction) -> Self {
        let tx = {
            let is_create = mock_tx.to.is_none();
            let sig = Signature {
                r: mock_tx.r.expect("tx expected to be signed"),
                s: mock_tx.s.expect("tx expected to be signed"),
                v: mock_tx.v.expect("tx expected to be signed").as_u64(),
            };
            let (rlp_unsigned, rlp_signed) = {
                let mut legacy_tx = TransactionRequest::new()
                    .from(mock_tx.from.address())
                    .nonce(mock_tx.nonce)
                    .gas_price(mock_tx.gas_price)
                    .gas(mock_tx.gas)
                    .value(mock_tx.value)
                    .data(mock_tx.input.clone())
                    .chain_id(mock_tx.chain_id.as_u64());
                if !is_create {
                    legacy_tx = legacy_tx.to(mock_tx.to.as_ref().map(|to| to.address()).unwrap());
                }

                let unsigned = legacy_tx.rlp().to_vec();

                let signed = legacy_tx.rlp_signed(&sig).to_vec();

                (unsigned, signed)
            };
            Transaction {
                hash: mock_tx.hash.unwrap(),
                nonce: mock_tx.nonce,
                gas_price: Some(mock_tx.gas_price),
                gas: mock_tx.gas,
                to: mock_tx.to.map(|to| to.address()),
                value: mock_tx.value,
                input: mock_tx.input,
                v: mock_tx.v.unwrap(),
                r: mock_tx.r.unwrap(),
                s: mock_tx.s.unwrap(),
                ..Default::default()
            }
        };
        SignedTransaction::from(&tx)
    }
}

#[cfg(test)]
mod rlp_test {
    use super::SignedTransaction;
    use ethers_core::utils::rlp;
    use hex;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    #[test]
    fn test_decode() {
        let tx: SignedTransaction = mock::CORRECT_MOCK_TXS[1].clone().into();
        let rlp_tx = rlp::encode(&tx);
        println!("{:?}", hex::encode(rlp_tx));

        let txs: Vec<SignedTransaction> = vec![
            mock::CORRECT_MOCK_TXS[0].clone().into(),
            mock::CORRECT_MOCK_TXS[1].clone().into(),
            // mock::CORRECT_MOCK_TXS[2].clone().into(),
        ];
        let rlp_txs = rlp::encode_list(&txs);
        println!("{:?}", hex::encode(rlp_txs.clone()));

        let dec_txs = rlp::Rlp::new(rlp_txs.to_vec().as_slice())
            .as_list::<eth_types::Transaction>()
            .unwrap();
        println!("{:?}", dec_txs);
    }

    #[test]
    fn test_encode() {
        let mut rng = ChaCha20Rng::seed_from_u64(2u64);
        let tx: SignedTransaction = mock::MockTransaction::default()
            .from(mock::AddrOrWallet::random(&mut rng))
            .to(mock::AddrOrWallet::random(&mut rng))
            .nonce(eth_types::word!("0x106"))
            .value(eth_types::word!("0x3e8"))
            .gas_price(eth_types::word!("0x4d2"))
            .input(eth_types::Bytes::from(
                b"hellohellohellohellohellohellohellohellohellohellohellohello",
            ))
            .build()
            .into();
        let rlp_tx = rlp::encode(&tx);
        println!("{:?}", hex::encode(rlp_tx));
    }
}

#[cfg(test)]
mod rlp_decode_circuit_tests {
    use super::*;
    use crate::util::log2_ceil;
    use eth_types::address;
    use halo2_proofs::{
        dev::{MockProver, VerifyFailure},
        halo2curves::bn256::Fr,
    };
    use mock::AddrOrWallet;
    use pretty_assertions::assert_eq;

    const NUM_BLINDING_ROWS: usize = 64;

    fn run<F: Field>(
        txs: Vec<Transaction>,
        chain_id: u64,
        max_txs: usize,
        max_calldata: usize,
    ) -> Result<(), Vec<VerifyFailure>> {
        let k = log2_ceil(
            NUM_BLINDING_ROWS + RlpDecoderCircuit::<Fr>::min_num_rows(max_txs, max_calldata),
        );
        // SignVerifyChip -> ECDSAChip -> MainGate instance column
        let circuit = RlpDecoderCircuit::<F>::new(max_txs, max_calldata, vec![]);

        let prover = match MockProver::run(k, &circuit, vec![]) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        prover.verify()
    }

    #[test]
    fn tx_circuit_1tx_1max_tx() {
        const MAX_TXS: usize = 1;
        const MAX_CALLDATA: usize = 32;

        let chain_id: u64 = mock::MOCK_CHAIN_ID.as_u64();

        let tx: Transaction = mock::CORRECT_MOCK_TXS[0].clone().into();

        assert_eq!(run::<Fr>(vec![tx], chain_id, MAX_TXS, MAX_CALLDATA), Ok(()));
    }

    #[test]
    fn tx_circuit_1tx_2max_tx() {
        const MAX_TXS: usize = 2;
        const MAX_CALLDATA: usize = 32;

        let chain_id: u64 = mock::MOCK_CHAIN_ID.as_u64();

        let tx: Transaction = mock::CORRECT_MOCK_TXS[0].clone().into();

        assert_eq!(run::<Fr>(vec![tx], chain_id, MAX_TXS, MAX_CALLDATA), Ok(()));
    }

    #[test]
    fn tx_circuit_bad_address() {
        const MAX_TXS: usize = 1;
        const MAX_CALLDATA: usize = 32;

        let mut tx = mock::CORRECT_MOCK_TXS[0].clone();
        // This address doesn't correspond to the account that signed this tx.
        tx.from = AddrOrWallet::from(address!("0x1230000000000000000000000000000000000456"));

        assert!(run::<Fr>(
            vec![tx.into()],
            mock::MOCK_CHAIN_ID.as_u64(),
            MAX_TXS,
            MAX_CALLDATA
        )
        .is_err(),);
    }
}

mod bench {
    use ark_std::{end_timer, start_timer};
    use halo2_proofs::{
        halo2curves::bn256::{Bn256, Fr, G1Affine},
        plonk::{create_proof, keygen_pk, keygen_vk, verify_proof},
        poly::{
            commitment::ParamsProver,
            kzg::{
                commitment::{KZGCommitmentScheme, ParamsKZG, ParamsVerifierKZG},
                multiopen::{ProverSHPLONK, VerifierSHPLONK},
                strategy::SingleStrategy,
            },
        },
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    };
    use std::env::var;

    use rand::SeedableRng;

    use rand_chacha::ChaChaRng;

    use super::*;
    use crate::util::log2_ceil;

    #[test]
    fn bench_super_circuit_prover() {
        let setup_prfx = "crate::constants::SETUP";
        let proof_gen_prfx = "crate::constants::PROOFGEN_PREFIX";
        let proof_ver_prfx = "crate::constants::PROOFVER_PREFIX";
        // Unique string used by bench results module for parsing the result
        const BENCHMARK_ID: &str = "Rlp decode Circuit";

        let degree: u32 = var("DEGREE")
            .unwrap_or_else(|_| "18".to_string())
            .parse()
            .expect("Cannot parse DEGREE env var as u32");

        let mut rng = ChaChaRng::seed_from_u64(2);

        let (circuit, instance) = {
            let mut circuit = RlpDecoderCircuit::<Fr>::new(10, 16384, vec![]);
            let instance = vec![vec![]];
            (circuit, instance)
        };
        let instance_refs: Vec<&[Fr]> = instance.iter().map(|v| &v[..]).collect();

        // Bench setup generation
        let setup_message = format!("{} {} with degree = {}", BENCHMARK_ID, setup_prfx, degree);
        let start1 = start_timer!(|| setup_message);
        let general_params = ParamsKZG::<Bn256>::setup(degree, &mut rng);
        let verifier_params: ParamsVerifierKZG<Bn256> = general_params.verifier_params().clone();
        end_timer!(start1);

        // Initialize the proving key
        let vk = keygen_vk(&general_params, &circuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(&general_params, vk, &circuit).expect("keygen_pk should not fail");
        // Create a proof
        let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);

        // Bench proof generation time
        let proof_message = format!(
            "{} {} with degree = {}",
            BENCHMARK_ID, proof_gen_prfx, degree
        );
        let start2 = start_timer!(|| proof_message);
        create_proof::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            ChaChaRng,
            Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
            RlpDecoderCircuit<Fr>,
        >(
            &general_params,
            &pk,
            &[circuit],
            &[&[]],
            rng,
            &mut transcript,
        )
        .expect("proof generation should not fail");
        let proof = transcript.finalize();
        end_timer!(start2);

        // Bench verification time
        let start3 = start_timer!(|| format!("{} {}", BENCHMARK_ID, proof_ver_prfx));
        let mut verifier_transcript = Blake2bRead::<_, G1Affine, Challenge255<_>>::init(&proof[..]);
        let strategy = SingleStrategy::new(&general_params);

        verify_proof::<
            KZGCommitmentScheme<Bn256>,
            VerifierSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
            SingleStrategy<'_, Bn256>,
        >(
            &verifier_params,
            pk.get_vk(),
            strategy,
            &[&[]],
            &mut verifier_transcript,
        )
        .expect("failed to verify bench circuit");
        end_timer!(start3);
    }
}
