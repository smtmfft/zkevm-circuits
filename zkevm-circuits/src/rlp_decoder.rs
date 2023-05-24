//! The rlp decoding transaction list circuit implementation.

use std::marker::PhantomData;

use crate::{
    evm_circuit::util::{constraint_builder::BaseConstraintBuilder, rlc},
    impl_expr,
    rlp_decoder_tables::{RMultPowTable, RlpDecoderTable, TxFieldSwitchTable},
    table::KeccakTable,
    util::{log2_ceil, Challenges, SubCircuit, SubCircuitConfig},
    witness,
};
use eth_types::{Field, Signature, Transaction, Word};
use ethers_core::{
    types::TransactionRequest,
    utils::rlp::{self, PayloadInfo},
};
use gadgets::util::{and, not, sum};
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, SecondPhase, Selector,
    },
    poly::Rotation,
};

use crate::util::Expr;
pub use halo2_proofs::halo2curves::{
    group::{
        ff::{Field as GroupField, PrimeField},
        prime::PrimeCurveAffine,
        Curve, Group, GroupEncoding,
    },
    secp256k1::{self, Secp256k1Affine, Secp256k1Compressed},
};
use mock::MockTransaction;

const NUM_BLINDING_ROWS: usize = 64;

/// RlpDecodeTypeTag is used to index the flag of rlp decoding type
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum RlpDecodeTypeTag {
    #[default]
    /// Nothing for no rlp decoding
    DoNothing,
    /// SingleByte: 0x00 - 0x7f
    SingleByte,
    /// NullValue: 0x80
    NullValue,
    /// ShortString: 0x81~0xb7
    ShortString,
    /// LongString: 0xb8
    LongString1,
    /// LongString: 0xb9
    LongString2,
    /// LongString: 0xba
    LongString3,
    /// EmptyList: 0xc0
    EmptyList,
    /// ShortList: 0xc1 ~ 0xf7
    ShortList,
    /// LongList1: 0xf8
    LongList1,
    /// LongList2: 0xf9, 0xFFFF upto (64K)
    LongList2,
    /// LongList3: 0xfa, 0xFFFFFF upto (16M)
    LongList3,
    /// PartialRlp: for those rlp that is not complete
    PartialRlp,
    /// RlpDecodeTypeNum,
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

// TODO: combine with TxFieldTag in table.rs
// Marker that defines whether an Operation performs a `READ` or a `WRITE`.
/// RlpTxFieldTag is used to tell the field of tx, used as state in the circuit
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum RlpTxFieldTag {
    #[default]
    /// for tx list rlp header
    TxListRlpHeader,
    /// for rlp header
    TxRlpHeader,
    /// for tx nonce
    Nonce,
    /// gas price
    GasPrice,
    /// Gas
    Gas,
    /// To
    To,
    /// Value
    Value,
    /// Data
    Data,
    /// SignV
    SignV,
    /// SignR
    SignR,
    /// SignS
    SignS,
    /// Padding
    Padding,
    // 1559 extra field
    /// ChainID
    ChainID,
    /// GasTipCap
    GasTipCap,
    /// GasFeeCap
    GasFeeCap,
    /// AccessList
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

const LEGACY_TX_FIELD_NUM: usize = RlpTxFieldTag::Padding as usize + 1;
const TX1559_TX_FIELD_NUM: usize = RlpTxFieldTag::AccessList as usize + 1;

// TODO: combine with TxFieldTag in table.rs
// Marker that defines whether an Operation performs a `READ` or a `WRITE`.
/// RlpTxTypeTag is used to tell the type of tx
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum RlpTxTypeTag {
    #[default]
    /// legacy tx
    TxLegacyType,
    /// 1559 tx
    Tx1559Type,
}
impl_expr!(RlpTxTypeTag);

/// max byte column num which is used to store the rlp raw bytes
pub const MAX_BYTE_COLUMN_NUM: usize = 33;

/// Witness for RlpDecoderCircuit
#[derive(Clone, Debug, Default)]
pub struct RlpDecoderCircuitConfigWitness<F: Field> {
    /// tx_id column
    pub tx_id: u64,
    /// tx_type column
    pub tx_type: RlpTxTypeTag,
    /// tag column
    pub tx_member: RlpTxFieldTag,
    /// complete column
    pub complete: bool,
    /// rlp types: [single, short, long, very_long, fixed(33)]
    pub rlp_type: RlpDecodeTypeTag,
    /// rlp_tag_length, the length of this rlp field
    pub rlp_tx_member_length: u64,
    /// remained rows, for n < 33 fields, it is n, for m > 33 fields, it is 33 and next row is
    /// partial, next_length = m - 33
    pub rlp_bytes_in_row: u8,
    /// r_mult column, (length, r_mult) => @fixed
    pub r_mult: F,
    /// remain_length
    pub rlp_remain_length: usize,
    /// value
    pub value: F,
    /// acc_rlc_value
    pub acc_rlc_value: F,
    /// bytes
    pub bytes: Vec<u8>, //[u8; MAX_BYTE_COLUMN],
    /// decodable, 0 for decode failed, 1 for success
    pub decodable: bool,
    /// valid, 0 for invalid, 1 for valid, should be == decodable at the end of the circuit
    pub valid: bool,
    /// full chip enable
    pub q_enable: bool,
    /// the begining
    pub q_first: bool,
    /// the end
    pub q_last: bool,
}

/// Config for RlpDecoderCircuit
#[derive(Clone, Debug)]
pub struct RlpDecoderCircuitConfig<F: Field> {
    /// tx_id column
    pub tx_id: Column<Advice>,
    /// tx_type column
    pub tx_type: Column<Advice>,
    /// tag column
    pub tx_member: Column<Advice>,
    /// complete column
    pub complete: Column<Advice>,
    /// rlp types: [single, short, long, very_long, fixed(33)]
    pub rlp_type: Column<Advice>,
    /// rlp_type checking gadget
    pub q_rlp_types: [Column<Advice>; RlpDecodeTypeTag::RlpDecodeTypeNum as usize],
    /// rlp_tag_length, the length of this rlp field
    pub rlp_tx_member_length: Column<Advice>,
    /// remained rows, for n < 33 fields, it is n, for m > 33 fields, it is 33 and next row is
    /// partial, next_length = m - 33
    pub rlp_bytes_in_row: Column<Advice>,
    /// r_mult column, (length, r_mult) => @fixed
    pub r_mult: Column<Advice>,
    /// remain_length, to be 0 at the end.
    pub rlp_remain_length: Column<Advice>,
    /// value
    pub value: Column<Advice>,
    /// acc_rlc_value
    pub acc_rlc_value: Column<Advice>,
    /// bytes
    pub bytes: [Column<Advice>; MAX_BYTE_COLUMN_NUM],
    /// decodable, 0 for decode failed, 1 for success
    pub decodable: Column<Advice>,
    /// valid, 0 for invalid, 1 for valid, should be == decodable at the end of the circuit
    pub valid: Column<Advice>,
    /// dynamic selector for fields
    pub q_tx_members: [Column<Advice>; LEGACY_TX_FIELD_NUM as usize],
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
    /// RlpDecoderTable
    pub rlp_decoder_table: RlpDecoderTable,
    /// state transition table
    pub tx_field_switch_table: TxFieldSwitchTable,
    /// r_mult pow table
    pub r_mult_pow_table: RMultPowTable,
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
        let tx_member = meta.advice_column();
        let complete = meta.advice_column();
        let rlp_type = meta.advice_column();
        let rlp_tx_member_length = meta.advice_column();
        let tx_member_bytes_in_row = meta.advice_column();
        let rlp_remain_length = meta.advice_column();
        let r_mult = meta.advice_column();
        let value = meta.advice_column();
        let acc_rlc_value = meta.advice_column_in(SecondPhase);
        let bytes: [Column<Advice>; MAX_BYTE_COLUMN_NUM] = (0..MAX_BYTE_COLUMN_NUM as usize)
            .map(|_| meta.advice_column())
            .collect::<Vec<Column<Advice>>>()
            .try_into()
            .unwrap();
        let decodable = meta.advice_column();
        let valid = meta.advice_column();
        let q_tx_members: [Column<Advice>; LEGACY_TX_FIELD_NUM as usize] = (0..LEGACY_TX_FIELD_NUM)
            .map(|_| meta.advice_column())
            .collect::<Vec<Column<Advice>>>()
            .try_into()
            .unwrap();
        let q_enable = meta.complex_selector();
        let q_first = meta.fixed_column();
        let q_last = meta.fixed_column();

        // type checking
        let q_rlp_types: [Column<Advice>; RlpDecodeTypeTag::RlpDecodeTypeNum as usize] = (0
            ..RlpDecodeTypeTag::RlpDecodeTypeNum as usize)
            .map(|_| meta.advice_column())
            .collect::<Vec<Column<Advice>>>()
            .try_into()
            .unwrap();

        macro_rules! rlp_type_enabled {
            ($meta:expr, $rlp_type:expr) => {
                $meta.query_advice(q_rlp_types[$rlp_type], Rotation::cur())
            };
        }

        // TODO: lookup bytes range table

        // lookup rlp_types table
        // TODO: bytes[1] as prefix of len also need to be constrainted
        meta.lookup_any("rlp decodable check", |meta| {
            let tx_type = meta.query_advice(tx_type, Rotation::cur());
            let tx_member_cur = meta.query_advice(tx_member, Rotation::cur());
            let byte0 = meta.query_advice(bytes[0], Rotation::cur());
            let decodable = meta.query_advice(decodable, Rotation::cur());
            let q_enable = meta.query_selector(q_enable);

            let is_not_partial = not::expr(rlp_type_enabled!(meta, RlpDecodeTypeTag::PartialRlp));

            let tx_type_in_table =
                meta.query_fixed(args.rlp_decoder_table.tx_type, Rotation::cur());
            let tx_member_in_table =
                meta.query_fixed(args.rlp_decoder_table.tx_field_tag, Rotation::cur());
            let byte0_in_table = meta.query_fixed(args.rlp_decoder_table.byte_0, Rotation::cur());
            let decodable_in_table =
                meta.query_fixed(args.rlp_decoder_table.decodable, Rotation::cur());
            vec![
                (
                    q_enable.expr() * is_not_partial.expr() * tx_type,
                    tx_type_in_table,
                ),
                (
                    q_enable.expr() * is_not_partial.expr() * tx_member_cur,
                    tx_member_in_table,
                ),
                (
                    q_enable.expr() * is_not_partial.expr() * byte0,
                    byte0_in_table,
                ),
                (
                    q_enable.expr() * is_not_partial.expr() * decodable,
                    decodable_in_table,
                ),
            ]
        });

        // // lookup tx_field_switch table
        meta.lookup_any("rlp tx field transition", |meta| {
            let current_member = meta.query_advice(tx_member, Rotation::cur());
            let next_member = meta.query_advice(tx_member, Rotation::next());
            let curr_member_in_table =
                meta.query_fixed(args.tx_field_switch_table.current_tx_field, Rotation::cur());
            let next_member_in_table =
                meta.query_fixed(args.tx_field_switch_table.next_tx_field, Rotation::cur());
            let q_enable = meta.query_selector(q_enable);
            let is_last = meta.query_fixed(q_last, Rotation::cur());

            vec![
                (
                    and::expr([not::expr(is_last.expr()), q_enable.expr()]) * current_member,
                    curr_member_in_table,
                ),
                (
                    and::expr([not::expr(is_last.expr()), q_enable.expr()]) * next_member,
                    next_member_in_table,
                ),
            ]
        });

        // lookup r_mult table with length,
        // TODO: r_mult is adv, add constraint for pow
        meta.lookup_any("rlp r_mult check", |meta| {
            let r_mult = meta.query_advice(r_mult, Rotation::cur());
            let pow = meta.query_advice(tx_member_bytes_in_row, Rotation::cur());
            let r_mult_in_table = meta.query_fixed(args.r_mult_pow_table.r_mult, Rotation::cur());
            let r_pow_in_table = meta.query_fixed(args.r_mult_pow_table.length, Rotation::cur());

            vec![(r_mult, r_mult_in_table), (pow, r_pow_in_table)]
        });

        meta.create_gate("common constraints for all rows", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            // boolean constraints
            cb.require_boolean(
                "field complete boolean",
                meta.query_advice(complete, Rotation::cur()),
            );
            cb.require_boolean(
                "decodable is boolean",
                meta.query_advice(decodable, Rotation::cur()),
            );
            cb.require_boolean(
                "valid is boolean",
                meta.query_advice(valid, Rotation::cur()),
            );

            // bind the rlp_type and rlp_type selector
            q_rlp_types.iter().enumerate().for_each(|(i, q_rlp_type)| {
                let q_rlp_type_enabled = meta.query_advice(*q_rlp_type, Rotation::cur());
                cb.require_boolean("q_rlp_types are bool", q_rlp_type_enabled.expr());
                cb.condition(q_rlp_type_enabled.expr(), |cb| {
                    let rlp_type = meta.query_advice(rlp_type, Rotation::cur());
                    cb.require_equal("rlp type check", rlp_type, i.expr())
                });
            });
            cb.require_equal(
                "1 rlp type only",
                sum::expr(
                    q_rlp_types
                        .iter()
                        .map(|t| meta.query_advice(*t, Rotation::cur())),
                ),
                1.expr(),
            );

            // bind the q_field with the field tag
            q_tx_members.iter().enumerate().for_each(|(i, q_member)| {
                let q_member_enabled = meta.query_advice(*q_member, Rotation::cur());
                cb.require_boolean("q_member are bool", q_member_enabled.expr());
                cb.condition(q_member_enabled.expr(), |cb| {
                    let tag = meta.query_advice(tx_member, Rotation::cur());
                    cb.require_equal("tag check", tag, i.expr())
                });
            });
            cb.require_equal(
                "1 tx field only",
                sum::expr(
                    q_tx_members
                        .iter()
                        .map(|field| meta.query_advice(*field, Rotation::cur())),
                ),
                1.expr(),
            );

            let valid_cur = meta.query_advice(valid, Rotation::cur());
            let valid_next = meta.query_advice(valid, Rotation::next());
            cb.require_equal(
                "valid should be consistent",
                valid_cur.expr(),
                valid_next.expr(),
            );

            let decodable = meta.query_advice(decodable, Rotation::cur());
            cb.require_zero(
                "if decode == 0 then valid must 0",
                not::expr(decodable.expr()) * valid_cur.expr(),
            );

            cb.gate(and::expr([
                meta.query_selector(q_enable),
                not::expr(meta.query_fixed(q_last, Rotation::cur())),
            ]))
        });

        // common logic for tx members
        meta.create_gate("tx members common constraints", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let tag = meta.query_advice(tx_member, Rotation::cur());
            let complete_cur = meta.query_advice(complete, Rotation::cur());
            let rlp_tag_length_cur = meta.query_advice(rlp_tx_member_length, Rotation::cur());
            let r_mult = meta.query_advice(r_mult, Rotation::cur());
            let bytes_in_row_cur = meta.query_advice(tx_member_bytes_in_row, Rotation::cur());
            let remain_length = meta.query_advice(rlp_remain_length, Rotation::cur());
            let acc_rlc_cur = meta.query_advice(acc_rlc_value, Rotation::cur());
            let byte_cells_cur = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let q_tx_rlp_header =
                meta.query_advice(q_tx_members[RlpTxFieldTag::TxRlpHeader], Rotation::cur());
            let q_enable = meta.query_selector(q_enable);
            let q_first = meta.query_fixed(q_first, Rotation::cur());

            // length with leading bytes
            cb.condition(rlp_type_enabled!(meta, RlpDecodeTypeTag::DoNothing), |cb| {
                cb.require_equal("0 length", rlp_tag_length_cur.clone(), 0.expr())
            });
            cb.condition(
                rlp_type_enabled!(meta, RlpDecodeTypeTag::SingleByte),
                |cb| cb.require_equal("single length", rlp_tag_length_cur.clone(), 1.expr()),
            );
            cb.condition(rlp_type_enabled!(meta, RlpDecodeTypeTag::NullValue), |cb| {
                cb.require_equal("empty length", rlp_tag_length_cur.clone(), 1.expr())
            });
            cb.condition(
                rlp_type_enabled!(meta, RlpDecodeTypeTag::ShortString),
                |cb| {
                    cb.require_equal(
                        "ShortString length",
                        rlp_tag_length_cur.clone(),
                        byte_cells_cur[0].expr() - 0x80.expr() + 1.expr(),
                    )
                },
            );
            cb.condition(
                rlp_type_enabled!(meta, RlpDecodeTypeTag::LongString1),
                |cb| {
                    cb.require_equal(
                        "Long String 0xb8 length",
                        rlp_tag_length_cur.clone(),
                        byte_cells_cur[1].expr() + 2.expr(),
                    )
                },
            );
            cb.condition(
                rlp_type_enabled!(meta, RlpDecodeTypeTag::LongString2),
                |cb| {
                    cb.require_equal(
                        "Long String 0xb9 length",
                        rlp_tag_length_cur.clone(),
                        byte_cells_cur[1].expr() * 256.expr() + byte_cells_cur[2].expr() + 3.expr(),
                    )
                },
            );
            cb.condition(
                rlp_type_enabled!(meta, RlpDecodeTypeTag::LongString3),
                |cb| {
                    cb.require_equal(
                        "Long String 0xba length",
                        rlp_tag_length_cur.clone(),
                        byte_cells_cur[1].expr() * 65536.expr()
                            + byte_cells_cur[2].expr() * 256.expr()
                            + byte_cells_cur[3].expr()
                            + 4.expr(),
                    )
                },
            );
            cb.condition(rlp_type_enabled!(meta, RlpDecodeTypeTag::EmptyList), |cb| {
                cb.require_equal("empty list length", rlp_tag_length_cur.clone(), 1.expr())
            });
            cb.condition(rlp_type_enabled!(meta, RlpDecodeTypeTag::ShortList), |cb| {
                cb.require_equal(
                    "short length",
                    rlp_tag_length_cur.clone(),
                    byte_cells_cur[0].expr() - 0xc0.expr() + 1.expr(),
                )
            });
            cb.condition(
                rlp_type_enabled!(meta, RlpDecodeTypeTag::PartialRlp),
                |cb| {
                    cb.require_equal(
                        "length = prev_length - prev_bytes_in_row",
                        rlp_tag_length_cur.clone(),
                        meta.query_advice(rlp_tx_member_length, Rotation::prev())
                            - meta.query_advice(tx_member_bytes_in_row, Rotation::prev()),
                    );

                    cb.require_zero(
                        "above row is incomplete",
                        meta.query_advice(complete, Rotation::prev()),
                    );

                    cb.require_equal("only data has partial rlp", tag, RlpTxFieldTag::Data.expr());
                },
            );

            cb.condition(complete_cur.expr(), |cb| {
                cb.require_equal(
                    "complete = 1 => rlp_tag_length = bytes_in_row",
                    bytes_in_row_cur.expr(),
                    rlp_tag_length_cur.expr(),
                );

                cb.require_equal(
                    "rlp_remain_length = rlp_remain_length.prev - length",
                    remain_length.expr(),
                    meta.query_advice(rlp_remain_length, Rotation::prev())
                        - bytes_in_row_cur.expr(),
                );
            });

            cb.condition(not::expr(complete_cur.expr()), |cb| {
                cb.require_equal(
                    "!complete => MAX_BYTES_COL == bytes_in_row",
                    bytes_in_row_cur.expr(),
                    MAX_BYTE_COLUMN_NUM.expr(),
                );
            });

            cb.require_equal(
                "rlc = r_mult_cur * rlc_next + rlc(bytes_cur)",
                acc_rlc_cur,
                r_mult * meta.query_advice(acc_rlc_value, Rotation::next())
                    + rlc::expr(&byte_cells_cur, args.challenges.keccak_input()),
            );

            cb.gate(and::expr([
                q_enable,
                not::expr(q_first),
                not::expr(q_tx_rlp_header),
            ]))
        });

        // TxListHeader in the first row
        meta.create_gate("txListHeader in first row", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let tx_id = meta.query_advice(tx_id, Rotation::cur());
            let tx_type_cur = meta.query_advice(tx_type, Rotation::cur());
            let tx_member_cur = meta.query_advice(tx_member, Rotation::cur());
            let complete = meta.query_advice(complete, Rotation::cur());
            let rlp_tag_length_cur = meta.query_advice(rlp_tx_member_length, Rotation::cur());
            let r_mult = meta.query_advice(r_mult, Rotation::cur());
            let remain_length = meta.query_advice(rlp_remain_length, Rotation::cur());
            let acc_rlc_cur = meta.query_advice(acc_rlc_value, Rotation::cur());
            let byte_cells_cur = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let decodable = meta.query_advice(decodable, Rotation::cur());
            let q_first = meta.query_fixed(q_first, Rotation::cur());

            cb.require_zero("0 tx_id", tx_id);
            cb.require_zero("0 tx_type", tx_type_cur.expr());
            cb.require_zero("0 tx_tag", tx_member_cur);
            cb.require_equal("field completed", complete.expr(), 1.expr());

            cb.condition(rlp_type_enabled!(meta, RlpDecodeTypeTag::LongList1), |cb| {
                cb.require_equal(
                    "long length: f8 + 1",
                    remain_length.expr(),
                    byte_cells_cur[1].expr(),
                )
                // TODO: byte_cells_cur[1] > 55
            });
            cb.condition(rlp_type_enabled!(meta, RlpDecodeTypeTag::LongList2), |cb| {
                cb.require_equal(
                    "long length: f9 + 2",
                    remain_length.expr(),
                    byte_cells_cur[1].expr() * 256.expr() + byte_cells_cur[2].expr(),
                )
                // TODO: byte_cells_cur[1] != 0
            });
            cb.condition(rlp_type_enabled!(meta, RlpDecodeTypeTag::LongList3), |cb| {
                cb.require_equal(
                    "long length: fa + 3",
                    remain_length.expr(),
                    byte_cells_cur[1].expr() * 65536.expr()
                        + byte_cells_cur[2].expr() * 256.expr()
                        + byte_cells_cur[3].expr(),
                )
                // TODO: byte_cells_cur[1] != 0
            });

            cb.condition(decodable, |cb| {
                cb.require_equal(
                    "rlp_tag_length = rlp_header length",
                    rlp_tag_length_cur.expr(),
                    byte_cells_cur[0].expr() - 247.expr() + 1.expr(),
                );
            });

            cb.require_equal(
                "rlc = r_mult_cur * rlc_next + rlc(bytes_cur)",
                acc_rlc_cur,
                r_mult * meta.query_advice(acc_rlc_value, Rotation::next())
                    + rlc::expr(&byte_cells_cur, args.challenges.keccak_input()),
            );

            cb.gate(q_first)
        });

        meta.create_gate("txHeader of legacy tx", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let tx_id_cur = meta.query_advice(tx_id, Rotation::cur());
            let tx_id_prev = meta.query_advice(tx_id, Rotation::prev());
            let tx_type_cur = meta.query_advice(tx_type, Rotation::cur());
            let tx_member_cur = meta.query_advice(tx_member, Rotation::cur());
            let complete = meta.query_advice(complete, Rotation::cur());
            let rlp_tag_length_cur = meta.query_advice(rlp_tx_member_length, Rotation::cur());
            let r_mult = meta.query_advice(r_mult, Rotation::cur());
            let acc_rlc_cur = meta.query_advice(acc_rlc_value, Rotation::cur());
            let byte_cells_cur = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let decodable = meta.query_advice(decodable, Rotation::cur());
            let q_tx_rlp_header =
                meta.query_advice(q_tx_members[RlpTxFieldTag::TxRlpHeader], Rotation::cur());

            cb.require_equal(
                "tx_id == tx_id_prev + 1",
                tx_id_cur.expr(),
                tx_id_prev.expr() + 1.expr(),
            );
            cb.require_equal(
                "legacy tx_type",
                tx_type_cur.expr(),
                RlpTxTypeTag::TxLegacyType.expr(),
            );
            cb.require_equal(
                "tag is tx header",
                tx_member_cur,
                RlpTxFieldTag::TxRlpHeader.expr(),
            );
            cb.require_equal("field completed", complete.expr(), 1.expr());

            cb.condition(decodable, |cb| {
                cb.require_equal(
                    "rlp_tag_length = rlp_header length",
                    rlp_tag_length_cur.expr(),
                    byte_cells_cur[0].expr() - 247.expr() + 1.expr(),
                );
            });

            cb.require_equal(
                "rlc = r_mult_cur * rlc_next + rlc(bytes_cur)",
                acc_rlc_cur,
                r_mult * meta.query_advice(acc_rlc_value, Rotation::next())
                    + rlc::expr(&byte_cells_cur, args.challenges.keccak_input()),
            );

            cb.gate(q_tx_rlp_header * meta.query_selector(q_enable))
        });

        // padding
        meta.create_gate("Padding", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let tx_member_cur = meta.query_advice(tx_member, Rotation::cur());
            let complete = meta.query_advice(complete, Rotation::cur());
            let length = meta.query_advice(rlp_tx_member_length, Rotation::cur());
            let r_mult = meta.query_advice(r_mult, Rotation::cur());
            let remain_length = meta.query_advice(rlp_remain_length, Rotation::cur());
            let acc_rlc_value = meta.query_advice(acc_rlc_value, Rotation::cur());
            let bytes_values = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let q_last = meta.query_fixed(q_last, Rotation::cur());
            let q_padding =
                meta.query_advice(q_tx_members[RlpTxFieldTag::Padding], Rotation::cur());

            cb.require_equal("tag", tx_member_cur, RlpTxFieldTag::Padding.expr());
            cb.require_equal("field completed", complete.expr(), 1.expr());
            cb.require_zero("padding has no r_mult", r_mult);
            cb.require_zero("padding has no length", length);
            cb.require_zero("padding has no remain length", remain_length);
            cb.require_zero(
                "last row above padding has no remain length",
                meta.query_advice(rlp_remain_length, Rotation::prev()),
            );
            cb.require_equal("padding has no rlc (all 0)", acc_rlc_value, 0.expr());
            bytes_values.iter().for_each(|byte| {
                cb.require_zero("padding has no bytes", byte.expr());
            });

            cb.gate(q_padding.expr() * not::expr(q_last) * meta.query_selector(q_enable))
        });

        meta.create_gate("end logic", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let complete = meta.query_advice(complete, Rotation::cur());
            let tx_member_cur = meta.query_advice(tx_member, Rotation::cur());
            let length = meta.query_advice(rlp_tx_member_length, Rotation::cur());
            let r_mult = meta.query_advice(r_mult, Rotation::cur());
            let remain_length = meta.query_advice(rlp_remain_length, Rotation::cur());
            let acc_rlc_value = meta.query_advice(acc_rlc_value, Rotation::cur());
            let decodable = meta.query_advice(decodable, Rotation::cur());
            let valid = meta.query_advice(valid, Rotation::cur());
            let q_enable = meta.query_selector(q_enable);
            let q_last = meta.query_fixed(q_last, Rotation::cur());

            cb.require_equal("completed at last", complete, 1.expr());
            cb.require_equal(
                "padding at last",
                tx_member_cur,
                RlpTxFieldTag::Padding.expr(),
            );
            cb.require_equal("padding has no r_mult", r_mult, 0.expr());
            cb.require_equal("padding has no length", length, 0.expr());
            cb.require_equal("padding has no remain length", remain_length, 0.expr());
            cb.require_equal("padding has no rlc (all 0)", acc_rlc_value, 0.expr());
            cb.require_equal("valid == decodable", valid, decodable);

            cb.gate(q_last * q_enable)
        });

        Self {
            tx_id,
            tx_type,
            tx_member,
            complete,
            rlp_type,
            q_rlp_types,
            rlp_tx_member_length,
            rlp_bytes_in_row: tx_member_bytes_in_row,
            r_mult,
            rlp_remain_length,
            value,
            acc_rlc_value,
            bytes,
            decodable,
            valid,
            q_tx_members,
            q_enable,
            q_first,
            q_last,
            args,
        }
    }
}

impl<F: Field> RlpDecoderCircuitConfig<F> {
    fn assign_rows(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        wits: &[RlpDecoderCircuitConfigWitness<F>],
    ) -> Result<(), Error> {
        let mut offset = offset;
        self.name_row_members(region);
        for wit in wits {
            self.assign_row(region, offset, wit)?;
            offset += 1;
        }
        Ok(())
    }

    fn name_row_members(&self, region: &mut Region<'_, F>) {
        region.name_column(|| "config.tx_id", self.tx_id);
        region.name_column(|| "config.tx_type", self.tx_type);
        region.name_column(|| "config.tag", self.tx_member);
        region.name_column(|| "config.complete", self.complete);
        region.name_column(|| "config.rlp_types", self.rlp_type);
        region.name_column(|| "config.rlp_tag_length", self.rlp_tx_member_length);
        region.name_column(|| "config.rlp_remain_length", self.rlp_remain_length);
        region.name_column(|| "config.r_mult", self.r_mult);
        region.name_column(|| "config.value", self.value);
        region.name_column(|| "config.acc_rlc_value", self.acc_rlc_value);
        for (i, byte) in self.bytes.iter().enumerate() {
            region.name_column(|| format!("config.bytes-[{}]", i), *byte);
        }
        region.name_column(|| "config.decodable", self.decodable);
        region.name_column(|| "config.valid", self.valid);
    }

    fn assign_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        w: &RlpDecoderCircuitConfigWitness<F>,
    ) -> Result<(), Error> {
        region.assign_advice(
            || "config.tx_id",
            self.tx_id,
            offset,
            || Value::known(F::from(w.tx_id)),
        )?;
        region.assign_advice(
            || "config.tx_type",
            self.tx_type,
            offset,
            || Value::known(F::from(w.tx_type as u64)),
        )?;
        region.assign_advice(
            || "config.tag",
            self.tx_member,
            offset,
            || Value::known(F::from(w.tx_member as u64)),
        )?;
        region.assign_advice(
            || "config.complete",
            self.complete,
            offset,
            || Value::known(F::from(w.complete)),
        )?;
        region.assign_advice(
            || "config.rlp_type",
            self.rlp_type,
            offset,
            || Value::known(F::from(w.rlp_type as u64)),
        )?;
        self.q_rlp_types.iter().enumerate().try_for_each(|(i, q)| {
            region
                .assign_advice(
                    || format!("config.q_rlp_types[{}]", i),
                    *q,
                    offset,
                    || {
                        if i as u64 == w.rlp_type as u64 {
                            Value::known(F::one())
                        } else {
                            Value::known(F::zero())
                        }
                    },
                )
                .map(|_| ())
        })?;
        region.assign_advice(
            || "config.rlp_tag_length",
            self.rlp_tx_member_length,
            offset,
            || Value::known(F::from(w.rlp_tx_member_length)),
        )?;
        region.assign_advice(
            || "config.tag_bytes_in_row",
            self.rlp_bytes_in_row,
            offset,
            || Value::known(F::from(w.rlp_bytes_in_row as u64)),
        )?;
        region.assign_advice(
            || "config.r_mult",
            self.r_mult,
            offset,
            || Value::known(F::from(w.r_mult)),
        )?;
        region.assign_advice(
            || "config.rlp_remain_length",
            self.rlp_remain_length,
            offset,
            || Value::known(F::from(w.rlp_remain_length as u64)),
        )?;
        region.assign_advice(
            || "config.value",
            self.value,
            offset,
            || Value::known(F::from(w.value)),
        )?;
        region.assign_advice(
            || "config.acc_rlc_value",
            self.acc_rlc_value,
            offset,
            || Value::known(F::from(w.acc_rlc_value)),
        )?;
        for (i, byte) in self.bytes.iter().enumerate() {
            region.assign_advice(
                || format!("config.bytes[{}]", i),
                *byte,
                offset,
                || {
                    if i < w.bytes.len() {
                        Value::known(F::from(w.bytes[i] as u64))
                    } else {
                        Value::known(F::zero())
                    }
                },
            )?;
        }
        region.assign_advice(
            || "config.decodable",
            self.decodable,
            offset,
            || Value::known(F::from(w.decodable)),
        )?;
        region.assign_advice(
            || "config.valid",
            self.valid,
            offset,
            || Value::known(F::from(w.valid)),
        )?;
        self.q_tx_members
            .iter()
            .enumerate()
            .try_for_each(|(i, q_field)| {
                region
                    .assign_advice(
                        || format!("config.q_fields[{}]", i),
                        *q_field,
                        offset,
                        || {
                            if i == w.tx_member as usize {
                                Value::known(F::one())
                            } else {
                                Value::known(F::zero())
                            }
                        },
                    )
                    .map(|_| ())
            })?;
        region.assign_fixed(
            || "config.q_first",
            self.q_first,
            offset,
            || Value::known(F::from(w.q_first)),
        )?;
        region.assign_fixed(
            || "config.q_last",
            self.q_last,
            offset,
            || Value::known(F::from(w.q_last)),
        )?;
        if w.q_enable {
            self.q_enable.enable(region, offset)?;
        }

        Ok(())
    }
}

/// rlp decode Circuit for verifying transaction signatures
#[derive(Clone, Default, Debug)]
pub struct RlpDecoderCircuit<F: Field> {
    /// input bytes
    pub bytes: Vec<u8>,
    /// Size of the circuit
    pub size: usize,
    /// phantom
    pub _marker: PhantomData<F>,
}

impl<F: Field> RlpDecoderCircuit<F> {
    /// Return a new RlpDecoderCircuit
    pub fn new(bytes: Vec<u8>, degree: usize) -> Self {
        RlpDecoderCircuit::<F> {
            bytes,
            size: 1 << degree,
            _marker: PhantomData,
        }
    }

    /// Return the minimum number of rows required to prove an input of a
    /// particular size.
    pub fn min_num_rows(block: &witness::Block<F>) -> (usize, usize) {
        let txs_len = block.txs.len();
        let call_data_rows = block.txs.iter().fold(0, |acc, tx| {
            acc + tx.call_data.len() / MAX_BYTE_COLUMN_NUM + 1
        });

        let min_num_rows = Self::calc_min_num_rows(txs_len, call_data_rows);
        (min_num_rows, min_num_rows)
    }

    /// Return the minimum number of rows required to prove an input of a
    /// particular size.
    pub fn min_num_rows_from_tx(txs: &Vec<Transaction>) -> (usize, usize) {
        let txs_len = txs.len();
        let call_data_rows = txs
            .iter()
            .fold(0, |acc, tx| acc + tx.input.len() / MAX_BYTE_COLUMN_NUM + 1);

        let min_num_rows = Self::calc_min_num_rows(txs_len, call_data_rows);
        (min_num_rows, min_num_rows)
    }

    fn calc_min_num_rows(txs_len: usize, call_data_rows: usize) -> usize {
        // add 2 for prev and next rotations.
        let constraint_size = txs_len * LEGACY_TX_FIELD_NUM + call_data_rows + 2;
        let tables_size =
            RlpDecoderTable::table_size() + TxFieldSwitchTable::table_size() + MAX_BYTE_COLUMN_NUM;
        constraint_size + tables_size + NUM_BLINDING_ROWS
    }
}

impl<F: Field> SubCircuit<F> for RlpDecoderCircuit<F> {
    type Config = RlpDecoderCircuitConfig<F>;

    fn new_from_block(block: &witness::Block<F>) -> Self {
        let txs: Vec<SignedTransaction> = block
            .eth_block
            .transactions
            .iter()
            .map(|tx| tx.into())
            .collect::<Vec<_>>();
        let bytes = rlp::encode_list(&txs).to_vec();
        let degree = log2_ceil(Self::min_num_rows(block).0);
        RlpDecoderCircuit::<F> {
            bytes,
            size: 1 << degree,
            _marker: PhantomData,
        }
    }

    /// Return the minimum number of rows required to prove the block
    fn min_num_rows_block(block: &witness::Block<F>) -> (usize, usize) {
        RlpDecoderCircuit::<F>::min_num_rows(block)
    }

    /// Make the assignments to the RlpDecodeCircuit
    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        let mut randomness = F::zero();
        challenges.keccak_input().map(|r| randomness = r);
        let witness: Vec<RlpDecoderCircuitConfigWitness<F>> =
            rlp_decode_tx_list_manually(&self.bytes, randomness, self.size as u32);

        config.args.rlp_decoder_table.load(layouter, challenges)?;
        config
            .args
            .tx_field_switch_table
            .load(layouter, challenges)?;
        config.args.r_mult_pow_table.load(layouter, challenges)?;
        config
            .args
            .keccak_table
            .dev_load(layouter, vec![&self.bytes], challenges)?;

        layouter.assign_region(
            || "rlp witness region",
            |mut region| {
                let offset = 0;
                config.assign_rows(&mut region, offset, &witness)?;
                Ok(())
            },
        )
    }

    fn instance(&self) -> Vec<Vec<F>> {
        // empty instance now
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
        let rlp_decoder_table = RlpDecoderTable::construct(meta);
        let tx_field_switch_table = TxFieldSwitchTable::construct(meta);
        let r_mult_pow_table = RMultPowTable::construct(meta);
        let keccak_table = KeccakTable::construct(meta);
        let challenges = Challenges::construct(meta);

        let config = {
            // let challenges_expr = challenges.exprs(meta);
            let r = 11u64;
            let challenges_expr = Challenges::mock(r.expr(), r.expr(), r.expr());
            RlpDecoderCircuitConfig::new(
                meta,
                RlpDecoderCircuitConfigArgs {
                    rlp_decoder_table,
                    tx_field_switch_table,
                    r_mult_pow_table,
                    keccak_table,
                    challenges: challenges_expr,
                },
            )
        };

        (config, challenges)
    }

    fn synthesize(
        &self,
        (config, _challenges): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        // let challenges = challenges.values(&mut layouter);
        let r = F::from(11u64);
        let challenges = Challenges::mock(Value::known(r), Value::known(r), Value::known(r));

        self.synthesize_sub(&config, &challenges, &mut layouter)
    }
}

fn generate_rlp_type_witness(header_byte: u8) -> (RlpDecodeTypeTag, bool) {
    let mut decodable = true;
    let rlp_type = match header_byte {
        0x00..=0x7f => RlpDecodeTypeTag::SingleByte,
        0x80 => RlpDecodeTypeTag::NullValue,
        0x81..=0xb7 => RlpDecodeTypeTag::ShortString,
        0xb8 => RlpDecodeTypeTag::LongString1,
        0xb9 => RlpDecodeTypeTag::LongString2,
        0xba => RlpDecodeTypeTag::LongString3,
        0xc0 => RlpDecodeTypeTag::EmptyList,
        0xc1..=0xf7 => RlpDecodeTypeTag::ShortList,
        0xf8 => RlpDecodeTypeTag::LongList1,
        0xf9 => RlpDecodeTypeTag::LongList2,
        0xfa => RlpDecodeTypeTag::LongList3,
        _ => {
            decodable = false;
            RlpDecodeTypeTag::DoNothing
        }
    };
    (rlp_type, decodable)
}

fn generate_fields_witness_len(tag: &RlpTxFieldTag, payload: &PayloadInfo) -> usize {
    match tag {
        RlpTxFieldTag::TxListRlpHeader => payload.header_len,
        RlpTxFieldTag::TxRlpHeader => payload.header_len,
        _ => payload.total(),
    }
}

fn generate_rlp_row_witness<F: Field>(
    tx_id: u64,
    tx_member: &RlpTxFieldTag,
    raw_bytes: &[u8],
    r: F,
    rlp_remain_length: usize,
) -> Vec<RlpDecoderCircuitConfigWitness<F>> {
    let mut witness = vec![];
    let (mut rlp_type, decodable) = generate_rlp_type_witness(raw_bytes[0]);
    let partial_rlp_type = RlpDecodeTypeTag::PartialRlp;
    let rlp_tag_len = raw_bytes.len();
    let mut prev_rlp_remain_length = rlp_remain_length;

    macro_rules! generate_witness {
        () => {{
            let mut temp_witness_vec = Vec::new();
            let mut tag_remain_length = rlp_tag_len;
            let mut raw_bytes_offset = 0;
            while tag_remain_length > MAX_BYTE_COLUMN_NUM {
                temp_witness_vec.push(RlpDecoderCircuitConfigWitness::<F> {
                    tx_id: tx_id,
                    tx_type: RlpTxTypeTag::TxLegacyType,
                    tx_member: tx_member.clone(),
                    complete: false,
                    rlp_type: rlp_type,
                    rlp_tx_member_length: tag_remain_length as u64,
                    rlp_bytes_in_row: MAX_BYTE_COLUMN_NUM as u8,
                    r_mult: r.pow(&[MAX_BYTE_COLUMN_NUM as u64, 0, 0, 0]),
                    rlp_remain_length: prev_rlp_remain_length - MAX_BYTE_COLUMN_NUM,
                    value: F::zero(),
                    acc_rlc_value: F::zero(),
                    bytes: raw_bytes[raw_bytes_offset..raw_bytes_offset + MAX_BYTE_COLUMN_NUM]
                        .to_vec(),
                    decodable: decodable,
                    valid: true,
                    q_enable: true,
                    q_first: false,
                    q_last: false,
                });
                raw_bytes_offset += MAX_BYTE_COLUMN_NUM;
                tag_remain_length -= MAX_BYTE_COLUMN_NUM;
                prev_rlp_remain_length -= MAX_BYTE_COLUMN_NUM;
                rlp_type = partial_rlp_type;
            }
            temp_witness_vec.push(RlpDecoderCircuitConfigWitness::<F> {
                tx_id: tx_id,
                tx_type: RlpTxTypeTag::TxLegacyType,
                tx_member: tx_member.clone(),
                complete: true,
                rlp_type: rlp_type,
                rlp_tx_member_length: tag_remain_length as u64,
                rlp_bytes_in_row: tag_remain_length as u8,
                r_mult: r.pow(&[tag_remain_length as u64, 0, 0, 0]),
                rlp_remain_length: prev_rlp_remain_length - tag_remain_length,
                value: F::zero(),
                acc_rlc_value: F::zero(),
                bytes: raw_bytes[raw_bytes_offset..].to_vec(),
                decodable: decodable,
                valid: true,
                q_enable: true,
                q_first: false,
                q_last: false,
            });
            temp_witness_vec
        }};
    }

    // TODO: reorganize the match
    match tx_member {
        RlpTxFieldTag::TxListRlpHeader => witness.append(&mut generate_witness!()),
        RlpTxFieldTag::TxRlpHeader => witness.append(&mut generate_witness!()),
        RlpTxFieldTag::Nonce => witness.append(&mut generate_witness!()),
        RlpTxFieldTag::GasPrice => witness.append(&mut generate_witness!()),
        RlpTxFieldTag::Gas => witness.append(&mut generate_witness!()),
        RlpTxFieldTag::To => witness.append(&mut generate_witness!()),
        RlpTxFieldTag::Value => witness.append(&mut generate_witness!()),
        RlpTxFieldTag::Data => witness.append(&mut generate_witness!()),
        RlpTxFieldTag::SignV => witness.append(&mut generate_witness!()),
        RlpTxFieldTag::SignR => witness.append(&mut generate_witness!()),
        RlpTxFieldTag::SignS => witness.append(&mut generate_witness!()),
        RlpTxFieldTag::Padding => {
            unreachable!("Padding should not be here")
        }
        _ => {
            unreachable!("1559 not support now")
        }
    }
    witness
}

fn generate_rlp_txfield_witness<F: Field>(
    tx_id: u64,
    tag: &RlpTxFieldTag,
    bytes: &[u8],
    r: F,
    witness: &mut Vec<RlpDecoderCircuitConfigWitness<F>>,
) -> Option<PayloadInfo> {
    let offset = 0;
    let decode_result = PayloadInfo::from(&bytes[offset..]);

    match decode_result {
        Ok(payload_info) => {
            let bytes_num = generate_fields_witness_len(tag, &payload_info);
            let rlp_remain_length = witness
                .last()
                .map_or(payload_info.total(), |w| w.rlp_remain_length);

            witness.append(&mut generate_rlp_row_witness(
                tx_id,
                tag,
                &bytes[offset..offset + bytes_num],
                r,
                rlp_remain_length,
            ));
            Some(payload_info)
        }
        // TODO: error case
        Err(decoder_err) => match decoder_err {
            rlp::DecoderError::RlpIsTooShort => todo!(),
            rlp::DecoderError::RlpDataLenWithZeroPrefix => todo!(),
            rlp::DecoderError::RlpInvalidIndirection => todo!(),
            _ => unimplemented!("Unsupport payload decode error: {:?}", decoder_err),
        },
    }
}

// trait RlpTxFieldWittnessGenerator<F: Field> {
//     fn generate_rlp_txfield_witness(
//         &self,
//         tx_id: u64,
//         bytes: &[u8],
//         r: F,
//         witness: &mut Vec<RlpDecoderCircuitConfigWitness<F>>,
//     ) -> Option<PayloadInfo>;
// }

// impl<F: Field> RlpTxFieldWittnessGenerator<F> for RlpTxFieldTag {
//     fn generate_rlp_txfield_witness(
//         &self,
//         tx_id: u64,
//         bytes: &[u8],
//         r: F,
//         witness: &mut Vec<RlpDecoderCircuitConfigWitness<F>>,
//     ) -> Option<PayloadInfo> {
//         let offset = 0;
//         let decode_result = PayloadInfo::from(&bytes[offset..]);
//         match self {
//             RlpTxFieldTag::TxListRlpHeader => todo!(),
//             RlpTxFieldTag::TxRlpHeader => todo!(),
//             RlpTxFieldTag::Nonce => todo!(),
//             RlpTxFieldTag::GasPrice => todo!(),
//             RlpTxFieldTag::Gas => todo!(),
//             RlpTxFieldTag::To => todo!(),
//             RlpTxFieldTag::Value => todo!(),
//             RlpTxFieldTag::Data => todo!(),
//             RlpTxFieldTag::SignV => todo!(),
//             RlpTxFieldTag::SignR => todo!(),
//             RlpTxFieldTag::SignS => todo!(),
//             RlpTxFieldTag::Padding => todo!(),
//             RlpTxFieldTag::ChainID => todo!(),
//             RlpTxFieldTag::GasTipCap => todo!(),
//             RlpTxFieldTag::GasFeeCap => todo!(),
//             RlpTxFieldTag::AccessList => todo!(),
//         }
//     }
// }

// TODO: use a state machine to decode the tx list as above
fn rlp_decode_tx_list_manually<F: Field>(
    bytes: &[u8],
    r: F,
    k: u32,
) -> Vec<RlpDecoderCircuitConfigWitness<F>> {
    let mut witness = vec![];
    let mut tx_id: u64 = 0;

    let mut offset = 0;
    let tx_list_header = generate_rlp_txfield_witness(
        tx_id,
        &RlpTxFieldTag::TxListRlpHeader,
        &bytes[offset..],
        r,
        &mut witness,
    );
    if tx_list_header.is_none() {
        return witness;
    }
    let tx_list_rlp_header = tx_list_header.unwrap();
    offset += tx_list_rlp_header.header_len;

    let total_list_len = tx_list_rlp_header.total();
    tx_id = 1; // tx_id started from 1 as we have a Anchor tx
    while offset < total_list_len {
        let tx_rlp_header = generate_rlp_txfield_witness(
            tx_id,
            &RlpTxFieldTag::TxRlpHeader,
            &bytes[offset..],
            r,
            &mut witness,
        );
        if tx_rlp_header.is_none() {
            return witness;
        }
        offset += tx_rlp_header.unwrap().header_len;

        let tx_rlp_nonce = generate_rlp_txfield_witness(
            tx_id,
            &RlpTxFieldTag::Nonce,
            &bytes[offset..],
            r,
            &mut witness,
        );
        if tx_rlp_nonce.is_none() {
            return witness;
        }
        offset += tx_rlp_nonce.unwrap().total();

        let tx_rlp_gas_price = generate_rlp_txfield_witness(
            tx_id,
            &RlpTxFieldTag::GasPrice,
            &bytes[offset..],
            r,
            &mut witness,
        );
        if tx_rlp_gas_price.is_none() {
            return witness;
        }
        offset += tx_rlp_gas_price.unwrap().total();

        let tx_rlp_gas = generate_rlp_txfield_witness(
            tx_id,
            &RlpTxFieldTag::Gas,
            &bytes[offset..],
            r,
            &mut witness,
        );
        if tx_rlp_gas.is_none() {
            return witness;
        }
        offset += tx_rlp_gas.unwrap().total();

        let tx_rlp_to_addr = generate_rlp_txfield_witness(
            tx_id,
            &RlpTxFieldTag::To,
            &bytes[offset..],
            r,
            &mut witness,
        );
        if tx_rlp_to_addr.is_none() {
            return witness;
        }
        offset += tx_rlp_to_addr.unwrap().total();

        let tx_rlp_value = generate_rlp_txfield_witness(
            tx_id,
            &RlpTxFieldTag::Value,
            &bytes[offset..],
            r,
            &mut witness,
        );
        if tx_rlp_value.is_none() {
            return witness;
        }
        offset += tx_rlp_value.unwrap().total();

        let tx_rlp_data = generate_rlp_txfield_witness(
            tx_id,
            &RlpTxFieldTag::Data,
            &bytes[offset..],
            r,
            &mut witness,
        );
        if tx_rlp_data.is_none() {
            return witness;
        }
        offset += tx_rlp_data.unwrap().total();

        let tx_rlp_v = generate_rlp_txfield_witness(
            tx_id,
            &RlpTxFieldTag::SignV,
            &bytes[offset..],
            r,
            &mut witness,
        );
        if tx_rlp_v.is_none() {
            return witness;
        }
        offset += tx_rlp_v.unwrap().total();

        let tx_rlp_r = generate_rlp_txfield_witness(
            tx_id,
            &RlpTxFieldTag::SignR,
            &bytes[offset..],
            r,
            &mut witness,
        );
        if tx_rlp_r.is_none() {
            return witness;
        }
        offset += tx_rlp_r.unwrap().total();

        let tx_rlp_s = generate_rlp_txfield_witness(
            tx_id,
            &RlpTxFieldTag::SignS,
            &bytes[offset..],
            r,
            &mut witness,
        );
        if tx_rlp_s.is_none() {
            return witness;
        }
        offset += tx_rlp_s.unwrap().total();
        tx_id += 1;
    }

    assert!(offset == total_list_len);
    fixup_acc_rlc(&mut witness, r);

    let witness_len = witness.len();
    assert!(k > (witness_len + 2 + NUM_BLINDING_ROWS) as u32);
    let complete_witness = complete_paddings(
        &mut witness,
        k as usize - witness_len - 2 - NUM_BLINDING_ROWS,
    );

    // for iw in complete_witness.iter().enumerate() {
    //     println!("witness[{}] {:?}", iw.0, iw.1);
    // }
    complete_witness
}

fn fixup_acc_rlc<F: Field>(witness: &mut Vec<RlpDecoderCircuitConfigWitness<F>>, randomness: F) {
    let mut rev_iter = witness.iter_mut().rev();
    let mut prev: Option<&mut RlpDecoderCircuitConfigWitness<F>> = None;
    while let Some(current_witness) = rev_iter.next() {
        let prev_acc_rlc_value =
            prev.map_or(F::zero(), |w| w.acc_rlc_value * current_witness.r_mult);
        current_witness.acc_rlc_value =
            prev_acc_rlc_value + rlc::value(&current_witness.bytes, randomness);

        prev = Some(current_witness);
    }
}
fn complete_paddings<F: Field>(
    witness: &mut Vec<RlpDecoderCircuitConfigWitness<F>>,
    num_padding_to_last_row: usize,
) -> Vec<RlpDecoderCircuitConfigWitness<F>> {
    let mut complete_witness = vec![];
    let mut pre_padding = RlpDecoderCircuitConfigWitness::<F>::default();
    pre_padding.rlp_remain_length =
        witness[0].rlp_remain_length + witness[0].rlp_bytes_in_row as usize;

    complete_witness.push(pre_padding);
    witness[0].q_first = true;
    complete_witness.append(witness);

    for i in 0..num_padding_to_last_row {
        complete_witness.push(RlpDecoderCircuitConfigWitness::<F> {
            tx_id: 0,
            tx_type: RlpTxTypeTag::TxLegacyType,
            tx_member: RlpTxFieldTag::Padding,
            complete: true,
            rlp_type: RlpDecodeTypeTag::DoNothing,
            rlp_tx_member_length: 0,
            rlp_bytes_in_row: 0,
            r_mult: F::zero(),
            rlp_remain_length: 0,
            value: F::zero(),
            acc_rlc_value: F::zero(),
            bytes: [0; MAX_BYTE_COLUMN_NUM].to_vec(),
            decodable: true,
            valid: true,
            q_enable: true,
            q_first: false,
            q_last: i == num_padding_to_last_row - 1,
        });
    }
    complete_witness.push(RlpDecoderCircuitConfigWitness::<F>::default());
    complete_witness
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
            let (_rlp_unsigned, _rlp_signed) = {
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
    use super::{rlp_decode_tx_list_manually, SignedTransaction};
    use ethers_core::utils::rlp;
    use halo2_proofs::halo2curves::bn256::Fr;
    use hex;
    use mock::AddrOrWallet;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    fn prepare_legacy_txlist_rlp_bytes(txs_num: usize) -> Vec<u8> {
        // let tx: SignedTransaction = mock::CORRECT_MOCK_TXS[1].clone().into();
        // let rlp_tx = rlp::encode(&tx);
        // println!("{:?}", hex::encode(rlp_tx));

        let txs: Vec<SignedTransaction> = vec![mock::CORRECT_MOCK_TXS[0].clone().into(); txs_num];
        let rlp_txs = rlp::encode_list(&txs);
        println!("rlp_txs = {:?}", hex::encode(rlp_txs.clone()));

        let rlp_bytes = rlp_txs.to_vec();
        println!("rlp_bytes = {:?}", hex::encode(&rlp_bytes));
        rlp_bytes
    }

    fn prepare_eip1559_txlist_rlp_bytes() -> Vec<u8> {
        todo!()
    }

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

    #[test]
    fn test_correct_witness_generation_empty_list() {
        let rlp_bytes = prepare_legacy_txlist_rlp_bytes(0);
        let randomness = Fr::from(100);
        let k = 128;

        let witness = rlp_decode_tx_list_manually::<Fr>(&rlp_bytes, randomness, k);
        for (i, w) in witness.iter().enumerate() {
            print!("witness[{}] = {:?}\n", i, w);
        }
    }

    #[test]
    fn test_correct_witness_generation_1tx() {
        let rlp_bytes = prepare_legacy_txlist_rlp_bytes(1);
        let randomness = Fr::from(100);
        let k = 128;

        let witness = rlp_decode_tx_list_manually::<Fr>(&rlp_bytes, randomness, k);
        for (i, w) in witness.iter().enumerate() {
            print!("witness[{}] = {:?}\n", i, w);
        }
    }

    #[test]
    fn test_correct_witness_generation_11tx() {
        let rlp_bytes = prepare_legacy_txlist_rlp_bytes(11);
        let randomness = Fr::from(100);
        let k = 256;

        let witness = rlp_decode_tx_list_manually::<Fr>(&rlp_bytes, randomness, k);
        for (i, w) in witness.iter().enumerate() {
            print!("witness[{}] = {:?}\n", i, w);
        }
    }

    #[test]
    fn test_correct_witness_generation_big_data() {
        let mut rng = ChaCha20Rng::seed_from_u64(2u64);
        let tx: SignedTransaction = mock::MockTransaction::default()
            .from(AddrOrWallet::random(&mut rng))
            .input(eth_types::Bytes::from(
                (0..55).map(|v| v as u8).collect::<Vec<u8>>(),
            ))
            .build()
            .into();

        let rlp_txs = rlp::encode_list(&[tx]);
        println!("rlp_txs = {:?}", hex::encode(rlp_txs.clone()));
        let randomness = Fr::from(100);
        let k = 256;

        let witness = rlp_decode_tx_list_manually::<Fr>(&rlp_txs.to_vec(), randomness, k);
        for (i, w) in witness.iter().enumerate() {
            print!("witness[{}] = {:?}\n", i, w);
        }
    }

    #[test]
    fn test_wrong_witness_generation() {
        todo!()
    }
}

#[cfg(test)]
mod rlp_decode_circuit_tests {
    use super::*;
    use crate::util::log2_ceil;
    use halo2_proofs::{
        dev::{MockProver, VerifyFailure},
        halo2curves::bn256::Fr,
    };
    use mock::AddrOrWallet;
    use pretty_assertions::assert_eq;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    fn run<F: Field>(txs: Vec<Transaction>) -> Result<(), Vec<VerifyFailure>> {
        let k = log2_ceil(RlpDecoderCircuit::<Fr>::min_num_rows_from_tx(&txs).0);

        let encodable_txs: Vec<SignedTransaction> =
            txs.iter().map(|tx| tx.into()).collect::<Vec<_>>();
        let rlp_bytes = rlp::encode_list(&encodable_txs);
        println!(
            "input rlp_bytes = {:?}, k = {}.",
            hex::encode(&rlp_bytes),
            k
        );

        let circuit = RlpDecoderCircuit::<F>::new(rlp_bytes.to_vec(), k as usize);
        let prover = match MockProver::run(k, &circuit, vec![]) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        prover.verify()
    }

    #[test]
    #[ignore]
    fn tx_circuit_0tx() {
        // 0xc0 is for invalid case.
        assert_eq!(run::<Fr>(vec![]), Ok(()));
    }

    #[test]
    fn tx_circuit_1tx() {
        let tx: Transaction = mock::CORRECT_MOCK_TXS[0].clone().into();
        assert_eq!(run::<Fr>(vec![tx]), Ok(()));
    }

    #[test]
    fn tx_circuit_2tx() {
        let tx1: Transaction = mock::CORRECT_MOCK_TXS[0].clone().into();
        let tx2: Transaction = mock::CORRECT_MOCK_TXS[1].clone().into();
        assert_eq!(run::<Fr>(vec![tx1, tx2]), Ok(()));
    }

    #[test]
    fn tx_circuit_1tx_non_to() {
        let mut rng = ChaCha20Rng::seed_from_u64(2u64);
        let tx = mock::MockTransaction::default()
            .from(AddrOrWallet::random(&mut rng))
            .build()
            .into();
        assert_eq!(run::<Fr>(vec![tx]), Ok(()));
    }

    #[test]
    fn tx_circuit_tx_with_various_input() {
        let mut rng = ChaCha20Rng::seed_from_u64(2u64);
        let mut tx = mock::MockTransaction::default()
            .from(AddrOrWallet::random(&mut rng))
            .input(eth_types::Bytes::from(b"0"))
            .build()
            .into();
        assert_eq!(run::<Fr>(vec![tx]), Ok(()));

        tx = mock::MockTransaction::default()
            .from(AddrOrWallet::random(&mut rng))
            .input(eth_types::Bytes::from(b"1"))
            .build()
            .into();
        assert_eq!(run::<Fr>(vec![tx]), Ok(()));

        tx = mock::MockTransaction::default()
            .from(AddrOrWallet::random(&mut rng))
            .input(eth_types::Bytes::from(
                (0..55).map(|v| v % 255).collect::<Vec<u8>>(),
            ))
            .build()
            .into();
        assert_eq!(run::<Fr>(vec![tx]), Ok(()));

        tx = mock::MockTransaction::default()
            .from(AddrOrWallet::random(&mut rng))
            .input(eth_types::Bytes::from(
                (0..65536).map(|v| v as u8).collect::<Vec<u8>>(),
            ))
            .build()
            .into();
        assert_eq!(run::<Fr>(vec![tx]), Ok(()));

        tx = mock::MockTransaction::default()
            .from(AddrOrWallet::random(&mut rng))
            .input(eth_types::Bytes::from(
                (0..65536 * 2).map(|v| v as u8).collect::<Vec<u8>>(),
            ))
            .build()
            .into();
        assert_eq!(run::<Fr>(vec![tx.clone(), tx.clone()]), Ok(()));
    }
}

#[cfg(test)]
mod bench {
    use super::*;
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
    use rand::SeedableRng;
    use rand_chacha::ChaChaRng;
    use std::env::var;

    #[test]
    fn bench_rlp_decode_circuit_prover() {
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
        let input_bytes = hex::decode("f850f84e8001830f4240808080820a97a0805d3057e9b74379d814e2c4d264be888a9b560ea2256781af8a6ea83af41208a07168d2b6d3aa47cbc5020c8a9b120926a197e1135b3aaa13ef0b292663345c15").unwrap();
        let circuit = RlpDecoderCircuit::<Fr>::new(input_bytes, degree as usize);

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
