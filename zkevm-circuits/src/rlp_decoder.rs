//! The rlp decoding transaction list circuit implementation.

use std::marker::PhantomData;

use crate::{
    evm_circuit::util::{constraint_builder::BaseConstraintBuilder, rlc},
    impl_expr,
    rlp_decoder_tables::{
        RlpDecodeRule, RlpDecoderFixedTable, RlpDecoderFixedTableTag, RLP_TX_FIELD_DECODE_RULES,
    },
    table::KeccakTable,
    util::{log2_ceil, Challenges, SubCircuit, SubCircuitConfig},
    witness,
};
use eth_types::{Field, Signature, Transaction, Word};
use ethers_core::{
    types::TransactionRequest,
    utils::rlp::{self, PayloadInfo},
};
use gadgets::{
    less_than::{LtChip, LtConfig, LtInstruction},
    util::{and, not, or, sum},
};
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, SecondPhase, Selector,
    },
    poly::Rotation,
};
use keccak256::plain::Keccak;

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

type RlpDecoderFixedTable6Columns = RlpDecoderFixedTable<6>;

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
    /// ShortString: 0x81~0xb7, value means bytes without leading 0
    ShortStringValue,
    /// ShortString: 0x81~0xb7, bytes contains leading 0
    ShortStringBytes,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
/// index type of decode error
pub enum RlpDecodeErrorType {
    /// the first byte is invalid, for example 0x00 for byte or 0xBF for list
    HeaderDecError,
    /// the length of rlp is invalid, for example 0xB854 or 0xB900FF for string
    LenOfLenError,
    /// the value of rlp is invalid, for example 0x8100 or 0x8179 for string
    ValueError,
    /// the rlp is not complete, for example 0xF8<EOF> for list
    RunOutOfDataError,
}
const RLP_DECODE_ERROR_TYPE_NUM: usize = RlpDecodeErrorType::RunOutOfDataError as usize + 1;

impl<T, const N: usize> std::ops::Index<RlpDecodeErrorType> for [T; N] {
    type Output = T;

    fn index(&self, index: RlpDecodeErrorType) -> &Self::Output {
        &self[index as usize]
    }
}

impl<T> std::ops::Index<RlpDecodeErrorType> for Vec<T> {
    type Output = T;

    fn index(&self, index: RlpDecodeErrorType) -> &Self::Output {
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
    /// DecodeError
    DecodeError,
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
#[derive(Clone, Debug, Default, PartialEq, Eq)]
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
    /// decode error types: [header, len_of_len, value, run_out_of_data]
    pub errors: [bool; RLP_DECODE_ERROR_TYPE_NUM],
    /// valid, 0 for invalid, 1 for valid, should be == decodable at the end of the circuit
    pub valid: bool,
    /// full chip enable
    pub q_enable: bool,
    /// the begining
    pub q_first: bool,
    /// the end
    pub q_last: bool,
    /// r_mult_comp
    pub r_mult_comp: F,
    /// rlc_quotient
    pub rlc_quotient: F,
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
    /// r_mult column, (length, r_mult) => @fixed, r_mult == r ^ length
    pub r_mult: Column<Advice>,
    /// remain_length, to be 0 at the end.
    pub rlp_remain_length: Column<Advice>,
    /// value
    pub value: Column<Advice>,
    /// acc_rlc_value
    pub acc_rlc_value: Column<Advice>,
    /// bytes
    pub bytes: [Column<Advice>; MAX_BYTE_COLUMN_NUM],
    /// decode error types: [header, len_of_len, value, run_out_of_data]
    pub errors: [Column<Advice>; RLP_DECODE_ERROR_TYPE_NUM],
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
    /// aux tables
    pub aux_tables: RlpDecoderCircuitConfigArgs<F>,
    /// condition check for <=55
    pub v_gt_55: LtConfig<F, 1>,
    /// condition check for > 0
    pub v_gt_0: LtConfig<F, 1>,
    /// condition check for prev_remain_length > 33
    pub remain_length_gt_33: LtConfig<F, 4>,
    /// condition check for prev_remain_length >= cur_length
    pub remain_length_ge_length: LtConfig<F, 4>,
    /// divide factor for big endian rlc, r_mult_comp * r_mult = r ^ MAX_BYTE_COLUMN_NUM(33)
    pub r_mult_comp: Column<Advice>,
    /// quotient value for big endian rlc, rlc_quotient = rlc[0..MAX_BYTE_COLUMN_NUM] / r_mult_comp
    pub rlc_quotient: Column<Advice>,
}

#[derive(Clone, Debug)]
/// Circuit configuration arguments
pub struct RlpDecoderCircuitConfigArgs<F: Field> {
    /// shared fixed tables
    pub rlp_fixed_table: RlpDecoderFixedTable6Columns,
    /// KeccakTable
    pub keccak_table: KeccakTable,
    /// Challenges
    pub challenges: Challenges<Expression<F>>,
}

impl<F: Field> SubCircuitConfig<F> for RlpDecoderCircuitConfig<F> {
    type ConfigArgs = RlpDecoderCircuitConfigArgs<F>;

    /// Return a new RlpDecoderCircuitConfig
    fn new(meta: &mut ConstraintSystem<F>, aux_tables: Self::ConfigArgs) -> Self {
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
        let decode_errors: [Column<Advice>; RLP_DECODE_ERROR_TYPE_NUM] = (0
            ..RLP_DECODE_ERROR_TYPE_NUM)
            .map(|_| meta.advice_column())
            .collect::<Vec<Column<Advice>>>()
            .try_into()
            .unwrap();
        let valid = meta.advice_column();
        let q_tx_members: [Column<Advice>; LEGACY_TX_FIELD_NUM as usize] = (0..LEGACY_TX_FIELD_NUM)
            .map(|_| meta.advice_column())
            .collect::<Vec<Column<Advice>>>()
            .try_into()
            .unwrap();
        let q_enable = meta.complex_selector();
        let q_first = meta.fixed_column();
        let q_last = meta.fixed_column();
        let r_mult_comp = meta.advice_column();
        let rlc_quotient = meta.advice_column();

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

        let cmp_55_lt_byte1 = LtChip::configure(
            meta,
            |meta| {
                rlp_type_enabled!(meta, RlpDecodeTypeTag::LongList1) * meta.query_selector(q_enable)
            },
            |_| 55.expr(),
            |meta| meta.query_advice(bytes[1], Rotation::cur()),
        );

        let cmp_0_lt_byte1 = LtChip::configure(
            meta,
            |meta| {
                or::expr([
                    rlp_type_enabled!(meta, RlpDecodeTypeTag::ShortStringValue),
                    rlp_type_enabled!(meta, RlpDecodeTypeTag::LongList2),
                    rlp_type_enabled!(meta, RlpDecodeTypeTag::LongList3),
                ]) * meta.query_selector(q_enable)
            },
            |_| 0.expr(),
            |meta| meta.query_advice(bytes[1], Rotation::cur()),
        );

        let cmp_bytes_in_row_lt_prev_remain: LtConfig<F, 4> = LtChip::configure(
            meta,
            |meta| {
                not::expr(meta.query_advice(valid, Rotation::cur())) * meta.query_selector(q_enable)
            },
            |_| MAX_BYTE_COLUMN_NUM.expr(),
            |meta| meta.query_advice(rlp_remain_length, Rotation::prev()),
        );

        // less equal n == less than n+1
        let cmp_length_le_prev_remain: LtConfig<F, 4> = LtChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| meta.query_advice(rlp_tx_member_length, Rotation::cur()),
            |meta| meta.query_advice(rlp_remain_length, Rotation::prev()) + 1.expr(),
        );

        /////////////////////////////////
        //// lookups
        //// /////////////////////////////
        // output txlist hash check
        // meta.lookup_any("comsumed all bytes correctly", |meta| {
        //     let is_enabled = meta.query_fixed(q_first, Rotation::next());
        //     let input_rlc = meta.query_advice(acc_rlc_value, Rotation::cur());
        //     let input_len = meta.query_advice(rlp_remain_length, Rotation::cur());
        //     let hash_rlc = meta.query_advice(value, Rotation::cur());

        //     let table = &aux_tables.keccak_table;
        //     let table_is_enabled = meta.query_advice(table.is_enabled, Rotation::cur());
        //     let table_input_rlc = meta.query_advice(table.input_rlc, Rotation::cur());
        //     let table_input_len = meta.query_advice(table.input_len, Rotation::cur());
        //     let table_hash_rlc = meta.query_advice(table.output_rlc, Rotation::cur());

        //     vec![
        //         (is_enabled.expr(), table_is_enabled.expr()),
        //         (is_enabled.expr() * input_rlc.expr(), table_input_rlc.expr()),
        //         (is_enabled.expr() * input_len.expr(), table_input_len.expr()),
        //         (is_enabled.expr() * hash_rlc.expr(), table_hash_rlc.expr()),
        //     ]
        // });

        // bytes range check
        bytes.iter().for_each(|byte| {
            meta.lookup_any("rlp byte range check", |meta| {
                let table = &aux_tables.rlp_fixed_table.byte_range_table;
                let table_tag = meta.query_fixed(table.table_tag, Rotation::cur());
                let value = meta.query_fixed(table.value, Rotation::cur());
                vec![
                    (RlpDecoderFixedTableTag::Range256.expr(), table_tag.expr()),
                    (meta.query_advice(*byte, Rotation::cur()), value.expr()),
                ]
            });
        });

        // lookup rlp_types table
        // TODO: bytes[1] as prefix of len also need to be constrainted
        meta.lookup_any("rlp decodable check", |meta| {
            let tx_type = meta.query_advice(tx_type, Rotation::cur());
            let tx_member_cur = meta.query_advice(tx_member, Rotation::cur());
            let byte0 = meta.query_advice(bytes[0], Rotation::cur());
            let decodable = not::expr(meta.query_advice(
                decode_errors[RlpDecodeErrorType::HeaderDecError],
                Rotation::cur(),
            ));
            let prev_is_valid = meta.query_advice(valid, Rotation::prev());
            let q_enable = meta.query_selector(q_enable);

            let is_not_partial = not::expr(rlp_type_enabled!(meta, RlpDecodeTypeTag::PartialRlp));

            let table = &aux_tables.rlp_fixed_table.tx_decode_table;
            let table_tag = meta.query_fixed(table.table_tag, Rotation::cur());
            let tx_type_in_table = meta.query_fixed(table.tx_type, Rotation::cur());
            let tx_member_in_table = meta.query_fixed(table.tx_field_tag, Rotation::cur());
            let byte0_in_table = meta.query_fixed(table.byte_0, Rotation::cur());
            let decodable_in_table = meta.query_fixed(table.decodable, Rotation::cur());

            let query_able = q_enable.expr() * is_not_partial.expr() * prev_is_valid.expr();
            vec![
                (
                    query_able.expr() * RlpDecoderFixedTableTag::RlpDecoderTable.expr(),
                    table_tag,
                ),
                (query_able.expr() * tx_type, tx_type_in_table),
                (query_able.expr() * tx_member_cur, tx_member_in_table),
                (query_able.expr() * byte0, byte0_in_table),
                (query_able.expr() * decodable, decodable_in_table),
            ]
        });

        // // lookup tx_field_switch table
        meta.lookup_any("rlp tx field transition", |meta| {
            let current_member = meta.query_advice(tx_member, Rotation::cur());
            let next_member = meta.query_advice(tx_member, Rotation::next());

            let table = &aux_tables.rlp_fixed_table.tx_member_switch_table;
            let table_tag = meta.query_fixed(table.table_tag, Rotation::cur());
            let curr_member_in_table = meta.query_fixed(table.current_tx_field, Rotation::cur());
            let next_member_in_table = meta.query_fixed(table.next_tx_field, Rotation::cur());
            let q_enable = meta.query_selector(q_enable);
            let is_last = meta.query_fixed(q_last, Rotation::cur());

            let query_able = and::expr([not::expr(is_last.expr()), q_enable.expr()]);
            vec![
                (
                    query_able.expr() * RlpDecoderFixedTableTag::TxFieldSwitchTable.expr(),
                    table_tag,
                ),
                (query_able.expr() * current_member, curr_member_in_table),
                (query_able.expr() * next_member, next_member_in_table),
            ]
        });

        // lookup r_mult/r_mult_comp table with length,
        // TODO: r_mult is adv, add constraint for pow
        meta.lookup_any("rlp r_mult check", |meta| {
            let r_mult = meta.query_advice(r_mult, Rotation::cur());
            let pow = meta.query_advice(tx_member_bytes_in_row, Rotation::cur());

            let table = &aux_tables.rlp_fixed_table.r_mult_pow_table;
            let table_tag = meta.query_fixed(table.table_tag, Rotation::cur());
            let r_mult_in_table = meta.query_fixed(table.r_mult, Rotation::cur());
            let r_pow_in_table = meta.query_fixed(table.length, Rotation::cur());

            let q_enable = meta.query_selector(q_enable);
            vec![
                (
                    q_enable.expr() * RlpDecoderFixedTableTag::RMult.expr(),
                    table_tag,
                ),
                (q_enable.expr() * r_mult, r_mult_in_table),
                (q_enable.expr() * pow, r_pow_in_table),
            ]
        });
        meta.lookup_any("rlp r_mult_comp check", |meta| {
            let r_mult_comp = meta.query_advice(r_mult_comp, Rotation::cur());
            let pow = 33.expr() - meta.query_advice(tx_member_bytes_in_row, Rotation::cur());

            let table = &aux_tables.rlp_fixed_table.r_mult_pow_table;
            let table_tag = meta.query_fixed(table.table_tag, Rotation::cur());
            let r_mult_in_table = meta.query_fixed(table.r_mult, Rotation::cur());
            let r_pow_in_table = meta.query_fixed(table.length, Rotation::cur());

            let q_enable = meta.query_selector(q_enable);
            vec![
                (
                    q_enable.expr() * RlpDecoderFixedTableTag::RMult.expr(),
                    table_tag,
                ),
                (q_enable.expr() * r_mult_comp, r_mult_in_table),
                (q_enable.expr() * pow, r_pow_in_table),
            ]
        });

        /////////////////////////////////
        //// constraints
        //// /////////////////////////////
        meta.create_gate("common constraints for all rows", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            // boolean constraints
            cb.require_boolean(
                "field complete boolean",
                meta.query_advice(complete, Rotation::cur()),
            );
            decode_errors.iter().for_each(|error| {
                cb.require_boolean(
                    "decode error is boolean",
                    meta.query_advice(*error, Rotation::cur()),
                );
            });
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

            let r_mult = meta.query_advice(r_mult, Rotation::cur());
            let acc_rlc_cur = meta.query_advice(acc_rlc_value, Rotation::cur());
            let rev_byte_cells = bytes
                .iter()
                .rev()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let rlc_quotient = meta.query_advice(rlc_quotient, Rotation::cur());
            let r_mult_comp = meta.query_advice(r_mult_comp, Rotation::cur());
            cb.require_equal(
                "rlc_quotient = rlc[0..32]/r_mult_comp",
                rlc_quotient.expr() * r_mult_comp.expr(),
                rlc::expr(&rev_byte_cells, aux_tables.challenges.keccak_input()),
            );
            cb.require_equal(
                "rlc = prev_rlc * r_mult + rlc[0..32]/r_mult_comp",
                acc_rlc_cur,
                r_mult * meta.query_advice(acc_rlc_value, Rotation::prev()) + rlc_quotient.expr(),
            );

            let valid_cur = meta.query_advice(valid, Rotation::cur());
            let valid_next = meta.query_advice(valid, Rotation::next());
            cb.require_equal(
                "valid should be consistent after invalid",
                and::expr([valid_cur.expr(), valid_next.expr()]),
                valid_next.expr(),
            );

            // if not in error state and not in padding state, the valid comes from the error states
            let not_error_state = not::expr(
                meta.query_advice(q_tx_members[RlpTxFieldTag::DecodeError], Rotation::cur()),
            );
            let not_padding_state =
                not::expr(meta.query_advice(q_tx_members[RlpTxFieldTag::Padding], Rotation::cur()));
            cb.condition(and::expr([not_error_state, not_padding_state]), |cb| {
                cb.require_equal(
                    "if any(errors) then valid must false",
                    or::expr(
                        decode_errors
                            .iter()
                            .map(|e| meta.query_advice(*e, Rotation::cur()))
                            .collect::<Vec<Expression<F>>>(),
                    ),
                    not::expr(valid_cur.expr()),
                )
            });

            cb.condition(valid_cur.expr(), |cb| {
                cb.require_equal(
                    "check if bytes run out",
                    cmp_length_le_prev_remain.is_lt(meta, None),
                    1.expr(),
                );
            });

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
            let bytes_in_row_cur = meta.query_advice(tx_member_bytes_in_row, Rotation::cur());
            let remain_length = meta.query_advice(rlp_remain_length, Rotation::cur());
            let byte_cells_cur = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let q_tx_rlp_header =
                meta.query_advice(q_tx_members[RlpTxFieldTag::TxRlpHeader], Rotation::cur());
            let q_dec_error =
                meta.query_advice(q_tx_members[RlpTxFieldTag::DecodeError], Rotation::cur());
            let q_enable = meta.query_selector(q_enable);
            let q_first = meta.query_fixed(q_first, Rotation::cur());

            // length with leading bytes
            cb.condition(rlp_type_enabled!(meta, RlpDecodeTypeTag::DoNothing), |cb| {
                cb.require_equal("0 length", rlp_tag_length_cur.clone(), 0.expr())
            });
            cb.condition(
                rlp_type_enabled!(meta, RlpDecodeTypeTag::SingleByte),
                |cb| {
                    cb.require_equal("single length", rlp_tag_length_cur.clone(), 1.expr());
                    // TODO:
                },
            );
            cb.condition(rlp_type_enabled!(meta, RlpDecodeTypeTag::NullValue), |cb| {
                cb.require_equal("empty length", rlp_tag_length_cur.clone(), 1.expr())
            });
            cb.condition(
                rlp_type_enabled!(meta, RlpDecodeTypeTag::ShortStringValue),
                |cb| {
                    cb.require_equal(
                        "ShortStringValue length",
                        rlp_tag_length_cur.clone(),
                        byte_cells_cur[0].expr() - 0x80.expr() + 1.expr(),
                    );

                    // 0x8100 is invalid for value, 0x8180 instead
                    cb.require_equal(
                        "v should be >0",
                        cmp_0_lt_byte1.is_lt(meta, None),
                        not::expr(meta.query_advice(
                            decode_errors[RlpDecodeErrorType::ValueError],
                            Rotation::cur(),
                        )),
                    )
                },
            );
            cb.condition(
                rlp_type_enabled!(meta, RlpDecodeTypeTag::ShortStringBytes),
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
                        rlp_tag_length_cur.expr(),
                        byte_cells_cur[1].expr() + 2.expr(),
                    );

                    let len_valid = not::expr(meta.query_advice(
                        decode_errors[RlpDecodeErrorType::LenOfLenError],
                        Rotation::cur(),
                    ));
                    // 0x8100 is invalid for value, 0x8180 instead
                    cb.require_equal(
                        "length of 0xb8 should be >55",
                        cmp_55_lt_byte1.is_lt(meta, None),
                        len_valid.expr(),
                    );
                },
            );
            cb.condition(
                rlp_type_enabled!(meta, RlpDecodeTypeTag::LongString2),
                |cb| {
                    cb.require_equal(
                        "Long String 0xb9 length",
                        rlp_tag_length_cur.clone(),
                        byte_cells_cur[1].expr() * 256.expr() + byte_cells_cur[2].expr() + 3.expr(),
                    );

                    // 0x8100 is invalid for value, 0x8180 instead
                    cb.require_equal(
                        "lenght 0 of 0xb9 should be >0",
                        cmp_0_lt_byte1.is_lt(meta, None),
                        not::expr(meta.query_advice(
                            decode_errors[RlpDecodeErrorType::LenOfLenError],
                            Rotation::cur(),
                        )),
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
                    );
                    // 0x8100 is invalid for value, 0x8180 instead
                    cb.require_equal(
                        "length 0 of 0xba should be >0",
                        cmp_0_lt_byte1.is_lt(meta, None),
                        not::expr(meta.query_advice(
                            decode_errors[RlpDecodeErrorType::LenOfLenError],
                            Rotation::cur(),
                        )),
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

            cb.gate(and::expr([
                q_enable,
                not::expr(q_first),
                not::expr(q_dec_error),
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
            let init_acc_rlc = meta.query_advice(acc_rlc_value, Rotation::prev());
            let rlp_tag_length_cur = meta.query_advice(rlp_tx_member_length, Rotation::cur());
            let remain_length = meta.query_advice(rlp_remain_length, Rotation::cur());
            let byte_cells_cur = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let valid = meta.query_advice(valid, Rotation::cur());
            let q_first = meta.query_fixed(q_first, Rotation::cur());

            cb.require_zero("0 tx_id", tx_id);
            cb.require_zero("0 tx_type", tx_type_cur.expr());
            cb.require_zero("0 tx_tag", tx_member_cur);
            cb.require_equal("field completed", complete.expr(), 1.expr());
            cb.require_zero("init acc rlc is 0", init_acc_rlc);

            cb.condition(
                rlp_type_enabled!(meta, RlpDecodeTypeTag::LongList1) * valid.expr(),
                |cb| {
                    cb.require_equal(
                        "long length 1 byte after 0xf8",
                        remain_length.expr(),
                        byte_cells_cur[1].expr(),
                    );

                    // TODO: byte_cells_cur[1] > 55, and check with len_decode flag
                    cb.require_equal(
                        "v should be >55",
                        cmp_55_lt_byte1.is_lt(meta, None),
                        1.expr(),
                    )
                },
            );
            cb.condition(
                rlp_type_enabled!(meta, RlpDecodeTypeTag::LongList2) * valid.expr(),
                |cb| {
                    cb.require_equal(
                        "long length 2 bytes after f9",
                        remain_length.expr(),
                        byte_cells_cur[1].expr() * 256.expr() + byte_cells_cur[2].expr(),
                    );
                    // TODO: byte_cells_cur[1] != 0, and check with len_decode flag
                    cb.require_equal("v should be >0", cmp_0_lt_byte1.is_lt(meta, None), 1.expr())
                },
            );
            cb.condition(
                rlp_type_enabled!(meta, RlpDecodeTypeTag::LongList3) * valid.expr(),
                |cb| {
                    cb.require_equal(
                        "long length 3 bytes after fa",
                        remain_length.expr(),
                        byte_cells_cur[1].expr() * 65536.expr()
                            + byte_cells_cur[2].expr() * 256.expr()
                            + byte_cells_cur[3].expr(),
                    );
                    // TODO: byte_cells_cur[1] != 0, and check with len_decode flag
                    cb.require_equal("v should be >0", cmp_0_lt_byte1.is_lt(meta, None), 1.expr())
                },
            );

            cb.condition(valid, |cb| {
                cb.require_equal(
                    "rlp_tag_length = rlp_header length",
                    rlp_tag_length_cur.expr(),
                    byte_cells_cur[0].expr() - 247.expr() + 1.expr(),
                );
            });

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
            let byte_cells_cur = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let decodable = not::expr(meta.query_advice(
                decode_errors[RlpDecodeErrorType::HeaderDecError],
                Rotation::cur(),
            ));
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
            let acc_rlc = meta.query_advice(acc_rlc_value, Rotation::cur());
            let acc_rlc_prev = meta.query_advice(acc_rlc_value, Rotation::prev());
            let bytes_values = bytes
                .iter()
                .map(|byte_col| meta.query_advice(*byte_col, Rotation::cur()))
                .collect::<Vec<_>>();
            let q_padding =
                meta.query_advice(q_tx_members[RlpTxFieldTag::Padding], Rotation::cur());

            cb.require_equal("tag", tx_member_cur, RlpTxFieldTag::Padding.expr());
            cb.require_equal("field completed", complete.expr(), 1.expr());
            cb.require_equal("padding has 1 r_mult", r_mult, 1.expr());
            cb.require_zero("padding has no length", length);
            cb.require_zero("padding has no remain length", remain_length);
            cb.require_zero(
                "last row above padding has no remain length",
                meta.query_advice(rlp_remain_length, Rotation::prev()),
            );
            cb.require_equal("padding has fixed rlc", acc_rlc, acc_rlc_prev);
            bytes_values.iter().for_each(|byte| {
                cb.require_zero("padding has no bytes", byte.expr());
            });

            cb.gate(q_padding.expr() * meta.query_selector(q_enable))
        });

        meta.create_gate("end with padding", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let q_enable = meta.query_selector(q_enable);
            let q_last = meta.query_fixed(q_last, Rotation::cur());
            let q_padding =
                meta.query_advice(q_tx_members[RlpTxFieldTag::Padding], Rotation::cur());

            cb.require_equal("padding at last", q_padding, 1.expr());

            cb.gate(q_last * q_enable)
        });

        // error gates and error state handling
        // 1. each error has its own check to avoid fake error witness
        // 2. error state needs extra logic to process all the rest bytes

        // header error is looked up, so, only check consistence with valid
        meta.create_gate("header decode error", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let q_enable = meta.query_selector(q_enable);
            let header_dec_error = meta.query_advice(
                decode_errors[RlpDecodeErrorType::HeaderDecError],
                Rotation::cur(),
            );
            let is_valid = meta.query_advice(valid, Rotation::cur());
            cb.require_equal(
                "header decode error",
                header_dec_error.expr(),
                not::expr(is_valid),
            );

            cb.gate(q_enable.expr() * header_dec_error.expr())
        });

        // len dec error depends on type
        meta.create_gate("len decode error", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let q_enable = meta.query_selector(q_enable);
            let len_dec_error = meta.query_advice(
                decode_errors[RlpDecodeErrorType::LenOfLenError],
                Rotation::cur(),
            );

            // error if byte_cells_cur[1] < 55 for longlist1
            cb.condition(
                or::expr([
                    rlp_type_enabled!(meta, RlpDecodeTypeTag::LongString1),
                    rlp_type_enabled!(meta, RlpDecodeTypeTag::LongList1),
                ]),
                |cb| {
                    cb.require_zero("error if v <= 55", cmp_55_lt_byte1.is_lt(meta, None));
                },
            );
            // error if byte[1] == 0 for longlist2 & 3
            cb.condition(
                or::expr([
                    rlp_type_enabled!(meta, RlpDecodeTypeTag::LongString2),
                    rlp_type_enabled!(meta, RlpDecodeTypeTag::LongString3),
                    rlp_type_enabled!(meta, RlpDecodeTypeTag::LongList2),
                    rlp_type_enabled!(meta, RlpDecodeTypeTag::LongList3),
                ]),
                |cb| {
                    cb.require_zero("error if v == 0", cmp_0_lt_byte1.is_lt(meta, None));
                },
            );

            cb.gate(q_enable.expr() * len_dec_error)
        });

        meta.create_gate("val decode error", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let q_enable = meta.query_selector(q_enable);
            let val_dec_error = meta.query_advice(
                decode_errors[RlpDecodeErrorType::ValueError],
                Rotation::cur(),
            );

            cb.condition(
                rlp_type_enabled!(meta, RlpDecodeTypeTag::ShortStringValue),
                |cb| {
                    cb.require_zero("error if v == 0", cmp_0_lt_byte1.is_lt(meta, None));
                },
            );
            cb.gate(q_enable.expr() * val_dec_error)
        });

        meta.create_gate("eof decode error", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let q_enable = meta.query_selector(q_enable);
            let is_eof = meta.query_advice(
                decode_errors[RlpDecodeErrorType::RunOutOfDataError],
                Rotation::cur(),
            );

            cb.require_zero(
                "remain < tag_len",
                cmp_length_le_prev_remain.is_lt(meta, None),
            );

            cb.gate(q_enable * is_eof)
        });

        // decode error
        meta.create_gate("Decode Error", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let tx_member_cur = meta.query_advice(tx_member, Rotation::cur());
            let complete = meta.query_advice(complete, Rotation::cur());
            let length = meta.query_advice(rlp_tx_member_length, Rotation::cur());
            let prev_remain_length = meta.query_advice(rlp_remain_length, Rotation::prev());
            let remain_length = meta.query_advice(rlp_remain_length, Rotation::cur());
            let prev_row_valid = meta.query_advice(valid, Rotation::prev());
            let q_error =
                meta.query_advice(q_tx_members[RlpTxFieldTag::DecodeError], Rotation::cur());

            cb.require_equal("tag", tx_member_cur, RlpTxFieldTag::DecodeError.expr());
            cb.require_equal("field completed", complete.expr(), 1.expr());

            // if prev_remain > 33, then length = 33 else, length = prev_remain
            cb.condition(cmp_bytes_in_row_lt_prev_remain.is_lt(meta, None), |cb| {
                cb.require_equal("decode_error length = 33", length.expr(), 33.expr());
            });
            cb.condition(
                not::expr(cmp_bytes_in_row_lt_prev_remain.is_lt(meta, None)),
                |cb| {
                    cb.require_equal(
                        "decode_error length = prev_remain",
                        length.expr(),
                        prev_remain_length.expr(),
                    );
                },
            );

            // remain_length = prev_remain_length - length;
            cb.require_equal(
                "remain_length = prev_remain - length_cur",
                remain_length.expr(),
                prev_remain_length.expr() - length.expr(),
            );
            cb.require_zero("row above is not valid", prev_row_valid.expr());

            cb.gate(q_error.expr() * meta.query_selector(q_enable))
        });

        meta.create_gate("end with padding", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let q_enable = meta.query_selector(q_enable);
            let q_last = meta.query_fixed(q_last, Rotation::cur());
            let q_padding =
                meta.query_advice(q_tx_members[RlpTxFieldTag::Padding], Rotation::cur());

            cb.require_equal("padding at last", q_padding, 1.expr());

            cb.gate(q_last * q_enable)
        });

        let circuit_config = RlpDecoderCircuitConfig {
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
            errors: decode_errors,
            valid,
            q_tx_members,
            q_enable,
            q_first,
            q_last,
            aux_tables,
            v_gt_55: cmp_55_lt_byte1,
            v_gt_0: cmp_0_lt_byte1,
            remain_length_gt_33: cmp_bytes_in_row_lt_prev_remain,
            remain_length_ge_length: cmp_length_le_prev_remain,
            r_mult_comp,
            rlc_quotient,
        };
        circuit_config
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

        let mut prev_wit = wits.last().unwrap();
        for wit in wits {
            let gt_55_chip = LtChip::construct(self.v_gt_55);
            let gt_0_chip = LtChip::construct(self.v_gt_0);

            let gt_33_chip = LtChip::construct(self.remain_length_gt_33);
            let enough_remain_chip = LtChip::construct(self.remain_length_ge_length);

            let leading_val = if wit.bytes.len() > 1 { wit.bytes[1] } else { 0 };
            gt_55_chip.assign(region, offset, F::from(55u64), F::from(leading_val as u64))?;
            gt_0_chip.assign(region, offset, F::zero(), F::from(leading_val as u64))?;

            let remain_bytes = prev_wit.rlp_remain_length as u64;
            let current_member_bytes = wit.rlp_tx_member_length;
            gt_33_chip.assign(region, offset, F::from(33u64), F::from(remain_bytes))?;
            enough_remain_chip.assign(
                region,
                offset,
                F::from(current_member_bytes),
                F::from(remain_bytes) + F::one(),
            )?;

            self.assign_row(region, offset, wit)?;
            prev_wit = wit;
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
        for (i, error) in self.errors.iter().enumerate() {
            region.name_column(|| format!("config.errors-[{}]", i), *error);
        }
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
        for (i, error) in self.errors.iter().enumerate() {
            region.assign_advice(
                || format!("config.errors[{}]", i),
                *error,
                offset,
                || Value::known(F::from(w.errors[i] as u64)),
            )?;
        }
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
        region.assign_advice(
            || "config.r_mult_comp",
            self.r_mult_comp,
            offset,
            || Value::known(F::from(w.r_mult_comp)),
        )?;
        region.assign_advice(
            || "config.rlc_quotient",
            self.rlc_quotient,
            offset,
            || Value::known(F::from(w.rlc_quotient)),
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
        let tables_size = RlpDecoderFixedTable6Columns::table_size();
        log::info!(
            "constraint_size: {}, tables_size: {}",
            constraint_size,
            tables_size
        );
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
        log::trace!(
            "randomness: {:?}, rlc_bytes = {:?}",
            randomness,
            rlc::value(self.bytes.iter().rev(), randomness)
        );

        let witness: Vec<RlpDecoderCircuitConfigWitness<F>> =
            gen_rlp_decode_state_witness(&self.bytes, randomness, self.size);

        for (i, w) in witness.iter().enumerate() {
            log::trace!("witness[{}]: {:?}", i, w);
        }

        config
            .aux_tables
            .rlp_fixed_table
            .load(layouter, challenges)?;

        config
            .aux_tables
            .keccak_table
            .dev_load(layouter, &[self.bytes.clone()], challenges)?;

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
        let rlp_fixed_table = RlpDecoderFixedTable6Columns::construct(meta);
        let keccak_table = KeccakTable::construct(meta);
        let challenges = Challenges::construct(meta);

        let config = {
            // let challenges_expr = challenges.exprs(meta);
            let r = 11u64;
            let challenges_expr = Challenges::mock(r.expr(), r.expr(), r.expr());
            RlpDecoderCircuitConfig::new(
                meta,
                RlpDecoderCircuitConfigArgs {
                    rlp_fixed_table,
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

fn generate_rlp_type_witness(
    tx_member: &RlpTxFieldTag,
    bytes: &[u8],
) -> (RlpDecodeTypeTag, bool, bool, bool) {
    let mut header_decodable = true;
    let mut len_decodable = true;
    let mut value_decodable = true;
    let header_byte = bytes.first().unwrap_or(&0).to_owned();
    let rlp_type = match header_byte {
        0x00 => {
            header_decodable = false;
            RlpDecodeTypeTag::SingleByte
        }
        0x01..=0x7f => RlpDecodeTypeTag::SingleByte,
        0x80 => RlpDecodeTypeTag::NullValue,
        0x81..=0xb7 => {
            if header_byte == 0x81 {
                value_decodable = bytes[1] >= 0x80;
            } else {
                value_decodable = bytes[1] > 0;
            }
            match tx_member {
                RlpTxFieldTag::To => {
                    value_decodable = true;
                    RlpDecodeTypeTag::ShortStringBytes
                }
                RlpTxFieldTag::Data => {
                    value_decodable = true;
                    RlpDecodeTypeTag::ShortStringBytes
                }
                _ => RlpDecodeTypeTag::ShortStringValue,
            }
        }
        0xb8 => {
            len_decodable = bytes[1] >= 0x80;
            RlpDecodeTypeTag::LongString1
        }
        0xb9 => {
            len_decodable = bytes[1] > 0;
            RlpDecodeTypeTag::LongString2
        }
        0xba => {
            len_decodable = bytes[1] > 0;
            RlpDecodeTypeTag::LongString3
        }
        0xc0 => RlpDecodeTypeTag::EmptyList,
        0xc1..=0xf7 => RlpDecodeTypeTag::ShortList,
        0xf8 => RlpDecodeTypeTag::LongList1,
        0xf9 => RlpDecodeTypeTag::LongList2,
        0xfa => RlpDecodeTypeTag::LongList3,
        _ => {
            header_decodable = false;
            RlpDecodeTypeTag::DoNothing
        }
    };
    (rlp_type, header_decodable, len_decodable, value_decodable)
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
    let (mut rlp_type, header_decodable, len_decodable, value_decodable) =
        generate_rlp_type_witness(tx_member, raw_bytes);
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
                    errors: [!header_decodable, !len_decodable, !value_decodable, false],
                    valid: header_decodable && len_decodable && value_decodable,
                    q_enable: true,
                    q_first: false,
                    q_last: false,
                    r_mult_comp: F::one(),
                    rlc_quotient: F::zero(),
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
                errors: [!header_decodable, !len_decodable, !value_decodable, false],
                valid: header_decodable && len_decodable && value_decodable,
                q_enable: true,
                q_first: false,
                q_last: false,
                r_mult_comp: r.pow(&[(MAX_BYTE_COLUMN_NUM - tag_remain_length) as u64, 0, 0, 0]),
                rlc_quotient: F::zero(),
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
        RlpTxFieldTag::DecodeError => witness.append(&mut generate_witness!()),
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

trait RlpTxFieldStateWittnessGenerator<F: Field> {
    fn next(
        &self,
        k: usize,
        tx_id: u64,
        bytes: &[u8],
        r: F,
        witness: &mut Vec<RlpDecoderCircuitConfigWitness<F>>,
    ) -> (Self, Option<usize>)
    where
        Self: Sized;

    fn rlp_decode_field_check(
        &self,
        bytes: &[u8],
        tx_id: u64,
        r: F,
        decode_rule: &RlpDecodeRule,
        witness: &mut Vec<RlpDecoderCircuitConfigWitness<F>>,
        next_state: RlpTxFieldTag,
    ) -> (Self, Option<usize>)
    where
        Self: Sized;
}

// using error to tell n
// consider the case which both error happens like 0xFA 0x00 0x01 EOF, both EOF error & len_of_len
// error happens
fn read_nbytes(bytes: &[u8], n: usize) -> Result<&[u8], &[u8]> {
    if n <= bytes.len() {
        Ok(&bytes[..n])
    } else {
        Err(bytes)
    }
}

fn rlp_bytes_len(bytes: &[u8]) -> usize {
    bytes.iter().fold(0, |acc, byte| acc * 256 + *byte as usize)
}

impl<F: Field> RlpTxFieldStateWittnessGenerator<F> for RlpTxFieldTag {
    fn next(
        &self,
        k: usize,
        tx_id: u64,
        bytes: &[u8],
        r: F,
        witness: &mut Vec<RlpDecoderCircuitConfigWitness<F>>,
    ) -> (Self, Option<usize>) {
        let decode_rules = RLP_TX_FIELD_DECODE_RULES
            .iter()
            .filter(|rule| rule.0 == RlpTxTypeTag::TxLegacyType && rule.1 == *self)
            .collect::<Vec<&(RlpTxTypeTag, RlpTxFieldTag, RlpDecodeRule)>>();
        assert!(decode_rules.len() >= 1);
        let (_, _, mut decode_rule) = decode_rules[0];

        macro_rules! state_switch {
            ($next_state: expr) => {
                self.rlp_decode_field_check(bytes, tx_id, r, &decode_rule, witness, $next_state)
            };
        }

        match self {
            RlpTxFieldTag::TxListRlpHeader => state_switch!(RlpTxFieldTag::TxRlpHeader),
            RlpTxFieldTag::TxRlpHeader => state_switch!(RlpTxFieldTag::Nonce),
            RlpTxFieldTag::Nonce => state_switch!(RlpTxFieldTag::GasPrice),
            RlpTxFieldTag::GasPrice => state_switch!(RlpTxFieldTag::Gas),
            RlpTxFieldTag::Gas => state_switch!(RlpTxFieldTag::To),
            RlpTxFieldTag::To => {
                assert!(decode_rules.len() == 2);
                if bytes.len() >= 1 && bytes[0] == 0x80 {
                    // empty to address
                    decode_rule = decode_rules[1].2;
                }
                state_switch!(RlpTxFieldTag::Value)
            }
            RlpTxFieldTag::Value => state_switch!(RlpTxFieldTag::Data),
            RlpTxFieldTag::Data => state_switch!(RlpTxFieldTag::SignV),
            RlpTxFieldTag::SignV => state_switch!(RlpTxFieldTag::SignR),
            RlpTxFieldTag::SignR => state_switch!(RlpTxFieldTag::SignS),
            RlpTxFieldTag::SignS => {
                // Tricky: we need to check if the bytes hold SignS only.
                let next_state = if bytes.len() == MAX_BYTE_COLUMN_NUM {
                    RlpTxFieldTag::Padding
                } else {
                    RlpTxFieldTag::TxRlpHeader
                };
                self.rlp_decode_field_check(bytes, tx_id, r, &decode_rule, witness, next_state)
            }
            RlpTxFieldTag::Padding => {
                let witness_len = witness.len();
                assert!(k > (witness_len + 1 + NUM_BLINDING_ROWS));
                fixup_acc_rlc_new(witness, r);
                complete_paddings_new(witness, r, k as usize - witness_len - 1 - NUM_BLINDING_ROWS);
                (RlpTxFieldTag::Padding, None)
            }
            RlpTxFieldTag::ChainID => todo!(),
            RlpTxFieldTag::GasTipCap => todo!(),
            RlpTxFieldTag::GasFeeCap => todo!(),
            RlpTxFieldTag::AccessList => todo!(),
            RlpTxFieldTag::DecodeError => {
                let rest_bytes = bytes.len().min(MAX_BYTE_COLUMN_NUM);
                let rlp_remain_length: usize = witness.last().unwrap().rlp_remain_length;
                witness.append(&mut generate_rlp_row_witness_new(
                    tx_id,
                    self,
                    &bytes[..rest_bytes],
                    r,
                    rlp_remain_length,
                    None,
                ));

                if rest_bytes == bytes.len() {
                    (RlpTxFieldTag::Padding, Some(rest_bytes))
                } else {
                    (RlpTxFieldTag::DecodeError, Some(rest_bytes))
                }
            }
        }
    }

    fn rlp_decode_field_check(
        &self,
        bytes: &[u8],
        tx_id: u64,
        r: F,
        decode_rule: &RlpDecodeRule,
        witness: &mut Vec<RlpDecoderCircuitConfigWitness<F>>,
        next_state: RlpTxFieldTag,
    ) -> (RlpTxFieldTag, Option<usize>) {
        let rlp_remain_length: usize = witness.last().unwrap().rlp_remain_length;
        let res = read_nbytes(bytes, 1);
        match res {
            Ok(bytes_read_header) => {
                let head_byte0 = bytes_read_header[0];
                // if decode rule check failed
                let (_, decodable) = decode_rule.rule_check(head_byte0);
                if !decodable {
                    witness.append(&mut generate_rlp_row_witness_new(
                        tx_id,
                        self,
                        &bytes[..1],
                        r,
                        rlp_remain_length,
                        Some(RlpDecodeErrorType::HeaderDecError),
                    ));
                    (RlpTxFieldTag::DecodeError, Some(1))
                } else {
                    match decode_rule {
                        RlpDecodeRule::Padding => unreachable!(),
                        RlpDecodeRule::Empty => match head_byte0 {
                            0x80 => {
                                witness.append(&mut generate_rlp_row_witness_new(
                                    tx_id,
                                    self,
                                    &bytes[..1],
                                    r,
                                    rlp_remain_length,
                                    None,
                                ));
                                (next_state, Some(1))
                            }
                            _ => unreachable!(),
                        },
                        RlpDecodeRule::Uint64 => unreachable!(),
                        RlpDecodeRule::Uint96 => match head_byte0 {
                            1..=0x80 => {
                                witness.append(&mut generate_rlp_row_witness_new(
                                    tx_id,
                                    self,
                                    &bytes[..1],
                                    r,
                                    rlp_remain_length,
                                    None,
                                ));
                                (next_state, Some(1))
                            }
                            0x81..=0x88 => {
                                let mut offset = 1;
                                let len_of_val = head_byte0 - 0x80;
                                let res = read_nbytes(&bytes[offset..], len_of_val as usize);
                                match res {
                                    Ok(val_bytes_read) => {
                                        let val_byte0 = val_bytes_read[0];
                                        if len_of_val == 1 && val_byte0 < 0x80 {
                                            witness.append(&mut generate_rlp_row_witness_new(
                                                tx_id,
                                                self,
                                                &bytes[..offset + 1],
                                                r,
                                                rlp_remain_length,
                                                Some(RlpDecodeErrorType::LenOfLenError), // maybe val error is better
                                            ));
                                            (RlpTxFieldTag::DecodeError, Some(offset + 1))
                                        } else if len_of_val > 1 && val_byte0 == 0 {
                                            witness.append(&mut generate_rlp_row_witness_new(
                                                tx_id,
                                                self,
                                                &bytes[..offset + 1],
                                                r,
                                                rlp_remain_length,
                                                Some(RlpDecodeErrorType::LenOfLenError),
                                            ));
                                            (RlpTxFieldTag::DecodeError, Some(offset + 1))
                                        } else {
                                            offset += val_bytes_read.len();
                                            witness.append(&mut generate_rlp_row_witness_new(
                                                tx_id,
                                                self,
                                                &bytes[..offset],
                                                r,
                                                rlp_remain_length,
                                                None,
                                            ));
                                            (next_state, Some(offset))
                                        }
                                    }
                                    Err(val_bytes_read) => {
                                        offset += val_bytes_read.len();
                                        witness.append(&mut generate_rlp_row_witness_new(
                                            tx_id,
                                            self,
                                            &bytes[..offset],
                                            r,
                                            rlp_remain_length,
                                            Some(RlpDecodeErrorType::RunOutOfDataError),
                                        ));
                                        (RlpTxFieldTag::DecodeError, Some(offset))
                                    }
                                }
                            }
                            _ => unreachable!(),
                        },
                        RlpDecodeRule::Uint256 => match head_byte0 {
                            1..=0x80 => {
                                witness.append(&mut generate_rlp_row_witness_new(
                                    tx_id,
                                    self,
                                    &bytes[..1],
                                    r,
                                    rlp_remain_length,
                                    None,
                                ));
                                (next_state, Some(1))
                            }
                            0x81..=0xa0 => {
                                let mut offset = 1;
                                let len_of_val = head_byte0 - 0x80;
                                let res = read_nbytes(&bytes[offset..], len_of_val as usize);
                                match res {
                                    Ok(val_bytes_read) => {
                                        let val_byte0 = val_bytes_read[0];
                                        if len_of_val == 1 && val_byte0 <= 0x80 {
                                            witness.append(&mut generate_rlp_row_witness_new(
                                                tx_id,
                                                self,
                                                &bytes[..offset + 1],
                                                r,
                                                rlp_remain_length,
                                                Some(RlpDecodeErrorType::LenOfLenError),
                                            ));
                                            (RlpTxFieldTag::DecodeError, Some(offset + 1))
                                        } else if len_of_val > 1 && val_byte0 == 0 {
                                            witness.append(&mut generate_rlp_row_witness_new(
                                                tx_id,
                                                self,
                                                &bytes[..offset + 1],
                                                r,
                                                rlp_remain_length,
                                                Some(RlpDecodeErrorType::LenOfLenError),
                                            ));
                                            (RlpTxFieldTag::DecodeError, Some(offset + 1))
                                        } else {
                                            offset += val_bytes_read.len();
                                            witness.append(&mut generate_rlp_row_witness_new(
                                                tx_id,
                                                self,
                                                &bytes[..offset],
                                                r,
                                                rlp_remain_length,
                                                None,
                                            ));
                                            (next_state, Some(offset))
                                        }
                                    }
                                    Err(val_bytes_read) => {
                                        offset += val_bytes_read.len();
                                        witness.append(&mut generate_rlp_row_witness_new(
                                            tx_id,
                                            self,
                                            &bytes[..offset],
                                            r,
                                            rlp_remain_length,
                                            Some(RlpDecodeErrorType::RunOutOfDataError),
                                        ));
                                        (RlpTxFieldTag::DecodeError, Some(offset))
                                    }
                                }
                            }
                            _ => unreachable!(),
                        },
                        RlpDecodeRule::Address => match head_byte0 {
                            0x94 => {
                                let mut offset = 1;
                                let len_of_val = 0x14;
                                let res = read_nbytes(&bytes[offset..], len_of_val as usize);
                                match res {
                                    Ok(val_bytes_read) => {
                                        offset += val_bytes_read.len();
                                        witness.append(&mut generate_rlp_row_witness_new(
                                            tx_id,
                                            self,
                                            &bytes[..offset],
                                            r,
                                            rlp_remain_length,
                                            None,
                                        ));
                                        (next_state, Some(offset))
                                    }
                                    Err(val_bytes_read) => {
                                        offset += val_bytes_read.len();
                                        witness.append(&mut generate_rlp_row_witness_new(
                                            tx_id,
                                            self,
                                            &bytes[..offset],
                                            r,
                                            rlp_remain_length,
                                            Some(RlpDecodeErrorType::RunOutOfDataError),
                                        ));
                                        (RlpTxFieldTag::DecodeError, Some(offset))
                                    }
                                }
                            }
                            _ => unreachable!(),
                        },
                        RlpDecodeRule::Bytes48K => match head_byte0 {
                            0..=0x80 => {
                                witness.append(&mut generate_rlp_row_witness_new(
                                    tx_id,
                                    self,
                                    &bytes[..1],
                                    r,
                                    rlp_remain_length,
                                    None,
                                ));
                                (next_state, Some(1))
                            }
                            0x81..=0xb7 => {
                                let mut offset = 1;
                                let len_of_val = head_byte0 - 0x80;
                                let res = read_nbytes(&bytes[offset..], len_of_val as usize);
                                match res {
                                    Ok(val_bytes_read) => {
                                        let val_byte0 = val_bytes_read[0];
                                        if len_of_val == 1 && val_byte0 < 0x80 {
                                            offset += 1;
                                            witness.append(&mut generate_rlp_row_witness_new(
                                                tx_id,
                                                self,
                                                &bytes[..offset],
                                                r,
                                                rlp_remain_length,
                                                Some(RlpDecodeErrorType::LenOfLenError),
                                            ));
                                            (RlpTxFieldTag::DecodeError, Some(offset))
                                        } else {
                                            offset += len_of_val as usize;
                                            witness.append(&mut generate_rlp_row_witness_new(
                                                tx_id,
                                                self,
                                                &bytes[..offset],
                                                r,
                                                rlp_remain_length,
                                                None,
                                            ));
                                            (next_state, Some(offset))
                                        }
                                    }
                                    Err(val_bytes_read) => {
                                        let bytes_len = (val_bytes_read.len() + offset)
                                            .min(MAX_BYTE_COLUMN_NUM);
                                        witness.append(&mut generate_rlp_row_witness_new(
                                            tx_id,
                                            self,
                                            &bytes[..bytes_len],
                                            r,
                                            rlp_remain_length,
                                            Some(RlpDecodeErrorType::RunOutOfDataError),
                                        ));
                                        (
                                            RlpTxFieldTag::DecodeError,
                                            Some(offset + val_bytes_read.len()),
                                        )
                                    }
                                }
                            }
                            0xb8..=0xba => {
                                let mut offset = 1;
                                let len_of_len = head_byte0 - 0xb7;
                                let res = read_nbytes(&bytes[offset..], len_of_len as usize);
                                match res {
                                    Ok(len_bytes_read) => {
                                        let len_byte0 = len_bytes_read[0];
                                        if len_of_len == 1 && len_byte0 <= 55 {
                                            offset += 1;
                                            witness.append(&mut generate_rlp_row_witness_new(
                                                tx_id,
                                                self,
                                                &bytes[..offset],
                                                r,
                                                rlp_remain_length,
                                                Some(RlpDecodeErrorType::LenOfLenError),
                                            ));
                                            (RlpTxFieldTag::DecodeError, Some(offset))
                                        } else if len_of_len > 1 && len_byte0 == 0 {
                                            offset += 1;
                                            witness.append(&mut generate_rlp_row_witness_new(
                                                tx_id,
                                                self,
                                                &bytes[..offset],
                                                r,
                                                rlp_remain_length,
                                                Some(RlpDecodeErrorType::LenOfLenError),
                                            ));
                                            (RlpTxFieldTag::DecodeError, Some(offset))
                                        } else {
                                            offset += len_bytes_read.len();
                                            let val_bytes_len = rlp_bytes_len(len_bytes_read);
                                            let res = read_nbytes(&bytes[offset..], val_bytes_len);
                                            match res {
                                                Ok(val_bytes_read) => {
                                                    offset += val_bytes_read.len();
                                                    witness.append(
                                                        &mut generate_rlp_row_witness_new(
                                                            tx_id,
                                                            self,
                                                            &bytes[..offset],
                                                            r,
                                                            rlp_remain_length,
                                                            None,
                                                        ),
                                                    );
                                                    (next_state, Some(offset))
                                                }
                                                Err(val_bytes_read) => {
                                                    let bytes_len = (offset + val_bytes_read.len())
                                                        .min(MAX_BYTE_COLUMN_NUM);
                                                    witness
                                                        .append(&mut generate_rlp_row_witness_new(
                                                        tx_id,
                                                        self,
                                                        &bytes[..bytes_len],
                                                        r,
                                                        rlp_remain_length,
                                                        Some(RlpDecodeErrorType::RunOutOfDataError),
                                                    ));
                                                    (RlpTxFieldTag::DecodeError, Some(bytes_len))
                                                }
                                            }
                                        }
                                    }
                                    Err(len_bytes_read) => {
                                        offset += len_bytes_read.len();
                                        witness.append(&mut generate_rlp_row_witness_new(
                                            tx_id,
                                            self,
                                            &bytes[..offset],
                                            r,
                                            rlp_remain_length,
                                            Some(RlpDecodeErrorType::RunOutOfDataError),
                                        ));
                                        (RlpTxFieldTag::DecodeError, Some(offset))
                                    }
                                }
                            }
                            _ => unreachable!(),
                        },
                        RlpDecodeRule::EmptyList => todo!(),
                        RlpDecodeRule::LongList => {
                            let header_byte0 = bytes_read_header[0];
                            // if decode rule check failed
                            let (_, decodable) = decode_rule.rule_check(header_byte0);
                            if !decodable {
                                witness.append(&mut generate_rlp_row_witness_new(
                                    tx_id,
                                    self,
                                    &bytes[..1],
                                    r,
                                    rlp_remain_length,
                                    Some(RlpDecodeErrorType::HeaderDecError),
                                ));
                                (RlpTxFieldTag::DecodeError, Some(1))
                            } else {
                                let mut offset = 1;
                                let len_of_len = header_byte0 - 0xF7;
                                let res = read_nbytes(&bytes[offset..], len_of_len as usize);
                                match res {
                                    Ok(len_bytes_read) => {
                                        let len_byte0 = len_bytes_read[0];
                                        if len_of_len == 1 && len_byte0 <= 55 {
                                            offset += 1;
                                            witness.append(&mut generate_rlp_row_witness_new(
                                                tx_id,
                                                self,
                                                &bytes[..offset],
                                                r,
                                                rlp_remain_length,
                                                Some(RlpDecodeErrorType::LenOfLenError),
                                            ));
                                            (RlpTxFieldTag::DecodeError, Some(offset))
                                        } else if len_of_len > 1 && len_byte0 == 0 {
                                            offset += 1;
                                            witness.append(&mut generate_rlp_row_witness_new(
                                                tx_id,
                                                self,
                                                &bytes[..offset],
                                                r,
                                                rlp_remain_length,
                                                Some(RlpDecodeErrorType::LenOfLenError),
                                            ));
                                            (RlpTxFieldTag::DecodeError, Some(offset))
                                        } else {
                                            // TODO: consume rlp_bytes_len(consumed_bytes) and get
                                            // EOF error earlier?
                                            offset += len_bytes_read.len();
                                            witness.append(&mut generate_rlp_row_witness_new(
                                                tx_id,
                                                self,
                                                &bytes[..offset],
                                                r,
                                                rlp_remain_length,
                                                None,
                                            ));
                                            (next_state, Some(offset))
                                        }
                                    }
                                    Err(consumed_bytes) => {
                                        offset += consumed_bytes.len();
                                        (RlpTxFieldTag::DecodeError, Some(offset))
                                    }
                                }
                            }
                        }
                    }
                }
            }
            Err(_) => {
                // error flag row
                witness.append(&mut generate_rlp_row_witness_new(
                    tx_id,
                    self,
                    &bytes,
                    r,
                    rlp_remain_length,
                    Some(RlpDecodeErrorType::RunOutOfDataError),
                ));
                (RlpTxFieldTag::DecodeError, Some(0))
            }
        }
    }
}

fn gen_rlp_decode_state_witness<F: Field>(
    bytes: &[u8],
    r: F,
    k: usize,
) -> Vec<RlpDecoderCircuitConfigWitness<F>> {
    let mut tx_id: u64 = 0;

    // update the rlp bytes hash
    let mut hasher = Keccak::default();
    hasher.update(bytes);
    let hash = hasher.digest();

    let mut witness = vec![RlpDecoderCircuitConfigWitness::<F> {
        rlp_remain_length: bytes.len(),
        value: rlc::value(hash.iter().rev(), r),
        // acc_rlc_value: rlc::value(bytes.iter().rev(), r),
        ..Default::default()
    }];

    let mut offset = 0;
    let mut init_state = RlpTxFieldTag::TxListRlpHeader;

    loop {
        // println!("Current state: {:?}, offset = {:?}", init_state, offset);
        let (next_state, next_offset) =
            init_state.next(k, tx_id, &bytes[offset..], r, &mut witness);
        if next_state == RlpTxFieldTag::TxRlpHeader {
            tx_id += 1;
        }
        match next_offset {
            Some(n) => {
                offset += n;
                init_state = next_state;
            }
            None => {
                break;
            }
        }
    }
    witness
}

fn fixup_acc_rlc_new<F: Field>(
    witness: &mut Vec<RlpDecoderCircuitConfigWitness<F>>,
    randomness: F,
) {
    let mut prev_acc_rlc = F::zero();
    // skip the first line
    for i in 1..witness.len() {
        let cur_wit = &mut witness[i];
        let mut bytes = cur_wit.bytes.clone();
        bytes.resize(MAX_BYTE_COLUMN_NUM, 0);
        bytes.reverse();
        cur_wit.rlc_quotient =
            rlc::value(&bytes, randomness) * cur_wit.r_mult_comp.invert().unwrap();
        cur_wit.acc_rlc_value = prev_acc_rlc * cur_wit.r_mult + cur_wit.rlc_quotient;
        prev_acc_rlc = cur_wit.acc_rlc_value;
    }
}

fn complete_paddings_new<F: Field>(
    witness: &mut Vec<RlpDecoderCircuitConfigWitness<F>>,
    randomness: F,
    num_padding_to_last_row: usize,
) {
    let before_padding = witness.last().unwrap().clone();
    let r_mult_comp_padding = randomness.pow(&[(MAX_BYTE_COLUMN_NUM) as u64, 0, 0, 0]);
    for i in 0..num_padding_to_last_row {
        witness.push(RlpDecoderCircuitConfigWitness::<F> {
            tx_id: 0,
            tx_type: RlpTxTypeTag::TxLegacyType,
            tx_member: RlpTxFieldTag::Padding,
            complete: true,
            rlp_type: RlpDecodeTypeTag::DoNothing,
            rlp_tx_member_length: 0,
            rlp_bytes_in_row: 0,
            r_mult: F::one(),
            rlp_remain_length: 0,
            value: F::zero(),
            acc_rlc_value: before_padding.acc_rlc_value,
            bytes: [0; MAX_BYTE_COLUMN_NUM].to_vec(),
            errors: before_padding.errors,
            valid: before_padding.valid,
            q_enable: true,
            q_first: false,
            q_last: i == num_padding_to_last_row - 1,
            r_mult_comp: r_mult_comp_padding,
            rlc_quotient: F::zero(),
        });
    }
    witness.push(RlpDecoderCircuitConfigWitness::<F>::default());
}

fn generate_rlp_row_witness_new<F: Field>(
    tx_id: u64,
    tx_member: &RlpTxFieldTag,
    raw_bytes: &[u8],
    r: F,
    rlp_remain_length: usize,
    error_id: Option<RlpDecodeErrorType>,
) -> Vec<RlpDecoderCircuitConfigWitness<F>> {
    log::trace!("generate witness for (tx_id: {}, tx_member: {:?}, raw_bytes: {:?}, r: {:?}, rlp_remain_length: {:?}, error_id: {:?})",
                tx_id, tx_member, raw_bytes, r, rlp_remain_length, error_id);
    let mut witness = vec![];
    let (mut rlp_type, _, _, _) = generate_rlp_type_witness(tx_member, raw_bytes);
    let partial_rlp_type = RlpDecodeTypeTag::PartialRlp;
    let rlp_tag_len = raw_bytes.len();
    let mut prev_rlp_remain_length = rlp_remain_length;

    // error case never cross raw
    assert!(error_id.is_none() || (raw_bytes.len() <= MAX_BYTE_COLUMN_NUM));
    let mut errors = [false; 4];
    error_id.map(|id| errors[id as usize] = true);
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
                    errors: errors,
                    valid: (tx_member != &RlpTxFieldTag::DecodeError)
                        && errors.iter().all(|&err| !err),
                    q_enable: true,
                    q_first: false,
                    q_last: false,
                    r_mult_comp: F::one(),
                    rlc_quotient: F::zero(),
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
                errors: errors,
                valid: (tx_member != &RlpTxFieldTag::DecodeError) && errors.iter().all(|&err| !err),
                q_enable: true,
                q_first: tx_member == &RlpTxFieldTag::TxListRlpHeader,
                q_last: false,
                r_mult_comp: r.pow(&[(MAX_BYTE_COLUMN_NUM - tag_remain_length) as u64, 0, 0, 0]),
                rlc_quotient: F::zero(),
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
        RlpTxFieldTag::DecodeError => witness.append(&mut generate_witness!()),
        RlpTxFieldTag::Padding => {
            unreachable!("Padding should not be here")
        }
        _ => {
            unreachable!("1559 not support now")
        }
    }
    witness
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
    use super::{gen_rlp_decode_state_witness, SignedTransaction};
    use ethers_core::utils::rlp;
    use halo2_proofs::halo2curves::bn256::Fr;
    use hex;
    use keccak256::plain::Keccak;
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

        // let witness = rlp_decode_tx_list_manually::<Fr>(&rlp_bytes, randomness, k);
        // for (i, w) in witness.iter().enumerate() {
        //     print!("witness[{}] = {:?}\n", i, w);
        // }

        let witness: Vec<super::RlpDecoderCircuitConfigWitness<Fr>> =
            gen_rlp_decode_state_witness::<Fr>(&rlp_bytes, randomness, k);
        for (i, w) in witness.iter().enumerate() {
            print!("witness[{}] = {:?}\n", i, w);
        }
    }

    #[test]
    fn test_correct_witness_generation_1tx() {
        let rlp_bytes = prepare_legacy_txlist_rlp_bytes(1);
        let randomness = Fr::from(100);
        let k = 128;

        let witness: Vec<super::RlpDecoderCircuitConfigWitness<Fr>> =
            gen_rlp_decode_state_witness::<Fr>(&rlp_bytes, randomness, k);
        for (i, w) in witness.iter().enumerate() {
            print!("witness[{}] = {:?}\n", i, w);
        }
    }

    #[test]
    fn test_correct_witness_generation_11tx() {
        let rlp_bytes = prepare_legacy_txlist_rlp_bytes(11);
        let randomness = Fr::from(100);
        let k = 256;

        let witness = gen_rlp_decode_state_witness::<Fr>(&rlp_bytes, randomness, k as usize);
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
        println!("tx = {:?}", tx);

        let rlp_txs = rlp::encode_list(&[tx]);
        println!("rlp_txs = {:?}", hex::encode(rlp_txs.clone()));
        let randomness = Fr::from(100);
        let k = 256;

        let rlp_bytes = rlp_txs.to_vec();
        let witness = gen_rlp_decode_state_witness::<Fr>(&rlp_bytes, randomness, k as usize);
        for (i, w) in witness.iter().enumerate() {
            print!("witness[{}] = {:?}\n", i, w);
        }
    }

    #[test]
    fn test_keccak() {
        let tx: SignedTransaction = mock::CORRECT_MOCK_TXS[0].clone().into();
        let rlp_txs = rlp::encode_list(&[tx]);
        println!("rlp_txs = {:?}", hex::encode(rlp_txs.clone()));
        // update the rlp bytes hash
        let mut hasher = Keccak::default();
        hasher.update(&rlp_txs.to_vec());
        let hash = hasher.digest();
        println!("hash = {:?}", hex::encode(&hash));

        let rlc = hash.iter().fold(Fr::zero(), |acc, b| {
            acc * Fr::from(11 as u64) + Fr::from(*b as u64)
        });
        println!("rlc = {:?}", rlc);
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

    mod invalid_rlp_test {
        use super::*;
        use pretty_assertions::assert_eq;

        /// predefined tx bytes
        /// "f8 50"        // witness[1]: list header
        /// "f8 4e"        // witness[2]: tx header
        /// "80"           // witness[3]: nonce
        /// "01"           // witness[4]: gas_price
        /// "83 0f4240"    // witness[5]: gas
        /// "80"           // witness[6]: to
        /// "80"           // witness[7]: value
        /// "82 3031"      // witness[8]: input
        /// "82 0a98"      // witness[9]: v
        /// "a0 b05805737618f6ac1ef211c02575f2fa82026fa1742caf192e2cffcd4161adca"  // witness[10]: r
        /// "a0 53fbe3d9957dffafca84c419fdd1cead150834c5de9f3215c66327123c0a0541"  // witness[11]: s
        fn const_tx_hex() -> String {
            String::from("f852")
                + "f850"
                + "80"
                + "01"
                + "830f4240"
                + "80"
                + "80"
                + "823031"
                + "820a98"
                + "a0b05805737618f6ac1ef211c02575f2fa82026fa1742caf192e2cffcd4161adca"
                + "a053fbe3d9957dffafca84c419fdd1cead150834c5de9f3215c66327123c0a0541"
        }

        fn generate_rlp_bytes(txs: Vec<Transaction>) -> Vec<u8> {
            let k = log2_ceil(RlpDecoderCircuit::<Fr>::min_num_rows_from_tx(&txs).0);

            let encodable_txs: Vec<SignedTransaction> =
                txs.iter().map(|tx| tx.into()).collect::<Vec<_>>();
            let rlp_bytes = rlp::encode_list(&encodable_txs);
            println!(
                "input rlp_bytes = {:?}, k = {}.",
                hex::encode(&rlp_bytes),
                k
            );
            rlp_bytes.to_vec()
        }

        fn run_invalid_rlp<F: Field>(
            rlp_bytes: Vec<u8>,
            k: usize,
        ) -> Result<(), Vec<VerifyFailure>> {
            let circuit = RlpDecoderCircuit::<F>::new(rlp_bytes, k);
            let prover = match MockProver::run(k as u32, &circuit, vec![]) {
                Ok(prover) => prover,
                Err(e) => panic!("{:#?}", e),
            };
            prover.verify()
        }

        #[test]
        fn const_tx_decode_is_ok() {
            let k = 12;
            let rlp_bytes = hex::decode(const_tx_hex()).unwrap();
            let witness = gen_rlp_decode_state_witness(&rlp_bytes, Fr::one(), 1 << k);
            // println!("witness = {:?}", &witness);
            assert_eq!(witness[witness.len() - 2].valid, true);
            assert_eq!(run_invalid_rlp::<Fr>(rlp_bytes, k), Ok(()));
        }

        #[test]
        fn invalid_rlp_wrong_list_header_header() {
            let mut rlp_bytes = hex::decode(const_tx_hex()).unwrap();
            rlp_bytes[0] = 0xc0;

            let k = 12;
            let witness = gen_rlp_decode_state_witness(&rlp_bytes, Fr::one(), 1 << k);
            assert_eq!(witness[1].valid, false);
            assert_eq!(witness[witness.len() - 2].valid, false);

            assert_eq!(run_invalid_rlp::<Fr>(rlp_bytes, k), Ok(()));
        }

        #[test]
        fn invalid_rlp_wrong_list_header_len() {
            let mut rlp_bytes = hex::decode(const_tx_hex()).unwrap();
            rlp_bytes[1] = 0x00;

            let k = 12;
            let witness = gen_rlp_decode_state_witness(&rlp_bytes, Fr::one(), 1 << k);
            assert_eq!(witness[1].valid, false);
            assert_eq!(witness[witness.len() - 2].valid, false);

            assert_eq!(run_invalid_rlp::<Fr>(rlp_bytes, k), Ok(()));
        }

        #[test]
        fn invalid_rlp_wrong_tx_header_header() {
            let mut rlp_bytes = hex::decode(&const_tx_hex()).unwrap();
            rlp_bytes[2] = 0xf5;

            let k = 12;
            let witness = gen_rlp_decode_state_witness(&rlp_bytes, Fr::one(), 1 << k);
            assert_eq!(witness[1].valid, true);
            assert_eq!(witness[2].valid, false);
            assert_eq!(witness[witness.len() - 2].valid, false);

            assert_eq!(run_invalid_rlp::<Fr>(rlp_bytes, k), Ok(()));
        }

        #[test]
        fn invalid_rlp_wrong_tx_header_len() {
            let mut rlp_bytes = hex::decode(&const_tx_hex()).unwrap();
            rlp_bytes[3] = 0x00;

            let k = 12;
            let witness = gen_rlp_decode_state_witness(&rlp_bytes, Fr::one(), 1 << k);
            assert_eq!(witness[witness.len() - 2].valid, false);

            assert_eq!(run_invalid_rlp::<Fr>(rlp_bytes, k), Ok(()));
        }

        #[test]
        fn invalid_rlp_wrong_tx_field_nonce() {
            let mut rlp_bytes = hex::decode(&const_tx_hex()).unwrap();
            rlp_bytes[4] = 0x00;

            let k = 12;
            let witness = gen_rlp_decode_state_witness(&rlp_bytes, Fr::one(), 1 << k);
            assert_eq!(witness[2].valid, true);
            assert_eq!(witness[3].valid, false);
            assert_eq!(witness[witness.len() - 2].valid, false);

            assert_eq!(run_invalid_rlp::<Fr>(rlp_bytes, k), Ok(()));
        }

        #[test]
        fn invalid_rlp_wrong_tx_field_gas() {
            let mut rlp_bytes = hex::decode(&const_tx_hex()).unwrap();
            rlp_bytes[5] = 0x00;

            let k = 12;
            let witness = gen_rlp_decode_state_witness(&rlp_bytes, Fr::one(), 1 << k);
            assert_eq!(witness[3].valid, true);
            assert_eq!(witness[4].valid, false);
            assert_eq!(witness[witness.len() - 2].valid, false);

            assert_eq!(run_invalid_rlp::<Fr>(rlp_bytes, k), Ok(()));
        }

        #[test]
        fn invalid_rlp_wrong_tx_field_to() {
            let mut rlp_bytes = hex::decode(&const_tx_hex()).unwrap();
            rlp_bytes[10] = 0x00;

            let k = 12;
            let witness = gen_rlp_decode_state_witness(&rlp_bytes, Fr::one(), 1 << k);
            assert_eq!(witness[5].valid, true);
            assert_eq!(witness[6].valid, false);
            assert_eq!(witness[witness.len() - 2].valid, false);

            assert_eq!(run_invalid_rlp::<Fr>(rlp_bytes, k), Ok(()));
        }

        #[test]
        fn invalid_rlp_wrong_tx_field_data() {
            let mut rlp_bytes = hex::decode(&const_tx_hex()).unwrap();
            rlp_bytes[12] = 0x81;
            rlp_bytes[13] = 0x02;

            let k = 12;
            let witness = gen_rlp_decode_state_witness(&rlp_bytes, Fr::one(), 1 << k);
            assert_eq!(witness[7].valid, true);
            assert_eq!(witness[8].valid, false);
            assert_eq!(witness[witness.len() - 2].valid, false);

            assert_eq!(run_invalid_rlp::<Fr>(rlp_bytes, k), Ok(()));
        }

        #[test]
        fn invalid_rlp_not_enough_length() {
            todo!()
        }
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
