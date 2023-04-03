//! Circuit implementation for RLP-encoding verification. Please refer: <https://hackmd.io/@rohitnarurkar/S1zSz0KM9>.

use std::marker::PhantomData;

use bus_mapping::circuit_input_builder::get_dummy_tx_hash;
use eth_types::Field;
use ethers_core::utils::rlp;
use gadgets::binary_number::{BinaryNumberChip, BinaryNumberConfig};
use gadgets::is_equal::{IsEqualChip, IsEqualConfig, IsEqualInstruction};
use gadgets::util::{select, sum};
use gadgets::{
    comparator::{ComparatorChip, ComparatorConfig, ComparatorInstruction},
    less_than::{LtChip, LtConfig, LtInstruction},
};

#[cfg(feature = "onephase")]
use halo2_proofs::plonk::FirstPhase as SecondPhase;
#[cfg(not(feature = "onephase"))]
use halo2_proofs::plonk::SecondPhase;

use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};

// use crate::evm_circuit::table::FixedTableTag;
use crate::util::{Challenges, SubCircuit, SubCircuitConfig};
use crate::witness::RlpTxTag::{
    ChainId, DataPrefix, Gas, GasPrice, Nonce, SigR, SigS, SigV, To, TxPrefix,
};
use crate::witness::{Block, Transaction};
use crate::{
    evm_circuit::{
        util::{and, constraint_builder::BaseConstraintBuilder, not, or},
        witness::{RlpTxTag, RlpWitnessGen},
    },
    table::RlpTable,
    util::Expr,
    witness::{RlpDataType, SignedTransaction},
};

/// rlp witness byte
#[derive(Clone, Copy, Debug)]
pub struct RlpWitnessByte {
    /// pure byte with place holder byte 00
    pub witness_byte: u8,
    /// indicate the byte is place holder or not
    pub place_holder: bool,
}

#[derive(Clone, Debug)]
struct RlpTagROM {
    // TODO: we can merge these three cols into one col using LC as
    //       as their type are (u8, u8, u8, u8)
    rlp_valid: Column<Fixed>,
    tag: Column<Fixed>,
    tag_next: Column<Fixed>,
    max_length: Column<Fixed>,
}

#[derive(Clone, Debug)]
/// Config for the RLP circuit.
pub struct RlpCircuitConfig<F> {
    minimum_rows: usize,
    /// Denotes whether or not the row is enabled.
    q_usable: Column<Fixed>,
    /// Denotes whether the row is the first row in the layout.
    is_first: Column<Advice>,
    /// Denotes whether the row is the last byte in the RLP-encoded data.
    is_last: Column<Advice>,
    /// Embedded lookup table in RLP circuit.
    rlp_table: RlpTable,
    /// Denotes the index of this row, starting from `1` and ending at `n`
    /// where `n` is the byte length of the RLP-encoded data.
    index: Column<Advice>,
    /// Denotes the index of this row, but reversed. It starts from `n` where
    /// `n` is the byte length of the RLP-encoded data and ends at `1`.
    rindex: Column<Advice>,
    /// Placeholder row do not increase the index and mainly used for
    /// DataPrefix when |tx.data| = 1 and tx.data < 0x80.
    placeholder: Column<Advice>,
    /// Denotes the byte value at this row index depends on rlp valid or not.
    byte_value: Column<Advice>,
    /// Denotes whether or not the row is for decode logic.
    /// TODO: combine with q_usable and make advice column
    q_decode_usable: Column<Fixed>,
    /// Denotes if tag is Rlp Array Prefix, which is for begining decode only.
    /// TODO: combine with is_prefix_tag
    is_decode_prefix_tag: Column<Fixed>,
    /// Denotes if the original rlp-encoded data is valid.
    rlp_valid: Column<Advice>,
    /// Denotes the byte value at this row index from the original RLP-encoded
    /// data.
    input_byte_value: Column<Advice>,
    /// Denotes an accumulator for the byte value field over all input (bytes).
    /// TODO: combine with the all_bytes_rlc_acc
    input_bytes_rlc_acc: Column<Advice>,
    /// Denotes the bytes left, i.e., the r-index of the total input.
    input_bytes_left: Column<Advice>,
    /// Denotes whether the decoding is ended, i.e., continously 1 from the
    /// first padding row, otherwise 0. TODO: advice column
    q_end: Column<Fixed>,
    /// Denotes the RLC accumulator value used for call data bytes.
    calldata_bytes_rlc_acc: Column<Advice>,
    /// Tag bits
    tag_bits: BinaryNumberConfig<RlpTxTag, 4>,
    /// Tag ROM
    tag_rom: RlpTagROM,
    /// Denotes the current tag's span in bytes.
    tag_length: Column<Advice>,
    /// Denotes an accumulator for the length of data, in the case where len >
    /// 55 and the length is represented in its big-endian form.
    length_acc: Column<Advice>,
    /// Denotes an accumulator for the byte value field over all rows (bytes).
    all_bytes_rlc_acc: Column<Advice>,
    /// Denotes if tag is simple
    /// (the one that tag_bits provides has degree 4, which is too large)
    is_simple_tag: Column<Advice>,
    /// Denotes if tag is Prefix
    is_prefix_tag: Column<Advice>,
    /// Denotes if tag is DataPrefix
    is_dp_tag: Column<Advice>,
    /// Comparison chip to check: 1 <= tag_index.
    tag_index_cmp_1: ComparatorConfig<F, 3>,
    /// Comparison chip to check: tag_index <= tag_length.
    tag_index_length_cmp: ComparatorConfig<F, 3>,
    /// Comparison chip to check: 1 <= tag_length.
    tag_length_cmp_1: ComparatorConfig<F, 3>,
    /// Lt chip to check: tag_index < 10.
    tag_index_lt_10: LtConfig<F, 3>,
    /// Lt chip to check: tag_index < 34.
    tag_index_lt_34: LtConfig<F, 3>,
    /// Lt chip to check: 127 < value.
    value_gt_127: LtConfig<F, 1>,
    /// Lt chip to check: 183 < value.
    value_gt_183: LtConfig<F, 1>,
    /// Lt chip to check: 191 < value.
    value_gt_191: LtConfig<F, 1>,
    /// Lt chip to check: 247 < value.
    value_gt_247: LtConfig<F, 1>,
    /// Lt chip to check: value < 129.
    value_lt_129: LtConfig<F, 1>,
    /// IsEq Chip to check: value == 128,
    value_eq_128: IsEqualConfig<F>,
    /// Lt chip to check: value < 184.
    value_lt_184: LtConfig<F, 1>,
    /// Lt chip to check: value < 192.
    value_lt_192: LtConfig<F, 1>,
    /// Lt chip to check: value < 248.
    value_lt_248: LtConfig<F, 1>,
    // for input bytes value check
    /// Lt chip to check: 127 < value.
    input_value_gt_127: LtConfig<F, 1>,
    /// Lt chip to check: 183 < value.
    input_value_gt_183: LtConfig<F, 1>,
    /// Lt chip to check: 191 < value.
    input_value_gt_191: LtConfig<F, 1>,
    /// Lt chip to check: 247 < value.
    input_value_gt_247: LtConfig<F, 1>,
    /// Lt chip to check: value < 129.
    input_value_lt_129: LtConfig<F, 1>,
    /// IsEq Chip to check: value == 128,
    input_value_eq_128: IsEqualConfig<F>,
    /// Lt chip to check: value < 184.
    input_value_lt_184: LtConfig<F, 1>,
    /// Lt chip to check: value < 192.
    input_value_lt_192: LtConfig<F, 1>,
    /// Lt chip to check: value < 248.
    input_value_lt_248: LtConfig<F, 1>,

    /// Comparison chip to check: 0 <= length_acc.
    length_acc_cmp_0: ComparatorConfig<F, 3>,
}

impl<F: Field> RlpCircuitConfig<F> {
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        rlp_table: &RlpTable,
        challenges: &Challenges<Expression<F>>,
    ) -> Self {
        let q_usable = meta.fixed_column();
        let is_first = meta.advice_column();
        let is_last = meta.advice_column();
        let index = meta.advice_column();
        let rindex = meta.advice_column();
        let placeholder = meta.advice_column();
        let byte_value = meta.advice_column();
        let q_decode_usable = meta.fixed_column();
        let is_decode_prefix_tag = meta.fixed_column();
        let rlp_valid = meta.advice_column();
        let input_byte_value = meta.advice_column();
        let input_bytes_rlc_acc = meta.advice_column_in(SecondPhase);
        let input_bytes_left = meta.advice_column();
        let q_end = meta.fixed_column();
        let calldata_bytes_rlc_acc = meta.advice_column_in(SecondPhase);
        let tag_length = meta.advice_column();
        let length_acc = meta.advice_column();
        let all_bytes_rlc_acc = meta.advice_column_in(SecondPhase);
        let evm_word_rand = challenges.evm_word();
        let keccak_input_rand = challenges.keccak_input();
        // these three columns are used to replace the degree-4 expressions with
        // degree-1 expressions
        let is_simple_tag = meta.advice_column();
        let is_prefix_tag = meta.advice_column();
        let is_dp_tag = meta.advice_column();
        let tag_bits = BinaryNumberChip::configure(meta, q_usable, Some(rlp_table.tag));
        let tag_rom = RlpTagROM {
            rlp_valid: meta.fixed_column(),
            tag: meta.fixed_column(),
            tag_next: meta.fixed_column(),
            max_length: meta.fixed_column(),
        };

        macro_rules! debug_print {
            ($column:expr) => {
                log::debug!("locate {}: {:?}", stringify!($column), $column);
            };
        }

        debug_print!(&q_usable);
        debug_print!(&is_first);
        debug_print!(&is_last);
        debug_print!(&index);
        debug_print!(&rindex);
        debug_print!(&placeholder);
        debug_print!(&byte_value);
        debug_print!(&q_decode_usable);
        debug_print!(&is_decode_prefix_tag);
        debug_print!(&rlp_valid);
        debug_print!(&input_byte_value);
        debug_print!(&input_bytes_rlc_acc);
        debug_print!(&input_bytes_left);
        debug_print!(&q_end);
        debug_print!(&calldata_bytes_rlc_acc);
        debug_print!(&tag_length);
        debug_print!(&length_acc);
        debug_print!(&all_bytes_rlc_acc);
        debug_print!(&evm_word_rand);
        debug_print!(&keccak_input_rand);

        // Helper macro to declare booleans to check the current row tag.
        macro_rules! is_tx_tag {
            ($var:ident, $tag_variant:ident) => {
                let $var = |meta: &mut VirtualCells<F>| {
                    tag_bits.value_equals(RlpTxTag::$tag_variant, Rotation::cur())(meta)
                };
            };
        }
        is_tx_tag!(is_tx_list_prefix, TxListPrefix);
        is_tx_tag!(is_tx_prefix, TxPrefix);
        is_tx_tag!(is_nonce, Nonce);
        is_tx_tag!(is_gas_price, GasPrice);
        is_tx_tag!(is_gas, Gas);
        is_tx_tag!(is_to, To);
        is_tx_tag!(is_value, Value);
        is_tx_tag!(is_data_prefix, DataPrefix);
        is_tx_tag!(is_data, Data);
        is_tx_tag!(is_chainid, ChainId);
        is_tx_tag!(is_sig_v, SigV);
        is_tx_tag!(is_sig_r, SigR);
        is_tx_tag!(is_sig_s, SigS);
        is_tx_tag!(is_padding, Padding);

        // Enable the comparator and lt chips if the current row is enabled.
        let cmp_lt_enabled = |meta: &mut VirtualCells<F>| {
            let q_usable = meta.query_fixed(q_usable, Rotation::cur());
            let is_padding = is_padding(meta);

            q_usable * not::expr(is_padding)
        };

        let tag_index_cmp_1 = ComparatorChip::configure(
            meta,
            cmp_lt_enabled,
            |_meta| 1.expr(),
            |meta| meta.query_advice(rlp_table.tag_rindex, Rotation::cur()),
        );
        let tag_index_length_cmp = ComparatorChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(rlp_table.tag_rindex, Rotation::cur()),
            |meta| meta.query_advice(tag_length, Rotation::cur()),
        );
        let tag_length_cmp_1 = ComparatorChip::configure(
            meta,
            cmp_lt_enabled,
            |_meta| 1.expr(),
            |meta| meta.query_advice(tag_length, Rotation::cur()),
        );
        let tag_index_lt_10 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(rlp_table.tag_rindex, Rotation::cur()),
            |_meta| 10.expr(),
        );
        let tag_index_lt_34 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(rlp_table.tag_rindex, Rotation::cur()),
            |_meta| 34.expr(),
        );
        let value_gt_127 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |_meta| 127.expr(),
            |meta| meta.query_advice(byte_value, Rotation::cur()),
        );
        let value_gt_183 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |_meta| 183.expr(),
            |meta| meta.query_advice(byte_value, Rotation::cur()),
        );
        let value_gt_191 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |_meta| 191.expr(),
            |meta| meta.query_advice(byte_value, Rotation::cur()),
        );
        let value_gt_247 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |_meta| 247.expr(),
            |meta| meta.query_advice(byte_value, Rotation::cur()),
        );
        let value_lt_129 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(byte_value, Rotation::cur()),
            |_meta| 129.expr(),
        );
        let value_eq_128 = IsEqualChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(byte_value, Rotation::cur()),
            |_| 128.expr(),
        );
        let value_lt_184 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(byte_value, Rotation::cur()),
            |_meta| 184.expr(),
        );
        let value_lt_192 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(byte_value, Rotation::cur()),
            |_meta| 192.expr(),
        );
        let value_lt_248 = LtChip::configure(
            meta,
            cmp_lt_enabled,
            |meta| meta.query_advice(byte_value, Rotation::cur()),
            |_meta| 248.expr(),
        );
        let length_acc_cmp_0 = ComparatorChip::configure(
            meta,
            cmp_lt_enabled,
            |_meta| 0.expr(),
            |meta| meta.query_advice(length_acc, Rotation::cur()),
        );

        meta.create_gate("is_simple_tag", |meta| {
            let is_simple_tag = meta.query_advice(is_simple_tag, Rotation::cur());
            let is_prefix_tag = meta.query_advice(is_prefix_tag, Rotation::cur());
            let is_data_prefix_tag = meta.query_advice(is_dp_tag, Rotation::cur());
            let q_usable = meta.query_fixed(q_usable, Rotation::cur());
            let tags = sum::expr([
                is_nonce(meta),
                is_gas_price(meta),
                is_gas(meta),
                is_to(meta),
                is_value(meta),
                is_sig_v(meta),
                is_sig_r(meta),
                is_sig_s(meta),
                is_chainid(meta),
            ]);
            vec![
                q_usable.expr() * (is_simple_tag - tags),
                q_usable.expr() * (is_prefix_tag - is_tx_prefix(meta)),
                q_usable.expr() * (is_data_prefix_tag - is_data_prefix(meta)),
            ]
        });

        // TODO: add lookup for byte_value in the fixed byte table.

        meta.lookup_any("(tag, tag_next) in tag_ROM", |meta| {
            let is_simple_tag = meta.query_advice(is_simple_tag, Rotation::cur());
            let tag = meta.query_advice(rlp_table.tag, Rotation::cur());
            let tag_next = meta.query_advice(rlp_table.tag, Rotation::next());
            let rom_tag = meta.query_fixed(tag_rom.tag, Rotation::cur());
            let rom_tag_next = meta.query_fixed(tag_rom.tag_next, Rotation::cur());
            let q_usable = meta.query_fixed(q_usable, Rotation::cur());
            let (_, tag_idx_eq_one) = tag_index_cmp_1.expr(meta, None);
            let condition = q_usable * is_simple_tag * tag_idx_eq_one;

            vec![
                (condition.expr() * tag, rom_tag),
                (condition * tag_next, rom_tag_next),
            ]
        });

        meta.create_gate("Common constraints", |meta| {
            let mut cb = BaseConstraintBuilder::new(9);

            let (tindex_lt, tindex_eq) = tag_index_cmp_1.expr(meta, None);
            assert_eq!(tindex_lt.degree(), 1, "{}", tindex_lt.degree());
            assert_eq!(tindex_eq.degree(), 2, "{}", tindex_lt.degree());
            let (tlength_lt, tlength_eq) = tag_length_cmp_1.expr(meta, None);
            let (tindex_lt_tlength, tindex_eq_tlength) = tag_index_length_cmp.expr(meta, None);
            let (length_acc_gt_0, length_acc_eq_0) = length_acc_cmp_0.expr(meta, None);
            let is_simple_tag = meta.query_advice(is_simple_tag, Rotation::cur());
            let is_prefix_tag = meta.query_advice(is_prefix_tag, Rotation::cur());
            let is_dp_tag = meta.query_advice(is_dp_tag, Rotation::cur());
            let is_tag_word = sum::expr([
                is_gas_price(meta),
                is_value(meta),
                is_sig_r(meta),
                is_sig_s(meta),
            ]);

            //////////////////////////////////////////////////////////////////////////////////////
            ////////////////////////////////// RlpTxTag::Prefix //////////////////////////////////
            //////////////////////////////////////////////////////////////////////////////////////
            cb.condition(is_prefix_tag.expr(), |cb| {
                // tag_index < 10
                cb.require_equal(
                    "tag_index < 10",
                    tag_index_lt_10.is_lt(meta, None),
                    1.expr(),
                );

                // tag_index >= 1
                cb.require_zero(
                    "tag_index >= 1",
                    not::expr(or::expr([tindex_lt.clone(), tindex_eq.clone()])),
                );
            });

            // if tag_index > 1
            cb.condition(is_prefix_tag.expr() * tindex_lt.clone(), |cb| {
                cb.require_equal(
                    "tag::next == RlpTxTag::Prefix",
                    meta.query_advice(rlp_table.tag, Rotation::next()),
                    RlpTxTag::TxPrefix.expr(),
                );
                cb.require_equal(
                    "tag_index::next == tag_index - 1",
                    meta.query_advice(rlp_table.tag_rindex, Rotation::next()),
                    meta.query_advice(rlp_table.tag_rindex, Rotation::cur()) - 1.expr(),
                );
                cb.require_equal(
                    "tag_length::next == tag_length",
                    meta.query_advice(tag_length, Rotation::next()),
                    meta.query_advice(tag_length, Rotation::cur()),
                );
            });

            // if tag_index == 1
            cb.condition(is_prefix_tag.expr() * tindex_eq.clone(), |cb| {
                cb.require_equal(
                    "tag::next == RlpTxTag::Nonce",
                    meta.query_advice(rlp_table.tag, Rotation::next()),
                    RlpTxTag::Nonce.expr(),
                );
                cb.require_equal(
                    "tag_index::next == tag_length::next",
                    meta.query_advice(rlp_table.tag_rindex, Rotation::next()),
                    meta.query_advice(tag_length, Rotation::next()),
                );
                // no more RlpLength & Rlp
                cb.require_equal(
                    "rindex::next == length_acc",
                    meta.query_advice(rindex, Rotation::next()),
                    meta.query_advice(length_acc, Rotation::cur()) - 1.expr(),
                );
            });

            // if tag_index == tag_length && tag_length > 1
            cb.condition(
                is_prefix_tag.expr() * tindex_eq_tlength.clone() * tlength_lt.clone(),
                |cb| {
                    cb.require_equal("247 < value", value_gt_247.is_lt(meta, None), 1.expr());
                    // cb.require_equal("value < 256", value_lt_256.is_lt(meta, None), 1.expr());
                    cb.require_equal(
                        "tag_index::next == value - 0xf7",
                        meta.query_advice(rlp_table.tag_rindex, Rotation::next()),
                        meta.query_advice(byte_value, Rotation::cur()) - 247.expr(),
                    );
                    cb.require_zero(
                        "length_acc == 0",
                        meta.query_advice(length_acc, Rotation::cur()),
                    );
                },
            );

            // if tag_index == tag_length && tag_length == 1
            cb.condition(
                is_prefix_tag.expr() * tindex_eq_tlength.clone() * tlength_eq.clone(),
                |cb| {
                    cb.require_equal("191 < value", value_gt_191.is_lt(meta, None), 1.expr());
                    cb.require_equal("value < 248", value_lt_248.is_lt(meta, None), 1.expr());
                    cb.require_equal(
                        "length_acc == value - 0xc0 (1)",
                        meta.query_advice(length_acc, Rotation::cur()),
                        meta.query_advice(byte_value, Rotation::cur()) - 192.expr(),
                    );
                },
            );

            // if tag_index < tag_length && tag_length > 1
            cb.condition(
                is_prefix_tag.expr() * tindex_lt_tlength.clone() * tlength_lt.clone(),
                |cb| {
                    cb.require_equal(
                        "length_acc == (length_acc::prev * 256) + value",
                        meta.query_advice(length_acc, Rotation::cur()),
                        meta.query_advice(length_acc, Rotation::prev()) * 256.expr()
                            + meta.query_advice(byte_value, Rotation::cur()),
                    );
                },
            );

            //////////////////////////////////////////////////////////////////////////////////////
            //////// RlpTxTag::Nonce, GasPrice, Gas, To, Value, ChainID, SigV, SigR, SigS ////////
            //////////////////////////////////////////////////////////////////////////////////////
            cb.condition(is_simple_tag.clone(), |cb| {
                // TODO: add tag_length < max_length

                // tag_index >= 1
                cb.require_zero(
                    "1 <= tag_index",
                    not::expr(or::expr([tindex_lt.clone(), tindex_eq.clone()])),
                );
            });

            // cb.require_equal(
            //     "interm == is_simple_tag "
            //     is_simple_tag.clone()
            // )
            cb.condition(
                is_simple_tag.clone(),
                |cb| {
                    cb.require_equal(
                        "tag_length =? 1",
                        meta.query_advice(rlp_table.tag_length_eq_one, Rotation::cur()),
                        tlength_eq.clone(),
                    );
                }
            );
            // if tag_index == tag_length && tag_length == 1
            cb.condition(
                is_simple_tag.clone() * tindex_eq_tlength.clone() * tlength_eq.clone(),
                |cb| {
                    let value = select::expr(
                        value_eq_128.is_equal_expression.expr(),
                        0.expr(),
                        meta.query_advice(byte_value, Rotation::cur()),
                    );
                    cb.require_equal("byte_value < 129", value_lt_129.is_lt(meta, None), 1.expr());
                    cb.require_equal(
                        "value == value_acc",
                        value,
                        meta.query_advice(rlp_table.value_acc, Rotation::cur()),
                    );
                },
            );

            // if tag_index == tag_length && tag_length > 1
            cb.condition(
                is_simple_tag.clone() * tindex_eq_tlength.clone() * tlength_lt.clone(),
                |cb| {
                    cb.require_equal("127 < value", value_gt_127.is_lt(meta, None), 1.expr());
                    cb.require_equal("value < 184", value_lt_184.is_lt(meta, None), 1.expr());
                    cb.require_equal(
                        "length_acc == value - 0x80",
                        meta.query_advice(length_acc, Rotation::cur()),
                        meta.query_advice(byte_value, Rotation::cur()) - 128.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == length_acc",
                        meta.query_advice(rlp_table.tag_rindex, Rotation::next()),
                        meta.query_advice(length_acc, Rotation::cur()),
                    );
                    cb.require_equal(
                        "value_acc == 0",
                        meta.query_advice(rlp_table.value_acc, Rotation::cur()),
                        0.expr(),
                    );
                },
            );

            // if tag_index > 1
            cb.condition(is_simple_tag.clone() * tindex_lt.clone(), |cb| {
                cb.require_equal(
                    "tag::next == tag",
                    meta.query_advice(rlp_table.tag, Rotation::next()),
                    meta.query_advice(rlp_table.tag, Rotation::cur()),
                );
                cb.require_equal(
                    "tag_index::next == tag_index - 1",
                    meta.query_advice(rlp_table.tag_rindex, Rotation::next()),
                    meta.query_advice(rlp_table.tag_rindex, Rotation::cur()) - 1.expr(),
                );
                cb.require_equal(
                    "tag_length::next == tag_length",
                    meta.query_advice(tag_length, Rotation::next()),
                    meta.query_advice(tag_length, Rotation::cur()),
                );
                let power_base = select::expr(
                    is_tag_word,
                    evm_word_rand.expr(),
                    256.expr(),
                );
                cb.require_equal(
                    "[simple_tag] value_acc::next == value_acc::cur * power_base + value::next",
                    meta.query_advice(rlp_table.value_acc, Rotation::next()),
                    meta.query_advice(rlp_table.value_acc, Rotation::cur()) * power_base +
                        meta.query_advice(byte_value, Rotation::next()),
                );
            });

            // if tag_index == 1
            cb.condition(is_simple_tag * tindex_eq.clone(), |cb| {
                cb.require_equal(
                    "tag_index::next == tag_length::next",
                    meta.query_advice(rlp_table.tag_rindex, Rotation::next()),
                    meta.query_advice(tag_length, Rotation::next()),
                );
            });

            //////////////////////////////////////////////////////////////////////////////////////
            ///////////////////////////////// RlpTxTag::DataPrefix ///////////////////////////////
            //////////////////////////////////////////////////////////////////////////////////////
            cb.condition(is_dp_tag.expr(), |cb| {
                // tag_index < 10
                cb.require_equal(
                    "tag_index < 10",
                    tag_index_lt_10.is_lt(meta, None),
                    1.expr(),
                );

                // tag_index >= 1
                cb.require_zero(
                    "tag_index >= 1",
                    not::expr(or::expr([tindex_lt.clone(), tindex_eq.clone()])),
                );
            });

            // if tag_index > 1
            cb.condition(is_dp_tag.expr() * tindex_lt.clone(), |cb| {
                cb.require_equal(
                    "tag::next == RlpTxTag::DataPrefix",
                    meta.query_advice(rlp_table.tag, Rotation::next()),
                    RlpTxTag::DataPrefix.expr(),
                );
                cb.require_equal(
                    "tag_index::next == tag_index - 1",
                    meta.query_advice(rlp_table.tag_rindex, Rotation::next()),
                    meta.query_advice(rlp_table.tag_rindex, Rotation::cur()) - 1.expr(),
                );
                cb.require_equal(
                    "tag_length::next == tag_length",
                    meta.query_advice(tag_length, Rotation::next()),
                    meta.query_advice(tag_length, Rotation::cur()),
                );
            });

            // if length_acc == 0
            cb.condition(
                is_dp_tag.expr() * tindex_eq.clone() * length_acc_eq_0,
                |cb| {
                    let is_tx_hash = meta.query_advice(rlp_table.data_type, Rotation::cur())
                        - RlpDataType::TxSign.expr();
                    let tag_next = select::expr(
                        is_tx_hash,
                        SigV.expr(),
                        ChainId.expr(),
                    );
                    cb.require_equal(
                        "value_acc == length_acc",
                        meta.query_advice(rlp_table.value_acc, Rotation::cur()),
                        meta.query_advice(length_acc, Rotation::cur()),
                    );
                    cb.require_equal(
                        "tag::next == RlpTxTag::ChainId",
                        meta.query_advice(rlp_table.tag, Rotation::next()),
                        tag_next,
                    );
                    cb.require_equal(
                        "tag_index::next == tag_length::next",
                        meta.query_advice(rlp_table.tag_rindex, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::next()),
                    );
                },
            );

            // if length_acc > 0
            cb.condition(
                is_dp_tag.expr() * tindex_eq.clone() * length_acc_gt_0,
                |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::Data",
                        meta.query_advice(rlp_table.tag, Rotation::next()),
                        RlpTxTag::Data.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == tag_length::next",
                        meta.query_advice(rlp_table.tag_rindex, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::next()),
                    );
                    cb.require_equal(
                        "tag_length::next == length_acc",
                        meta.query_advice(tag_length, Rotation::next()),
                        meta.query_advice(length_acc, Rotation::cur()),
                    );
                    cb.require_equal(
                        "value_acc == length_acc",
                        meta.query_advice(rlp_table.value_acc, Rotation::cur()),
                        meta.query_advice(length_acc, Rotation::cur()),
                    );
                },
            );

            // if tag_index == tag_length && tag_length > 1
            cb.condition(
                is_dp_tag.expr() * tindex_eq_tlength.clone() * tlength_lt.clone(),
                |cb| {
                    cb.require_equal("value > 183", value_gt_183.is_lt(meta, None), 1.expr());
                    cb.require_equal("value < 192", value_lt_192.is_lt(meta, None), 1.expr());
                    cb.require_equal(
                        "tag_index == (value - 0xb7) + 1",
                        meta.query_advice(rlp_table.tag_rindex, Rotation::cur()),
                        meta.query_advice(byte_value, Rotation::cur()) - 182.expr(),
                    );
                    cb.require_zero(
                        "length_acc == 0",
                        meta.query_advice(length_acc, Rotation::cur()),
                    );
                },
            );

            // if tag_index < tag_length && tag_length > 1
            cb.condition(
                is_dp_tag.expr() * tindex_lt_tlength * tlength_lt,
                |cb| {
                    cb.require_equal(
                        "length_acc == (length_acc::prev * 256) + value",
                        meta.query_advice(length_acc, Rotation::cur()),
                        meta.query_advice(length_acc, Rotation::prev()) * 256.expr()
                            + meta.query_advice(byte_value, Rotation::cur()),
                    );
                },
            );

            // if tag_index == tag_length && tag_length == 1
            cb.condition(
                is_dp_tag.expr() * tindex_eq_tlength * tlength_eq,
                |cb| {
                    cb.require_equal("value < 184", value_lt_184.is_lt(meta, None), 1.expr());
                    let real_length_acc = select::expr(
                        value_gt_127.is_lt(meta, None),
                        meta.query_advice(byte_value, Rotation::cur()) - 128.expr(), // value > 127
                        1.expr(),
                    );
                    cb.require_equal(
                        "length_acc == value > 127 ? value - 0x80 : 1",
                        meta.query_advice(length_acc, Rotation::cur()),
                        real_length_acc,
                    );
                },
            );

            //////////////////////////////////////////////////////////////////////////////////////
            //////////////////////////////////// RlpTxTag::Data //////////////////////////////////
            //////////////////////////////////////////////////////////////////////////////////////
            cb.condition(is_data(meta), |cb| {
                // tag_index >= 1
                cb.require_zero(
                    "tag_index >= 1",
                    not::expr(or::expr([tindex_lt.clone(), tindex_eq.clone()])),
                );
            });

            // if tag_index > 1
            cb.condition(is_data(meta) * tindex_lt.clone(), |cb| {
                cb.require_equal(
                    "tag::next == RlpTxTag::Data",
                    meta.query_advice(rlp_table.tag, Rotation::next()),
                    RlpTxTag::Data.expr(),
                );
                cb.require_equal(
                    "tag_rindex::next == tag_rindex - 1",
                    meta.query_advice(rlp_table.tag_rindex, Rotation::next()),
                    meta.query_advice(rlp_table.tag_rindex, Rotation::cur()) - 1.expr(),
                );
                cb.require_equal(
                    "tag_length::next == tag_length",
                    meta.query_advice(tag_length, Rotation::next()),
                    meta.query_advice(tag_length, Rotation::cur()),
                );
                cb.require_equal(
                    "calldata_bytes_rlc_acc' == calldata_bytes_rlc_acc * r + byte_value'",
                    meta.query_advice(calldata_bytes_rlc_acc, Rotation::next()),
                    meta.query_advice(calldata_bytes_rlc_acc, Rotation::cur()) * keccak_input_rand.clone()
                        + meta.query_advice(byte_value, Rotation::next()),
                );
                cb.require_equal(
                    "rlp_table.value_acc == byte_value",
                    meta.query_advice(rlp_table.value_acc, Rotation::cur()),
                    meta.query_advice(byte_value, Rotation::cur()),
                );
            });

            // if tag_index == 1 for TxSign
            cb.condition(
                and::expr(vec![
                    is_data(meta),
                    tindex_eq.clone(),
                    not::expr(meta.query_advice(rlp_table.data_type, Rotation::cur())),
                ]),
                |cb| {
                    cb.require_equal(
                        "[data] tag::next == RlpTxTag::ChainId",
                        meta.query_advice(rlp_table.tag, Rotation::next()),
                        RlpTxTag::ChainId.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == tag_length::next",
                        meta.query_advice(rlp_table.tag_rindex, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::next()),
                    );
                }
            );

            // if tag_index == 1 for TxHash
            cb.condition(
                and::expr(vec![
                    is_data(meta),
                    tindex_eq.clone(),
                    meta.query_advice(rlp_table.data_type, Rotation::cur()),
                ]),
                |cb| {
                    cb.require_equal(
                        "tag::next == RlpTxTag::SigV",
                        meta.query_advice(rlp_table.tag, Rotation::next()),
                        RlpTxTag::SigV.expr(),
                    );
                    cb.require_equal(
                        "tag_index::next == tag_length::next",
                        meta.query_advice(rlp_table.tag_rindex, Rotation::next()),
                        meta.query_advice(tag_length, Rotation::next()),
                    );
                }
            );

            cb.gate(meta.query_fixed(q_usable, Rotation::cur()))
        });

        meta.create_gate("DataType::TxSign (unsigned transaction)", |meta| {
            let mut cb = BaseConstraintBuilder::new(9);

            let (_, tindex_eq) = tag_index_cmp_1.expr(meta, None);

            //////////////////////////////////////////////////////////////////////////////////////
            ////////////////////////////////// RlpTxTag::ChainID /////////////////////////////////
            //////////////////////////////////////////////////////////////////////////////////////

            // if tag_index == 1
            cb.condition(is_chainid(meta) * tindex_eq, |cb| {
                // checks for RlpTxTag::Zero on the next row.
                cb.require_equal(
                    "next tag is Zero",
                    meta.query_advice(rlp_table.tag, Rotation::next()),
                    RlpTxTag::Zero.expr(),
                );
                cb.require_equal(
                    "next tag is Zero => tag_rindex::next == 1",
                    meta.query_advice(rlp_table.tag_rindex, Rotation::next()),
                    1.expr(),
                );
                cb.require_equal(
                    "next tag is Zero => value::next == 128",
                    meta.query_advice(byte_value, Rotation::next()),
                    128.expr(),
                );
                cb.require_equal(
                    "next tag is Zero => value_acc::next == 0",
                    meta.query_advice(rlp_table.value_acc, Rotation::next()),
                    0.expr(),
                );

                // checks for RlpTxTag::Zero on the next(2) row.
                cb.require_equal(
                    "tag::Rotation(2) == RlpTxTag::Zero",
                    meta.query_advice(rlp_table.tag, Rotation(2)),
                    RlpTxTag::Zero.expr(),
                );
                cb.require_equal(
                    "tag_rindex::Rotation(2) == tag_length::Rotation(2)",
                    meta.query_advice(rlp_table.tag_rindex, Rotation(2)),
                    meta.query_advice(tag_length, Rotation(2)),
                );
                cb.require_equal(
                    "next-to-next tag is Zero => tag_rindex::Rotation(2) == 1",
                    meta.query_advice(rlp_table.tag_rindex, Rotation(2)),
                    1.expr(),
                );
                cb.require_equal(
                    "next-to-next tag is Zero => value::Rotation(2) == 128",
                    meta.query_advice(byte_value, Rotation(2)),
                    128.expr(),
                );
                cb.require_equal(
                    "next-to-next tag is Zero => value_acc::Rotation(2) == 0",
                    meta.query_advice(rlp_table.value_acc, Rotation(2)),
                    0.expr(),
                );

                // checks for RlpTxTag::RlpLength on the next(3) row.
                cb.require_equal(
                    "tag::Rotation(3) == RlpTxTag::RlpLength",
                    meta.query_advice(rlp_table.tag, Rotation(3)),
                    RlpTxTag::RlpLength.expr(),
                );
                cb.require_equal(
                    "tag_rindex::Rotation(3) == tag_length::Rotation(3)",
                    meta.query_advice(rlp_table.tag_rindex, Rotation(3)),
                    meta.query_advice(tag_length, Rotation(3)),
                );
                cb.require_equal(
                    "tag_rindex::Rotation(3) == 1",
                    meta.query_advice(rlp_table.tag_rindex, Rotation(3)),
                    1.expr(),
                );
                cb.require_equal(
                    "value_acc::Rotation(3) == Rlp encoding length == index::Rotation(2)",
                    meta.query_advice(rlp_table.value_acc, Rotation(3)),
                    meta.query_advice(index, Rotation(2)),
                );

                // checks for RlpTxTag::Rlp on the next(4) row.
                cb.require_equal(
                    "tag::Rotation(4) == RlpTxTag::Rlp",
                    meta.query_advice(rlp_table.tag, Rotation(4)),
                    RlpTxTag::Rlp.expr(),
                );
                // reaches the end of an RLP(TxSign) instance
                cb.require_zero(
                    "next(4) tag is Rlp => rindex == 0",
                    meta.query_advice(rindex, Rotation(4)),
                );
                cb.require_equal(
                    "tag_rindex::Rotation(4) == tag_length::Rotation(4)",
                    meta.query_advice(rlp_table.tag_rindex, Rotation(4)),
                    meta.query_advice(tag_length, Rotation(4)),
                );
                cb.require_equal(
                    "tag_rindex::Rotation(4) == 1",
                    meta.query_advice(rlp_table.tag_rindex, Rotation(4)),
                    1.expr(),
                );
                cb.require_equal(
                    "last tag is Rlp => value_acc::Rotation(4) == all_bytes_rlc_acc::Rotation(2)",
                    meta.query_advice(rlp_table.value_acc, Rotation(4)),
                    meta.query_advice(all_bytes_rlc_acc, Rotation(2)),
                );
                cb.require_equal(
                    "last tag is Rlp => is_last::Rotation(4) == 1",
                    meta.query_advice(is_last, Rotation(4)),
                    1.expr(),
                );
            });

            cb.gate(and::expr(vec![
                meta.query_fixed(q_usable, Rotation::cur()),
                not::expr(meta.query_advice(rlp_table.data_type, Rotation::cur())),
            ]))
        });

        meta.create_gate("DataType::TxHash (signed transaction)", |meta| {
            let mut cb = BaseConstraintBuilder::new(9);

            let (_, tindex_eq) = tag_index_cmp_1.expr(meta, None);

            // if tag_index == 1
            cb.condition(is_sig_s(meta) * tindex_eq, |cb| {
                // rindex == 0 for the end of an RLP(TxHash) instance
                cb.require_equal(
                    "next(2) tag is Rlp => rindex == 0",
                    meta.query_advice(rindex, Rotation::cur()),
                    0.expr(),
                );
                // // RlpTxTag::RlpLength checks.
                // cb.require_equal(
                //     "next tag is RlpLength",
                //     meta.query_advice(rlp_table.tag, Rotation::next()),
                //     RlpTxTag::RlpLength.expr(),
                // );
                // cb.require_equal(
                //     "tag_rindex::next == 1",
                //     meta.query_advice(rlp_table.tag_rindex,
                // Rotation::next()),     1.expr(),
                // );
                // cb.require_equal(
                //     "tag::next == RlpLength => value_acc::next ==
                // index::cur",     meta.query_advice(rlp_table.
                // value_acc, Rotation::next()),
                //     meta.query_advice(index, Rotation::cur()),
                // );

                // // RlpTxTag::Rlp checks.
                // cb.require_equal(
                //     "tag::Rotation(2) == RlpTxTag::Rlp",
                //     meta.query_advice(rlp_table.tag, Rotation(2)),
                //     RlpTxTag::Rlp.expr(),
                // );
                // cb.require_equal(
                //     "last tag is Rlp => value_acc::Rotation(2) ==
                // all_bytes_rlc_acc::cur()",
                //     meta.query_advice(rlp_table.value_acc, Rotation(2)),
                //     meta.query_advice(all_bytes_rlc_acc, Rotation::cur()),
                // );
                // cb.require_equal(
                //     "is_last::Rotation(2) == 1",
                //     meta.query_advice(is_last, Rotation(2)),
                //     1.expr(),
                // );
            });

            cb.gate(and::expr(vec![
                meta.query_fixed(q_usable, Rotation::cur()),
                meta.query_advice(rlp_table.data_type, Rotation::cur()),
            ]))
        });

        // Constraints that always need to be satisfied.
        meta.create_gate("always", |meta| {
            let mut cb = BaseConstraintBuilder::new(9);

            cb.require_boolean(
                "is_first is boolean",
                meta.query_advice(is_first, Rotation::cur()),
            );
            cb.require_boolean(
                "is_last is boolean",
                meta.query_advice(is_last, Rotation::cur()),
            );
            cb.require_in_set(
                "data_type is in set {TxHash, TxSign}",
                meta.query_advice(rlp_table.data_type, Rotation::cur()),
                vec![RlpDataType::TxHash.expr(), RlpDataType::TxSign.expr()],
            );

            cb.gate(meta.query_fixed(q_usable, Rotation::cur()))
        });

        // Constraints for the first row in the layout.
        meta.create_gate("is_first == 1", |meta| {
            let mut cb = BaseConstraintBuilder::new(9);

            cb.require_equal(
                "value_rlc == value",
                meta.query_advice(all_bytes_rlc_acc, Rotation::cur()),
                meta.query_advice(byte_value, Rotation::cur()),
            );
            cb.require_equal(
                "index == 1",
                meta.query_advice(index, Rotation::cur()),
                1.expr(),
            );

            cb.gate(and::expr(vec![
                meta.query_fixed(q_usable, Rotation::cur()),
                meta.query_advice(is_first, Rotation::cur()),
                not::expr(is_padding(meta)),
            ]))
        });

        // Constraints for every row except the last row in one RLP instance.
        meta.create_gate("is_last == 0", |meta| {
            let mut cb = BaseConstraintBuilder::new(9);

            cb.condition(
                not::expr(meta.query_advice(placeholder, Rotation::cur())),
                |cb| {
                    cb.require_equal(
                        "index' == index + 1",
                        meta.query_advice(index, Rotation::next()),
                        meta.query_advice(index, Rotation::cur()) + 1.expr(),
                    );
                    cb.require_equal(
                        "rindex' == rindex - 1",
                        meta.query_advice(rindex, Rotation::next()),
                        meta.query_advice(rindex, Rotation::cur()) - 1.expr(),
                    );
                    cb.require_equal(
                        "all_bytes_rlc_acc' == (all_bytes_rlc_acc * r) + byte_value'",
                        meta.query_advice(all_bytes_rlc_acc, Rotation::next()),
                        meta.query_advice(all_bytes_rlc_acc, Rotation::cur())
                            * keccak_input_rand.clone()
                            + meta.query_advice(byte_value, Rotation::next()),
                    );
                },
            );
            cb.condition(meta.query_advice(placeholder, Rotation::cur()), |cb| {
                cb.require_equal(
                    "index' == index",
                    meta.query_advice(index, Rotation::next()),
                    meta.query_advice(index, Rotation::cur()),
                );
                cb.require_equal(
                    "rindex' == rindex",
                    meta.query_advice(rindex, Rotation::next()),
                    meta.query_advice(rindex, Rotation::cur()),
                );
                cb.require_equal(
                    "all_bytes_rlc_acc' == all_bytes_rlc_acc",
                    meta.query_advice(all_bytes_rlc_acc, Rotation::next()),
                    meta.query_advice(all_bytes_rlc_acc, Rotation::cur()),
                );
                cb.require_equal(
                    "byte_value' == byte_value",
                    meta.query_advice(byte_value, Rotation::next()),
                    meta.query_advice(byte_value, Rotation::cur()),
                );
                cb.require_equal(
                    "input_bytes_rlc_acc' == input_bytes_rlc_acc",
                    meta.query_advice(input_bytes_rlc_acc, Rotation::next()),
                    meta.query_advice(input_bytes_rlc_acc, Rotation::cur()),
                );
            });

            cb.require_equal(
                "tx_id' == tx_id",
                meta.query_advice(rlp_table.tx_id, Rotation::next()),
                meta.query_advice(rlp_table.tx_id, Rotation::cur()),
            );
            cb.require_equal(
                "data_type' == data_type",
                meta.query_advice(rlp_table.data_type, Rotation::next()),
                meta.query_advice(rlp_table.data_type, Rotation::cur()),
            );

            cb.gate(and::expr(vec![
                meta.query_fixed(q_usable, Rotation::cur()),
                not::expr(meta.query_advice(is_last, Rotation::cur())),
                not::expr(is_padding(meta)),
            ]))
        });

        meta.create_gate("placeholder row only happens on DataPrefix", |meta| {
            let mut cb = BaseConstraintBuilder::default();
            let (_, tag_length_eq_one) = tag_length_cmp_1.expr(meta, Some(Rotation::cur()));

            cb.require_equal("tag == DataPrefix", is_data_prefix(meta), 1.expr());
            cb.require_equal("tag_length == 1", tag_length_eq_one, 1.expr());
            cb.require_equal(
                "byte_value <= 0x80",
                value_lt_129.is_lt(meta, None),
                1.expr(),
            );
            cb.require_zero(
                "byte_value != 0x80",
                value_eq_128.is_equal_expression.expr(),
            );

            cb.gate(and::expr(vec![
                meta.query_fixed(q_usable, Rotation::cur()),
                meta.query_advice(placeholder, Rotation::cur()),
            ]))
        });

        // Constraints for the last row, i.e. RLP summary row.
        meta.create_gate("is_last == 1", |meta| {
            let mut cb = BaseConstraintBuilder::new(9);

            // cb.require_equal(
            //     "is_last == 1 then tag == RlpTxTag::Rlp",
            //     meta.query_advice(rlp_table.tag, Rotation::cur()),
            //     RlpTxTag::Rlp.expr(),
            // );

            // no TxHash -> TxSign switch
            // if data_type::cur == TxHash
            // - tx_id does not change.
            // - TxSign rows follow.
            // cb.condition(
            //     meta.query_advice(rlp_table.data_type, Rotation::cur()),
            //     |cb| {
            //         cb.require_equal(
            //             "tx_id does not change",
            //             meta.query_advice(rlp_table.tx_id, Rotation::cur()),
            //             meta.query_advice(rlp_table.tx_id, Rotation::next()),
            //         );
            //         cb.require_equal(
            //             "TxSign rows follow TxHash rows",
            //             meta.query_advice(rlp_table.data_type, Rotation::next()),
            //             RlpDataType::TxSign.expr(),
            //         );
            //         cb.require_equal(
            //             "TxSign rows' first row is Prefix again",
            //             meta.query_advice(rlp_table.tag, Rotation::next()),
            //             RlpTxTag::TxPrefix.expr(),
            //         );
            //         cb.require_equal(
            //             "TxSign rows' first row starts with rlp_table.tag_rindex =
            // tag_length",             meta.query_advice(rlp_table.tag_rindex,
            // Rotation::next()),             meta.query_advice(tag_length,
            // Rotation::next()),         );
            //     },
            // );

            // no TxSign, so is_last ahead to next TxHash
            // if data_type::cur == TxSign and it was **not**
            // the last tx in the layout (tag::next != Padding)
            // - tx_id increments.
            // - TxHash rows follow.
            let is_tag_next_padding =
                tag_bits.value_equals(RlpTxTag::Padding, Rotation::next())(meta);
            cb.condition(not::expr(is_tag_next_padding), |cb| {
                cb.require_equal(
                    "tx_id increments",
                    meta.query_advice(rlp_table.tx_id, Rotation::cur()) + 1.expr(),
                    meta.query_advice(rlp_table.tx_id, Rotation::next()),
                );
                cb.require_equal(
                    "TxHash rows follow TxSign rows",
                    meta.query_advice(rlp_table.data_type, Rotation::next()),
                    RlpDataType::TxHash.expr(),
                );
                cb.require_equal(
                    "TxHash rows' first row is Prefix again",
                    meta.query_advice(rlp_table.tag, Rotation::next()),
                    RlpTxTag::TxPrefix.expr(),
                );
                cb.require_equal(
                    "TxSign rows' first row starts with rlp_table.tag_rindex = tag_length",
                    meta.query_advice(rlp_table.tag_rindex, Rotation::next()),
                    meta.query_advice(tag_length, Rotation::next()),
                );
            });

            cb.gate(and::expr(vec![
                meta.query_fixed(q_usable, Rotation::cur()),
                meta.query_advice(is_last, Rotation::cur()),
            ]))
        });

        meta.create_gate("padding rows", |meta| {
            let mut cb = BaseConstraintBuilder::new(9);

            cb.condition(is_padding(meta), |cb| {
                cb.require_equal(
                    "tag_next == Padding",
                    meta.query_advice(rlp_table.tag, Rotation::next()),
                    RlpTxTag::Padding.expr(),
                );

                cb.require_zero(
                    "tx_id == 0",
                    meta.query_advice(rlp_table.tx_id, Rotation::cur()),
                );
                cb.require_zero(
                    "data_type == 0",
                    meta.query_advice(rlp_table.data_type, Rotation::cur()),
                );
                cb.require_zero(
                    "tag_rindex == 0",
                    meta.query_advice(rlp_table.tag_rindex, Rotation::cur()),
                );
                cb.require_zero(
                    "value_acc == 0",
                    meta.query_advice(rlp_table.value_acc, Rotation::cur()),
                );
            });

            cb.gate(meta.query_fixed(q_usable, Rotation::cur()))
        });

        //////////////////////////////////////////////////////////////////////////
        ///// Below are constraints for rlp decoding & validness check ///////////
        //////////////////////////////////////////////////////////////////////////
        // Step 1: copy input data to output table according to rlp_valid flag
        meta.create_gate("process input data to output table", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);
            let byte_value_cell = meta.query_advice(byte_value, Rotation::cur());
            let input_byte_cell = meta.query_advice(input_byte_value, Rotation::cur());
            let rlp_valid_cell = meta.query_advice(rlp_valid, Rotation::cur());

            // output_table == decoded_table * rlp_valid
            // TODO: could be ifx/elsex
            let is_first = meta.query_advice(is_first, Rotation::cur());
            cb.condition(not::expr(is_first.expr()), |cb| {
                cb.require_equal(
                    "input bytes == rlp.bytes * rlp_valid",
                    byte_value_cell.clone(),
                    input_byte_cell.clone() * rlp_valid_cell.clone(),
                );
            });

            cb.condition(not::expr(rlp_valid_cell.clone()) * is_first.expr(), |cb| {
                cb.require_equal(
                    "input bytes [0] == 148 if not valid",
                    byte_value_cell.clone(),
                    148.expr(),
                );
            });

            cb.condition(rlp_valid_cell.expr() * is_first.expr(), |cb| {
                cb.require_equal(
                    "input bytes == rlp.bytes * rlp_valid",
                    byte_value_cell.clone(),
                    input_byte_cell.clone() * rlp_valid_cell.clone(),
                );
            });

            cb.condition(
                not::expr(meta.query_advice(placeholder, Rotation::cur()))
                    * meta.query_fixed(q_decode_usable, Rotation::next()),
                |cb| {
                    // TODO: index column check
                    cb.require_equal(
                        "input_bytes_rlc_acc' == (input_bytes_rlc_acc * r) + byte_value'",
                        meta.query_advice(input_bytes_rlc_acc, Rotation::next()),
                        meta.query_advice(input_bytes_rlc_acc, Rotation::cur())
                            * keccak_input_rand.clone()
                            + meta.query_advice(input_byte_value, Rotation::next()),
                    );
                },
            );

            let q_decode_usable = meta.query_fixed(q_decode_usable, Rotation::cur());
            cb.gate(q_decode_usable)
        });

        // Step 2: constraint decoding tag transition
        meta.lookup_any("decoded (valid, tag, tag_next) in tag_ROM", |meta| {
            let rlp_valid_cell = meta.query_advice(rlp_valid, Rotation::cur());
            let tag = meta.query_advice(rlp_table.tag, Rotation::cur());
            let tag_next = meta.query_advice(rlp_table.tag, Rotation::next());
            let rom_rlp_valid = meta.query_fixed(tag_rom.rlp_valid, Rotation::cur());
            let rom_tag = meta.query_fixed(tag_rom.tag, Rotation::cur());
            let rom_tag_next = meta.query_fixed(tag_rom.tag_next, Rotation::cur());
            let q_decode_usable = meta.query_fixed(q_decode_usable, Rotation::cur());
            let (_, tag_idx_eq_one) = tag_index_cmp_1.expr(meta, None);
            let condition = q_decode_usable * tag_idx_eq_one;

            vec![
                (condition.expr() * rlp_valid_cell, rom_rlp_valid),
                (condition.expr() * tag, rom_tag),
                (condition * tag_next, rom_tag_next),
            ]
        });

        // Re-apply key common contraints to decoding column
        // This makes sure that rlp_valid is correctly set as this part computers the
        // rlp_valid Actually we only checks the decoding length and tag
        // switching because this is merely the 2 possbile ways.
        // 1. check length.
        // 2. check tag movement.
        macro_rules! make_value_cmp_gadget {
            ($var:ident > $num:expr) => {
                let $var = LtChip::configure(
                    meta,
                    cmp_lt_enabled,
                    |_meta| $num.expr(),
                    |meta| meta.query_advice(input_byte_value, Rotation::cur()),
                );
            };
            ($var:ident < $num:expr) => {
                let $var = LtChip::configure(
                    meta,
                    cmp_lt_enabled,
                    |meta| meta.query_advice(input_byte_value, Rotation::cur()),
                    |_meta| $num.expr(),
                );
            };
            ($var:ident == $num:expr) => {
                let $var = IsEqualChip::configure(
                    meta,
                    cmp_lt_enabled,
                    |meta| meta.query_advice(input_byte_value, Rotation::cur()),
                    |_meta| $num.expr(),
                );
            };
        }

        make_value_cmp_gadget!(input_value_gt_247 > 247);
        make_value_cmp_gadget!(input_value_gt_127 > 127);
        make_value_cmp_gadget!(input_value_gt_183 > 183);
        make_value_cmp_gadget!(input_value_gt_191 > 191);
        make_value_cmp_gadget!(input_value_lt_129 < 129);
        make_value_cmp_gadget!(input_value_eq_128 == 128);
        make_value_cmp_gadget!(input_value_lt_184 < 184);
        make_value_cmp_gadget!(input_value_lt_192 < 192);
        make_value_cmp_gadget!(input_value_lt_248 < 248);

        meta.create_gate("Common constraints for decoding columns", |meta| {
            let mut cb = BaseConstraintBuilder::new(9);

            let (tindex_lt, tindex_eq) = tag_index_cmp_1.expr(meta, None);
            assert_eq!(tindex_lt.degree(), 1, "{}", tindex_lt.degree());
            assert_eq!(tindex_eq.degree(), 2, "{}", tindex_lt.degree());
            let (tlength_lt, tlength_eq) = tag_length_cmp_1.expr(meta, None);
            let (tindex_lt_tlength, tindex_eq_tlength) = tag_index_length_cmp.expr(meta, None);
            let (length_acc_gt_0, length_acc_eq_0) = length_acc_cmp_0.expr(meta, None);
            let is_simple_tag = meta.query_advice(is_simple_tag, Rotation::cur());
            let is_decode_prefix_tag = meta.query_fixed(is_decode_prefix_tag, Rotation::cur());
            let is_dp_tag = meta.query_advice(is_dp_tag, Rotation::cur());
            let is_rlp_valid = meta.query_advice(rlp_valid, Rotation::cur());

            //////////////////////////////////////////////////////////////////////////////////////
            ////////////////////////////////// RlpHeaderTag::Prefix //////////////////////////////
            //////////////////////////////////////////////////////////////////////////////////////
            // TODO: merge to tx prefix
            cb.condition(is_decode_prefix_tag.expr(), |cb| {
                // tag_index < 10
                cb.require_equal(
                    "tag_index < 10",
                    tag_index_lt_10.is_lt(meta, None),
                    1.expr(),
                );

                // tag_index >= 1
                cb.require_zero(
                    "tag_index >= 1",
                    not::expr(or::expr([tindex_lt.clone(), tindex_eq.clone()])),
                );
            });

            // if tag_index > 1
            cb.condition(is_decode_prefix_tag.expr() * tindex_lt.clone() * is_rlp_valid.clone(), |cb| {
                cb.require_equal(
                    "tag::next == RlpTxTag::TxListPrefix",
                    meta.query_advice(rlp_table.tag, Rotation::next()),
                    RlpTxTag::TxListPrefix.expr(),
                );
                cb.require_equal(
                    "tag_index::next == tag_index - 1",
                    meta.query_advice(rlp_table.tag_rindex, Rotation::next()),
                    meta.query_advice(rlp_table.tag_rindex, Rotation::cur()) - 1.expr(),
                );
                cb.require_equal(
                    "tag_length::next == tag_length",
                    meta.query_advice(tag_length, Rotation::next()),
                    meta.query_advice(tag_length, Rotation::cur()),
                );
            });

            // if tag_index == 1, RlpArrayPrefix -> RlpTxPrefix (another array prefix for legacy Tx)
            cb.condition(is_decode_prefix_tag.expr() * tindex_eq.clone() * is_rlp_valid.clone(), |cb| {
                cb.require_equal(
                    "next row below array prefix is tx prefix",
                    meta.query_advice(is_prefix_tag, Rotation::next()),
                    1.expr(),
                );
                // cb.require_equal(
                //     "tag::next == RlpTxTag::TxPrefix",
                //     meta.query_advice(rlp_table.tag, Rotation::next()),
                //     RlpTxTag::TxPrefix.expr(),
                // );
                cb.require_equal(
                    "tag_index::next == tag_length::next",
                    meta.query_advice(rlp_table.tag_rindex, Rotation::next()),
                    meta.query_advice(tag_length, Rotation::next()),
                );
                cb.require_equal(
                    "byte_left::curr == length_acc",
                    meta.query_advice(input_bytes_left, Rotation::cur()),
                    meta.query_advice(length_acc, Rotation::cur()),
                );
            });

            // if tag_index == tag_length && tag_length > 1
            cb.condition(
                is_decode_prefix_tag.expr() * tindex_eq_tlength.clone() * tlength_lt.clone() * is_rlp_valid.clone(),
                |cb| {
                    cb.require_equal("247 < value", value_gt_247.is_lt(meta, None), 1.expr());
                    // cb.require_equal("value < 256", value_lt_256.is_lt(meta, None), 1.expr());
                    cb.require_equal(
                        "tag_index::next == value - 0xf7",
                        meta.query_advice(rlp_table.tag_rindex, Rotation::next()),
                        meta.query_advice(byte_value, Rotation::cur()) - 247.expr(),
                    );
                    cb.require_zero(
                        "length_acc == 0",
                        meta.query_advice(length_acc, Rotation::cur()),
                    );
                },
            );

            // if tag_index < tag_length && tag_length > 1
            cb.condition(
                is_decode_prefix_tag.expr() * tindex_lt_tlength.clone() * tlength_lt.clone() * is_rlp_valid.clone(),
                |cb| {
                    cb.require_equal(
                        "length_acc == (length_acc::prev * 256) + value",
                        meta.query_advice(length_acc, Rotation::cur()),
                        meta.query_advice(length_acc, Rotation::prev()) * 256.expr()
                            + meta.query_advice(byte_value, Rotation::cur()),
                    );
                },
            );

            // check the value is decodable.
            cb.condition(
                is_decode_prefix_tag.expr() * tindex_eq_tlength.clone() * tlength_lt.clone(),
                |cb| {
                    cb.require_equal("247 < value", input_value_gt_247.is_lt(meta, None), is_rlp_valid.clone());
                },
            );

            // bytes left count-down
            cb.condition(
              meta.query_fixed(q_end, Rotation::cur()),
               |cb| {
                    cb.require_equal(
                    "input_bytes_left::next == input_bytes_left::cur - 1",
                    meta.query_advice(input_bytes_left, Rotation::next()),
                    meta.query_advice(input_bytes_left, Rotation::cur()) - 1.expr(),
              );
            },
          );

            //////////////////////////////////////////////////////////////////////////////////////
            //////// RlpTxTag::Nonce, GasPrice, Gas, To, Value, ChainID, SigV, SigR, SigS ////////
            //////////////////////////////////////////////////////////////////////////////////////
            // if tag_index == tag_length && tag_length == 1
            cb.condition(
                is_simple_tag.clone() * tindex_eq_tlength.clone() * tlength_eq.clone(),
                |cb| {
                    cb.require_equal("byte_value < 129", input_value_lt_129.is_lt(meta, None), is_rlp_valid.clone());
                },
            );

            // if tag_index == tag_length && tag_length > 1
            cb.condition(
                is_simple_tag.clone() * tindex_eq_tlength.clone() * tlength_lt.clone(),
                |cb| {
                    cb.require_equal("127 < value", input_value_gt_127.is_lt(meta, None), is_rlp_valid.clone());
                    cb.require_equal("value < 184", input_value_lt_184.is_lt(meta, None), is_rlp_valid.clone());
                },
            );

            //////////////////////////////////////////////////////////////////////////////////////
            ///////////////////////////////// RlpTxTag::DataPrefix ///////////////////////////////
            //////////////////////////////////////////////////////////////////////////////////////
            // if length_acc == 0
            // support txHash type only
            cb.condition(
                is_dp_tag.expr() * tindex_eq.clone() * length_acc_eq_0,
                |cb| {
                    cb.require_boolean("TxHash type RLP only", meta.query_advice(rlp_table.data_type, Rotation::cur())
                        - RlpDataType::TxSign.expr());
                }
            );

            // if tag_index == tag_length && tag_length > 1
            cb.condition(
                is_dp_tag.expr() * tindex_eq_tlength.clone() * tlength_lt.clone(),
                |cb| {
                    cb.require_equal("value > 183", input_value_gt_183.is_lt(meta, None), is_rlp_valid.clone());
                    cb.require_equal("value < 192", input_value_lt_192.is_lt(meta, None), is_rlp_valid.clone());
                },
            );

            // if tag_index == tag_length && tag_length == 1
            cb.condition(
                is_dp_tag.expr() * tindex_eq_tlength * tlength_eq,
                |cb| {
                    cb.require_equal("value < 184", input_value_lt_184.is_lt(meta, None), is_rlp_valid.clone());
                },
            );

            //////////////////////////////////////////////////////////////////////////////////////
            //////////////////////////////////// RlpTxTag::Data //////////////////////////////////
            //////////////////////////////////////////////////////////////////////////////////////
            // null constraint for data
            cb.gate(meta.query_fixed(q_decode_usable, Rotation::cur()))
        });

        ////////////////////////////////////////////////////////////////
        /////////////////// RlpTxTag::Padding //////////////////////////
        ////////////////////////////////////////////////////////////////
        // last row of the tabl must be padding.
        meta.create_gate("bytes_left to 0 and circuit end with padding", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);
            let q_decode_usable_curr = meta.query_fixed(q_decode_usable, Rotation::cur());
            let q_decode_usable_next = meta.query_fixed(q_decode_usable, Rotation::next());
            let q_padding_end = meta.query_fixed(q_end, Rotation::cur());
            let bytes_left = meta.query_advice(input_bytes_left, Rotation::cur());

            cb.require_boolean("q_end is bool", q_padding_end.clone());

            cb.condition(q_padding_end.expr(), |cb| {
                cb.require_zero("no bytes left", bytes_left);

                cb.require_equal(
                    "q_end in last q_usable",
                    q_decode_usable_curr.clone(),
                    1.expr(),
                );
                cb.require_zero("not usable after q_end", q_decode_usable_next);
            });

            cb.require_equal("end with padding", q_padding_end.clone(), is_padding(meta));

            cb.gate(q_decode_usable_curr.clone())
        });

        Self {
            minimum_rows: meta.minimum_rows(),
            q_usable,
            is_first,
            is_last,
            rlp_table: *rlp_table,
            index,
            rindex,
            placeholder,
            byte_value,
            q_decode_usable,
            is_decode_prefix_tag,
            rlp_valid,
            input_byte_value,
            input_bytes_rlc_acc,
            input_bytes_left,
            q_end,
            calldata_bytes_rlc_acc,
            tag_bits,
            tag_rom,
            tag_length,
            length_acc,
            all_bytes_rlc_acc,
            is_simple_tag,
            is_prefix_tag,
            is_dp_tag,
            tag_index_cmp_1,
            tag_index_length_cmp,
            tag_length_cmp_1,
            tag_index_lt_10,
            tag_index_lt_34,
            value_gt_127,
            value_gt_183,
            value_gt_191,
            value_gt_247,
            value_lt_129,
            value_eq_128,
            value_lt_184,
            value_lt_192,
            value_lt_248,
            input_value_gt_127,
            input_value_gt_183,
            input_value_gt_191,
            input_value_gt_247,
            input_value_lt_129,
            input_value_eq_128,
            input_value_lt_184,
            input_value_lt_192,
            input_value_lt_248,
            length_acc_cmp_0,
        }
    }

    pub(crate) fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        input_bytes: &[RlpWitnessByte],
        valid: bool,
        signed_txs: &[SignedTransaction],
        k: usize,
        challenges: &Challenges<Value<F>>,
    ) -> Result<(), Error> {
        let keccak_input_rand = challenges.keccak_input();
        let tag_chip = BinaryNumberChip::construct(self.tag_bits);
        let tag_index_cmp_1_chip = ComparatorChip::construct(self.tag_index_cmp_1.clone());
        let tag_index_length_cmp_chip =
            ComparatorChip::construct(self.tag_index_length_cmp.clone());
        let tag_length_cmp_1_chip = ComparatorChip::construct(self.tag_length_cmp_1.clone());

        let tag_index_lt_10_chip = LtChip::construct(self.tag_index_lt_10);
        let tag_index_lt_34_chip = LtChip::construct(self.tag_index_lt_34);

        let value_gt_127_chip = LtChip::construct(self.value_gt_127);
        let value_gt_183_chip = LtChip::construct(self.value_gt_183);
        let value_gt_191_chip = LtChip::construct(self.value_gt_191);
        let value_gt_247_chip = LtChip::construct(self.value_gt_247);
        let value_lt_129_chip = LtChip::construct(self.value_lt_129);
        let value_eq_128_chip = IsEqualChip::construct(self.value_eq_128.clone());
        let value_lt_184_chip = LtChip::construct(self.value_lt_184);
        let value_lt_192_chip = LtChip::construct(self.value_lt_192);
        let value_lt_248_chip = LtChip::construct(self.value_lt_248);

        let length_acc_cmp_0_chip = ComparatorChip::construct(self.length_acc_cmp_0.clone());

        // input bytes related
        let input_value_gt_127_chip = LtChip::construct(self.input_value_gt_127);
        let input_value_gt_183_chip = LtChip::construct(self.input_value_gt_183);
        let input_value_gt_191_chip = LtChip::construct(self.input_value_gt_191);
        let input_value_gt_247_chip = LtChip::construct(self.input_value_gt_247);
        let input_value_lt_129_chip = LtChip::construct(self.input_value_lt_129);
        let input_value_eq_128_chip = IsEqualChip::construct(self.input_value_eq_128.clone());
        let input_value_lt_184_chip = LtChip::construct(self.input_value_lt_184);
        let input_value_lt_192_chip = LtChip::construct(self.input_value_lt_192);
        let input_value_lt_248_chip = LtChip::construct(self.input_value_lt_248);

        debug_assert!(
            k >= self.minimum_rows,
            "k: {}, minimum_rows: {}",
            k,
            self.minimum_rows,
        );
        let padding_end_offset = k - self.minimum_rows + 1;
        layouter.assign_region(
            || "assign tag rom",
            |mut region| {
                for (i, (rlp_valid, tag, tag_next, max_length)) in [
                    (true, RlpTxTag::Nonce, RlpTxTag::GasPrice, 10),
                    (true, RlpTxTag::GasPrice, RlpTxTag::Gas, 34),
                    (true, RlpTxTag::Gas, RlpTxTag::To, 10),
                    (true, RlpTxTag::To, RlpTxTag::Value, 22),
                    (true, RlpTxTag::Value, RlpTxTag::DataPrefix, 34),
                    (true, RlpTxTag::ChainId, RlpTxTag::Zero, 10),
                    (true, RlpTxTag::DataPrefix, RlpTxTag::Data, 10),
                    (true, RlpTxTag::DataPrefix, RlpTxTag::SigV, 1),
                    (true, RlpTxTag::Data, RlpTxTag::SigV, 24 * 1024), // 24k bytes
                    (true, RlpTxTag::SigV, RlpTxTag::SigR, 10),
                    (true, RlpTxTag::SigR, RlpTxTag::SigS, 34),
                    // (true, RlpTxTag::SigS, RlpTxTag::RlpLength, 34),
                    (true, RlpTxTag::SigS, RlpTxTag::TxPrefix, 34), /* No RlpLength so SigS to
                                                                     * Nonce */
                    (true, RlpTxTag::SigS, RlpTxTag::Padding, 34), // If last, SigS to Padding
                    (true, RlpTxTag::TxListPrefix, RlpTxTag::TxPrefix, 10),
                    (true, RlpTxTag::TxPrefix, RlpTxTag::Nonce, 10),
                    (false, RlpTxTag::TxListPrefix, RlpTxTag::Padding, 1),
                ]
                .into_iter()
                .enumerate()
                {
                    let offset = i;
                    region.assign_fixed(
                        || "tag",
                        self.tag_rom.rlp_valid,
                        offset,
                        || Value::known(F::from(rlp_valid as u64)),
                    )?;
                    region.assign_fixed(
                        || "tag",
                        self.tag_rom.tag,
                        offset,
                        || Value::known(F::from(tag as u64)),
                    )?;
                    region.assign_fixed(
                        || "tag_next",
                        self.tag_rom.tag_next,
                        offset,
                        || Value::known(F::from(tag_next as u64)),
                    )?;
                    region.assign_fixed(
                        || "max_length",
                        self.tag_rom.max_length,
                        offset,
                        || Value::known(F::from(max_length)),
                    )?;
                }

                Ok(())
            },
        )?;

        layouter.assign_region(
            || "assign RLP-encoded data",
            |mut region| {
                let mut offset = 0;
                let simple_tags = [
                    Nonce,
                    GasPrice,
                    Gas,
                    To,
                    RlpTxTag::Value,
                    SigV,
                    SigR,
                    SigS,
                    ChainId,
                ];

                let txlist_prefix_len = {
                    if input_bytes[0].witness_byte <= 0xF7 {
                        // invalid case
                        1usize
                    } else {
                        input_bytes[0].witness_byte as usize - 0xF7 + 1
                    }
                };

                let total_bytes = {
                    if valid {
                        input_bytes.len()
                    } else {
                        1usize
                    }
                };

                // fill input bytes
                let mut all_bytes_rlc_acc = Value::known(F::zero());
                let mut bytes_left = total_bytes;
                for (i, value) in input_bytes.iter().enumerate() {
                    region.assign_advice(
                        || format!("input byte [{}]", offset),
                        self.input_byte_value,
                        offset + i as usize,
                        || Value::known(F::from(value.witness_byte as u64)),
                    )?;

                    region.assign_advice(
                        || format!("rlp valid: {}", offset),
                        self.rlp_valid,
                        offset + i as usize,
                        || Value::known(F::from(valid as u64)),
                    )?;

                    region.assign_fixed(
                        || format!("decoder usable: {}", offset),
                        self.q_decode_usable,
                        offset + i as usize,
                        || Value::known(F::from(valid as u64)),
                    )?;

                    if bytes_left > 0 && !value.place_holder {
                        bytes_left -= 1;
                        region.assign_advice(
                            || format!("bytes left: {}", offset),
                            self.input_bytes_left,
                            offset + i as usize,
                            || Value::known(F::from(bytes_left as u64)),
                        )?;
                    }

                    if i < txlist_prefix_len {
                        region.assign_fixed(
                            || format!("decoder prefix: {}", offset),
                            self.is_decode_prefix_tag,
                            offset + i as usize,
                            || Value::known(F::from(valid as u64)),
                        )?;
                    }

                    all_bytes_rlc_acc = all_bytes_rlc_acc
                        .zip(keccak_input_rand)
                        .map(|(acc, rand)| acc * rand + F::from(value.witness_byte as u64));
                    region.assign_advice(
                        || format!("value: {}", offset + i),
                        self.input_bytes_rlc_acc,
                        offset + i as usize,
                        || all_bytes_rlc_acc,
                    )?;

                    input_value_eq_128_chip.assign(
                        &mut region,
                        offset + i as usize,
                        Value::known(F::from(value.witness_byte as u64)),
                        Value::known(F::from(128u64)),
                    )?;

                    for (chip, lhs, rhs) in [
                        (&input_value_gt_127_chip, 127, value.witness_byte),
                        (&input_value_gt_183_chip, 183, value.witness_byte),
                        (&input_value_gt_191_chip, 191, value.witness_byte),
                        (&input_value_gt_247_chip, 247, value.witness_byte),
                        (&input_value_lt_129_chip, value.witness_byte as usize, 129),
                        (&input_value_lt_184_chip, value.witness_byte as usize, 184),
                        (&input_value_lt_192_chip, value.witness_byte as usize, 192),
                        (&input_value_lt_248_chip, value.witness_byte as usize, 248),
                    ] {
                        chip.assign(
                            &mut region,
                            offset + i as usize,
                            F::from(lhs as u64),
                            F::from(rhs as u64),
                        )?;
                    }
                }

                let mut length_acc = 0u64;
                // fill txlist prefix
                for (i, value) in input_bytes.iter().take(txlist_prefix_len).enumerate() {
                    // value
                    let rlp_table = &self.rlp_table;
                    region.assign_advice(
                        || format!("value: {}", offset + i),
                        self.byte_value,
                        offset + i,
                        || Value::known(F::from(value.witness_byte as u64)),
                    )?;
                    let tag_rindex = txlist_prefix_len as u64 - i as u64;
                    region.assign_advice(
                        || format!("tag_rindex: {}", offset + i),
                        rlp_table.tag_rindex,
                        offset + i,
                        || Value::known(F::from(tag_rindex)),
                    )?;
                    region.assign_advice(
                        || format!("tag: {}", offset),
                        rlp_table.tag,
                        offset + i as usize,
                        || Value::known(F::from(RlpTxTag::TxListPrefix as u64)),
                    )?;
                    region.assign_advice(
                        || format!("tag_length: {}", offset + i),
                        self.tag_length,
                        offset + i,
                        || Value::known(F::from(txlist_prefix_len as u64)),
                    )?;
                    if i > 0 {
                        length_acc = length_acc * 256 + value.witness_byte as u64;
                        region.assign_advice(
                            || format!("length_acc: {}", offset + i),
                            self.length_acc,
                            offset + i,
                            || Value::known(F::from(length_acc)),
                        )?;
                    }

                    tag_chip.assign(&mut region, offset + i, &RlpTxTag::TxListPrefix)?;

                    for (chip, lhs, rhs) in [(&tag_index_cmp_1_chip, 1, tag_rindex as u64)] {
                        chip.assign(&mut region, offset + i, F::from(lhs as u64), F::from(rhs))?;
                    }

                    for (chip, lhs, rhs) in [(&tag_index_lt_10_chip, tag_rindex, 10)] {
                        chip.assign(
                            &mut region,
                            offset + i,
                            F::from(lhs as u64),
                            F::from(rhs as u64),
                        )?;
                    }
                }

                offset = txlist_prefix_len;

                for (signed_tx_idx, signed_tx) in signed_txs.iter().enumerate() {
                    if signed_tx.tx.hash != get_dummy_tx_hash(signed_tx.tx.chain_id) {
                        log::debug!(
                            "rlp circuit assign {}th tx at offset:{}, tx hash {:?}",
                            signed_tx_idx,
                            offset,
                            signed_tx.tx.hash
                        );
                    }
                    // tx hash (signed tx)
                    let mut all_bytes_rlc_acc = Value::known(F::zero());
                    let tx_hash_rows = signed_tx.gen_witness(challenges);
                    let has_placeholder =
                        signed_tx.tx.call_data.len() == 1 && signed_tx.tx.call_data[0] < 0x80;
                    let n_rows = if has_placeholder {
                        tx_hash_rows.len() - 1
                    } else {
                        tx_hash_rows.len()
                    };
                    for (idx, row) in tx_hash_rows
                        .iter()
                        // .chain(signed_tx.rlp_rows(keccak_input_rand).iter())
                        .enumerate()
                    {
                        log::trace!("offset {}, write row {}:\n\t{:?}", offset, idx, row);
                        let prev_row_placeholder = row.tag == RlpTxTag::Data && has_placeholder;
                        let cur_row_placeholder = row.tag == DataPrefix && has_placeholder;
                        // update value accumulator over the entire RLP encoding.
                        if !prev_row_placeholder {
                            // prev row has already accumulate the byte_value
                            all_bytes_rlc_acc = all_bytes_rlc_acc
                                .zip(keccak_input_rand)
                                .map(|(acc, rand)| acc * rand + F::from(row.value as u64));
                        }

                        // q_usable
                        region.assign_fixed(
                            || format!("q_usable: {}", offset),
                            self.q_usable,
                            offset,
                            || Value::known(F::one()),
                        )?;
                        // is_first
                        region.assign_advice(
                            || format!("assign is_first {}", offset),
                            self.is_first,
                            offset,
                            || Value::known(F::from((idx == 0) as u64)),
                        )?;
                        // advices
                        let rindex = (n_rows - row.index) as u64; // rindex decreases from n_rows - 1 to 0
                        let rlp_table = &self.rlp_table;
                        let is_simple_tag =
                            simple_tags.iter().filter(|tag| **tag == row.tag).count();
                        let is_prefix_tag = (row.tag == TxPrefix).into();
                        let is_dp_tag = (row.tag == DataPrefix).into();

                        for (name, column, value) in [
                            ("is_last", self.is_last, (row.index == n_rows).into()),
                            ("tx_id", rlp_table.tx_id, row.tx_id as u64),
                            ("tag", rlp_table.tag, (row.tag as u64)),
                            ("is_simple_tag", self.is_simple_tag, is_simple_tag as u64),
                            ("is_prefix_tag", self.is_prefix_tag, is_prefix_tag),
                            ("is_dp_tag", self.is_dp_tag, is_dp_tag),
                            ("tag_index", rlp_table.tag_rindex, (row.tag_rindex as u64)),
                            (
                                "tag_length_eq_one",
                                rlp_table.tag_length_eq_one,
                                (row.tag_length == 1) as u64,
                            ),
                            ("data_type", rlp_table.data_type, (row.data_type as u64)),
                            ("index", self.index, (row.index as u64)),
                            ("rindex", self.rindex, (rindex)),
                            ("placeholder", self.placeholder, cur_row_placeholder as u64),
                            ("value", self.byte_value, (row.value as u64)),
                            ("tag_length", self.tag_length, (row.tag_length as u64)),
                            ("length_acc", self.length_acc, (row.length_acc)),
                        ] {
                            region.assign_advice(
                                || format!("assign {} {}", name, offset),
                                column,
                                offset,
                                || Value::known(F::from(value)),
                            )?;
                        }
                        for (name, column, value) in [
                            (
                                "rlp_table::value_acc",
                                self.rlp_table.value_acc,
                                row.value_acc,
                            ),
                            (
                                "calldata_bytes_acc_rlc",
                                self.calldata_bytes_rlc_acc,
                                row.value_rlc_acc,
                            ),
                            (
                                "all_bytes_rlc_acc",
                                self.all_bytes_rlc_acc,
                                all_bytes_rlc_acc,
                            ),
                        ] {
                            region.assign_advice(
                                || format!("assign {} {}", name, offset),
                                column,
                                offset,
                                || value,
                            )?;
                        }

                        tag_chip.assign(&mut region, offset, &row.tag)?;

                        for (chip, lhs, rhs) in [
                            (&tag_index_cmp_1_chip, 1, row.tag_rindex as u64),
                            (
                                &tag_index_length_cmp_chip,
                                row.tag_rindex,
                                row.tag_length as u64,
                            ),
                            (&tag_length_cmp_1_chip, 1, row.tag_length as u64),
                            (&length_acc_cmp_0_chip, 0, row.length_acc),
                        ] {
                            chip.assign(&mut region, offset, F::from(lhs as u64), F::from(rhs))?;
                        }

                        value_eq_128_chip.assign(
                            &mut region,
                            offset,
                            Value::known(F::from(row.value as u64)),
                            Value::known(F::from(128u64)),
                        )?;

                        for (chip, lhs, rhs) in [
                            (&tag_index_lt_10_chip, row.tag_rindex, 10),
                            (&tag_index_lt_34_chip, row.tag_rindex, 34),
                        ] {
                            chip.assign(
                                &mut region,
                                offset,
                                F::from(lhs as u64),
                                F::from(rhs as u64),
                            )?;
                        }
                        for (chip, lhs, rhs) in [
                            (&value_gt_127_chip, 127, row.value),
                            (&value_gt_183_chip, 183, row.value),
                            (&value_gt_191_chip, 191, row.value),
                            (&value_gt_247_chip, 247, row.value),
                            (&value_lt_129_chip, row.value as usize, 129),
                            (&value_lt_184_chip, row.value as usize, 184),
                            (&value_lt_192_chip, row.value as usize, 192),
                            (&value_lt_248_chip, row.value as usize, 248),
                        ] {
                            chip.assign(
                                &mut region,
                                offset,
                                F::from(lhs as u64),
                                F::from(rhs as u64),
                            )?;
                        }

                        offset += 1;
                    }
                }

                // TODO: speed up the assignment of padding rows
                let padding_start_offset = offset;
                // end with padding rows.
                for offset in padding_start_offset..padding_end_offset {
                    self.assign_padding_rows(&mut region, offset)?;
                }

                Ok(())
            },
        )
    }

    fn assign_padding_rows(&self, region: &mut Region<'_, F>, offset: usize) -> Result<(), Error> {
        for column in [
            self.rlp_table.tx_id,
            self.rlp_table.tag_rindex,
            self.rlp_table.value_acc,
            self.rlp_table.data_type,
        ]
        .into_iter()
        {
            region.assign_advice(
                || format!("padding row, offset: {}", offset),
                column,
                offset,
                || Value::known(F::zero()),
            )?;
        }
        region.assign_advice(
            || format!("padding row, tag = Padding, offset: {}", offset),
            self.rlp_table.tag,
            offset,
            || {
                Value::known(F::from(
                    <RlpTxTag as Into<usize>>::into(RlpTxTag::Padding) as u64
                ))
            },
        )?;
        region.assign_fixed(
            || format!("padding row, offset: {}", offset),
            self.q_usable,
            offset,
            || Value::known(F::one()),
        )?;

        Ok(())
    }
}

/// Circuit configuration arguments
pub struct RlpCircuitConfigArgs<F: Field> {
    /// RlpTable
    rlp_table: RlpTable,
    /// Challenges
    challenges: Challenges<Expression<F>>,
}

impl<F: Field> SubCircuitConfig<F> for RlpCircuitConfig<F> {
    type ConfigArgs = RlpCircuitConfigArgs<F>;

    fn new(meta: &mut ConstraintSystem<F>, args: Self::ConfigArgs) -> Self {
        RlpCircuitConfig::configure(meta, &args.rlp_table, &args.challenges)
    }
}

/// Circuit to verify RLP encoding is correct
#[derive(Clone, Debug)]
pub struct RlpCircuit<F, RLP> {
    /// Rlp encoding inputs
    pub inputs: Vec<u8>,
    /// Max txs
    pub max_txs: usize,
    /// Size of the circuit
    pub size: usize,
    /// witness data
    pub witness: Vec<RlpWitnessByte>,
    /// decoded txs
    pub signed_txs: Vec<RLP>,
    /// rlp is valid
    pub rlp_valid: bool,
    /// marker
    pub _marker: PhantomData<F>,
}

impl<F: Field> RlpCircuit<F, SignedTransaction> {
    /// new RlpCircuit
    pub fn new(inputs: &Vec<u8>, k: usize, max_txs: usize) -> Self {
        let (inputs_witness, signed_txs, valid) = decode_tx_list_rlp_witness(inputs);
        log::info!(
            "input_witness.len() = {}, txs.len() = {}, valid = {}.",
            inputs_witness.len(),
            signed_txs.len(),
            valid,
        );
        Self {
            inputs: inputs.clone(),
            max_txs: max_txs,
            size: 1 << k,
            witness: inputs_witness,
            signed_txs: signed_txs.clone(),
            rlp_valid: valid,
            _marker: PhantomData,
        }
    }

    /// new RlpCircuit from forged witness
    pub fn new_from_fake_witness(
        inputs: &Vec<u8>,
        inputs_witness: &Vec<RlpWitnessByte>,
        signed_txs: Vec<SignedTransaction>,
        rlp_valid: bool,
        k: usize,
        max_txs: usize,
    ) -> Self {
        Self {
            inputs: inputs.clone(),
            max_txs: max_txs,
            size: 1 << k,
            witness: inputs_witness.clone(),
            signed_txs: signed_txs.clone(),
            rlp_valid: rlp_valid,
            _marker: PhantomData,
        }
    }
}

impl<F: Field, RLP> Default for RlpCircuit<F, RLP> {
    fn default() -> Self {
        Self {
            inputs: vec![],
            max_txs: 0,
            size: 0,
            witness: vec![],
            signed_txs: vec![],
            rlp_valid: false,
            _marker: PhantomData,
        }
    }
}

impl<F: Field> SubCircuit<F> for RlpCircuit<F, SignedTransaction> {
    type Config = RlpCircuitConfig<F>;

    fn new_from_block(block: &Block<F>) -> Self {
        let max_txs = block.circuits_params.max_txs;
        debug_assert!(block.txs.len() <= max_txs);

        let signed_txs = block
            .txs
            .iter()
            .zip(block.sigs.iter())
            .map(|(tx, sig)| SignedTransaction {
                tx: tx.clone(),
                signature: *sig,
            })
            .chain((block.txs.len()..max_txs).into_iter().map(|tx_id| {
                let mut padding_tx = Transaction::dummy(block.context.chain_id().as_u64());
                padding_tx.id = tx_id + 1;

                (&padding_tx).into()
            }))
            .collect::<Vec<_>>();

        // TODO: remove
        Self {
            inputs: vec![],
            max_txs: block.circuits_params.max_txs,
            // FIXME: this hard-coded size is used to pass unit test, we should use 1 << k instead.
            size: 1 << 18,
            witness: vec![],
            signed_txs: vec![],
            rlp_valid: false,
            _marker: Default::default(),
        }
    }

    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        config.assign(
            layouter,
            &self.witness,
            self.rlp_valid,
            &self.signed_txs,
            self.size,
            challenges,
        )
    }

    fn min_num_rows_block(block: &crate::witness::Block<F>) -> (usize, usize) {
        let rows = block
            .txs
            .iter()
            .zip(block.sigs.iter())
            .map(|(tx, sig)| {
                let mut len = rlp::encode(tx).len() + 1; // 1 for DataPrefix placeholder
                let signed_tx = SignedTransaction {
                    tx: tx.clone(),
                    signature: *sig,
                };
                len += rlp::encode(&signed_tx).len() + 1; // 1 for DataPrefix placeholder
                len
            })
            .count();
        (rows, std::cmp::max(1 << 18, rows))
    }
}

/// generate decode witness, the main problem is the placeholder,
/// others are vertically continous bytes.
/// so far there is only 1 place_holder type i.e., for a [x<0x80]
/// calldata bytes.
/// Now we ignore the this case for POC.
fn decode_tx_list_rlp_witness(
    rlp_bytes: &Vec<u8>,
) -> (Vec<RlpWitnessByte>, Vec<SignedTransaction>, bool) {
    if rlp_bytes[0] <= 0xF7 {
        // not a tx list
        log::debug!("invalid rlp txlist, starts with {}.", rlp_bytes[0]);
        (
            rlp_bytes
                .iter()
                .map(|b| RlpWitnessByte {
                    witness_byte: *b,
                    place_holder: false,
                })
                .collect(),
            vec![],
            false,
        )
    } else if let Ok(decode_txs) = rlp::Rlp::new(&rlp_bytes).as_list() {
        // decodable rlp
        log::debug!("decode_txs = {:?}", &decode_txs);
        let txs: Vec<eth_types::Transaction> = decode_txs;
        let signed_txs = txs
            .iter()
            .enumerate()
            .map(|(tx_id, eth_tx)| {
                let is_create = eth_tx.to.is_none();
                let sig = eth_types::Signature {
                    r: eth_tx.r,
                    s: eth_tx.s,
                    v: eth_tx.v.as_u64(),
                };
                let (rlp_unsigned, rlp_signed) = {
                    let mut legacy_tx = ethers_core::types::TransactionRequest::new()
                        .from(eth_tx.from)
                        .nonce(eth_tx.nonce)
                        .gas_price(eth_tx.gas_price.unwrap())
                        .gas(eth_tx.gas)
                        .value(eth_tx.value)
                        .data(eth_tx.input.clone())
                        .chain_id(eth_tx.chain_id.unwrap().as_u64());
                    if !is_create {
                        legacy_tx = legacy_tx.to(eth_tx.to.unwrap());
                    }

                    let unsigned = legacy_tx.rlp().to_vec();

                    let signed = legacy_tx.rlp_signed(&sig).to_vec();

                    (unsigned, signed)
                };
                let tx = Transaction {
                    block_number: 0,
                    id: tx_id,
                    hash: eth_tx.hash,
                    nonce: eth_tx.nonce.as_u64(),
                    gas: eth_tx.gas.as_u64(),
                    gas_price: eth_tx.gas_price.unwrap(),
                    caller_address: eth_tx.from,
                    callee_address: eth_tx.to,
                    is_create,
                    value: eth_tx.value,
                    call_data: eth_tx.input.to_vec(),
                    call_data_length: eth_tx.input.len(),
                    call_data_gas_cost: eth_tx
                        .input
                        .iter()
                        .fold(0, |acc, byte| acc + if *byte == 0 { 4 } else { 16 }),
                    chain_id: eth_tx.chain_id.unwrap().as_u64(),
                    rlp_unsigned,
                    rlp_signed,
                    v: sig.v,
                    r: sig.r,
                    s: sig.s,
                    calls: vec![],
                    steps: vec![],
                };
                //TODO: support this placeholder type
                assert!(tx.call_data_length != 1);
                SignedTransaction::from(&tx)
            })
            .collect();

        // write rlp bytes with place holder(TODO)
        let mut rlp_witness_bytes: Vec<RlpWitnessByte> = vec![];
        // TODO: place_holder in calldata
        for i in 0..rlp_bytes.len() {
            rlp_witness_bytes.push(RlpWitnessByte {
                witness_byte: rlp_bytes[i],
                place_holder: false,
            });
        }

        (rlp_witness_bytes, signed_txs, true)
    } else {
        // non decodable rlp with correct txlist header
        log::debug!(
            "non decodable rlp txlist, starts with {:?}.",
            &rlp_bytes[0..10]
        );
        let mut rlp_witness_bytes: Vec<RlpWitnessByte> = vec![];
        for i in 0..rlp_bytes.len() {
            rlp_witness_bytes.push(RlpWitnessByte {
                witness_byte: rlp_bytes[i],
                place_holder: false,
            });
        }

        (rlp_witness_bytes, vec![], false)
    }
}

impl<F: Field> Circuit<F> for RlpCircuit<F, SignedTransaction> {
    type Config = (RlpCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let rlp_table = RlpTable::construct(meta);
        let challenges = Challenges::construct(meta);
        let rand_exprs = challenges.exprs(meta);
        let config = RlpCircuitConfig::configure(meta, &rlp_table, &rand_exprs);

        (config, challenges)
    }

    fn synthesize(
        &self,
        (config, challenges): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let challenges = challenges.values(&layouter);
        config.assign(
            &mut layouter,
            self.witness.as_slice(),
            self.rlp_valid,
            &self.signed_txs,
            self.size,
            &challenges,
        )
    }
}

#[cfg(test)]
mod tests {
    use ark_std::{end_timer, start_timer};
    use ethers_core::utils::rlp;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    use std::io::Read;
    use std::marker::PhantomData;

    use super::Field;
    use super::{decode_tx_list_rlp_witness, RlpWitnessByte};
    use halo2_proofs::plonk::{create_proof, keygen_pk, keygen_vk, verify_proof};
    use halo2_proofs::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG, ParamsVerifierKZG};
    use halo2_proofs::poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK};
    use halo2_proofs::poly::kzg::strategy::SingleStrategy;
    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
    use halo2_proofs::{
        halo2curves::bn256::{Bn256, G1Affine},
        poly::commitment::ParamsProver,
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    };

    use mock::CORRECT_MOCK_TXS;

    use crate::evm_circuit::witness::SignedTransaction;

    use super::RlpCircuit;

    fn verify_normal_rlp_circuit<F: Field>(
        k: u32,
        inputs: Vec<u8>,
        max_txs: usize,
        success: bool,
        expected_txs_len: usize,
        expected_rlp_valid: bool,
    ) where
        RlpCircuit<F, SignedTransaction>: halo2_proofs::plonk::Circuit<Fr>,
    {
        let circuit: RlpCircuit<F, SignedTransaction> =
            RlpCircuit::<F, SignedTransaction>::new(&inputs, k as usize, max_txs);

        assert_eq!(expected_txs_len, circuit.signed_txs.len());
        assert_eq!(expected_rlp_valid, circuit.rlp_valid);

        const NUM_BLINDING_ROWS: usize = 8;
        let instance = vec![];
        let prover = MockProver::<F>::run(k, &circuit, instance).unwrap();
        let err = prover.verify_par();
        let print_failures = true;
        if err.is_err() && print_failures {
            if let Some(e) = err.err() {
                for s in e.iter() {
                    println!("{}", s);
                }
            }
        }
        let err = prover.verify_par();
        assert_eq!(err.is_ok(), success);
    }

    fn verify_rlp_circuit_with_fake_witness<F: Field>(
        k: u32,
        max_txs: usize,
        inputs: Vec<u8>,
        inputs_witness: &Vec<RlpWitnessByte>,
        signed_txs: Vec<SignedTransaction>,
        rlp_valid: bool,
        success: bool,
    ) where
        RlpCircuit<F, SignedTransaction>: halo2_proofs::plonk::Circuit<Fr>,
    {
        let circuit: RlpCircuit<F, SignedTransaction> =
            RlpCircuit::<F, SignedTransaction>::new_from_fake_witness(
                &inputs,
                inputs_witness,
                signed_txs,
                rlp_valid,
                k as usize,
                max_txs,
            );

        const NUM_BLINDING_ROWS: usize = 8;
        let instance = vec![];
        let prover = MockProver::<F>::run(k, &circuit, instance).unwrap();
        let err = prover.verify_par();
        let print_failures = true;
        if err.is_err() && print_failures {
            if let Some(e) = err.err() {
                for s in e.iter() {
                    println!("{}", s);
                }
            }
        }
        let err = prover.verify_par();
        assert_eq!(err.is_ok(), success);
    }

    fn branch_rlp<F: Field>(k: u32, inputs: Vec<u8>, max_txs: usize)
    where
        RlpCircuit<F, SignedTransaction>: halo2_proofs::plonk::Circuit<Fr>,
    {
        let circuit: RlpCircuit<F, SignedTransaction> =
            RlpCircuit::<F, SignedTransaction>::new(&inputs, k as usize, max_txs);

        const NUM_BLINDING_ROWS: usize = 8;
        let mut rng = ChaCha20Rng::seed_from_u64(42);

        let general_params = ParamsKZG::<Bn256>::setup(k as u32, &mut rng);
        let verifier_params: ParamsVerifierKZG<Bn256> = general_params.verifier_params().clone();

        // Initialize the proving key
        let vk = keygen_vk(&general_params, &circuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(&general_params, vk, &circuit).expect("keygen_pk should not fail");
        // Create a proof
        let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);

        // Bench proof generation time
        let proof_message = format!("{} {} with degree = {}", "gen proof of", "rlp circuit", k);
        let start2 = start_timer!(|| proof_message);
        create_proof::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            ChaCha20Rng,
            Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
            RlpCircuit<F, SignedTransaction>,
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
        let start3 = start_timer!(|| format!("{} {}", 1, "rlp verify"));
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

    // #[test]
    // fn rlp_circuit_tx_1() {
    //     verify_txs::<Fr>(8, vec![CORRECT_MOCK_TXS[0].clone().into()], 1,
    // true);     verify_txs::<Fr>(8,
    // vec![CORRECT_MOCK_TXS[4].clone().into()], 1, true);

    //     // test against the case in which tx.data has only one byte and is
    //     // less than 0x80
    //     let mut mock_tx = CORRECT_MOCK_TXS[0].clone();
    //     mock_tx.input(vec![0x3f].into());
    //     verify_txs::<Fr>(8, vec![mock_tx.into()], 1, true);
    // }

    #[test]
    fn rlp_circuit_tx_empty() {
        let txs: Vec<SignedTransaction> = vec![];
        let inputs = rlp::encode_list(&txs).into();
        verify_normal_rlp_circuit::<Fr>(8, inputs, 10, true, 0, false);
    }

    #[test]
    fn rlp_circuit_tx_2() {
        let txs: Vec<SignedTransaction> = vec![CORRECT_MOCK_TXS[6].clone().into()];
        let inputs = rlp::encode_list(&txs);
        verify_normal_rlp_circuit::<Fr>(8, inputs.into(), 2, true, 1, true);
    }

    #[test]
    fn rlp_circuit_tx_3() {
        let txs: Vec<SignedTransaction> = vec![CORRECT_MOCK_TXS[2].clone().into()];
        let inputs = rlp::encode_list(&txs);
        verify_normal_rlp_circuit::<Fr>(20, inputs.into(), 50, true, 1, true);
    }

    #[test]
    fn rlp_circuit_multi_txs() {
        let txs: Vec<SignedTransaction> = vec![
            CORRECT_MOCK_TXS[0].clone().into(),
            CORRECT_MOCK_TXS[1].clone().into(),
            CORRECT_MOCK_TXS[2].clone().into(),
        ];
        let inputs = rlp::encode_list(&txs).into();

        verify_normal_rlp_circuit::<Fr>(10, inputs, 5, true, 3, true);
    }

    #[test]
    fn rlp_circuit_tx_invalid_prefix_to_empty() {
        let txs: Vec<SignedTransaction> = vec![];
        let mut inputs: Vec<u8> = rlp::encode_list(&txs).into();
        inputs[0] = 0xC2;
        verify_normal_rlp_circuit::<Fr>(8, inputs, 10, true, 0, false);

        let txs: Vec<SignedTransaction> = vec![CORRECT_MOCK_TXS[0].clone().into()];
        let mut inputs: Vec<u8> = rlp::encode_list(&txs).into();
        inputs[0] = 0xC8;
        verify_normal_rlp_circuit::<Fr>(8, inputs, 10, true, 0, false);
    }

    /// field     pos prefix data
    /// array     00  f8     6f
    /// tx prefix 02  f8     6d
    /// nonce     04  82     1234
    /// gas price 07  86     100000000000
    /// gas limit 0e  83     0f4240
    /// to        12  94     0000000000000000000000000000000000000000
    /// value     27  83     054321
    /// data      2b  80     N/A
    /// sign_v    2c  82     0a98
    /// sign_r    2f  a0     a8193..{32bytes}..cf23
    /// sign_s    50  a0     409f8..{32bytes}..dc01
    /// padding   71  00     00

    #[test]
    fn rlp_circuit_tx_invalid_field() {
        let txs: Vec<SignedTransaction> = vec![CORRECT_MOCK_TXS[6].clone().into()];
        let inputs: Vec<u8> = rlp::encode_list(&txs).into();
        let mut invalid_inputs = vec![0; inputs.len()];

        invalid_inputs[..].copy_from_slice(inputs.as_slice());
        invalid_inputs[2] = 0xC2;
        verify_normal_rlp_circuit::<Fr>(8, invalid_inputs.clone(), 10, true, 0, false);

        invalid_inputs[..].copy_from_slice(inputs.as_slice());
        invalid_inputs[4] = 0x12;
        verify_normal_rlp_circuit::<Fr>(8, invalid_inputs.clone(), 10, true, 0, false);

        // invalid_inputs[..].copy_from_slice(inputs.as_slice());
        // invalid_inputs[50] = 0xa1;
        // verify_normal_rlp_circuit::<Fr>(8, invalid_inputs.clone(), 10, true,
        // 0, false);
    }

    #[test]
    fn rlp_circuit_tx_wrong_flag_for_empty_txs() {
        let txs: Vec<SignedTransaction> = vec![];
        let inputs = rlp::encode_list(&txs).into();
        let (inputs_witness, signed_txs, valid_and_not_empty) = decode_tx_list_rlp_witness(&inputs);
        assert!(valid_and_not_empty == false);
        verify_rlp_circuit_with_fake_witness::<Fr>(
            8,
            10,
            inputs,
            &inputs_witness,
            signed_txs,
            true, // fake witness
            false,
        );
    }

    #[test]
    fn rlp_circuit_tx_wrong_flag_for_single_tx() {
        let txs: Vec<SignedTransaction> = vec![CORRECT_MOCK_TXS[6].clone().into()];
        let inputs = rlp::encode_list(&txs).into();
        let (inputs_witness, signed_txs, valid_and_not_empty) = decode_tx_list_rlp_witness(&inputs);
        assert!(valid_and_not_empty == true);

        let mut invalid_inputs = vec![
            RlpWitnessByte {
                witness_byte: 0,
                place_holder: false
            };
            inputs.len()
        ];

        invalid_inputs[..].copy_from_slice(inputs_witness.as_slice());
        invalid_inputs[2] = RlpWitnessByte {
            witness_byte: 0xC2,
            place_holder: false,
        };

        verify_rlp_circuit_with_fake_witness::<Fr>(
            8,
            10,
            inputs,
            &invalid_inputs,
            signed_txs,
            true,
            false,
        );
    }}

#[cfg(test)]
mod rlp_test {
    use ethers_core::utils::rlp;
    use hex;

    use crate::witness::SignedTransaction;

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
}
