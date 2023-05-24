//! The rlp decoding tables implementation.

use crate::{
    rlp_decoder::{RlpDecodeTypeTag, RlpTxFieldTag, RlpTxTypeTag, MAX_BYTE_COLUMN_NUM},
    util::Challenges,
};
use eth_types::Field;
pub use halo2_proofs::halo2curves::{
    group::{
        ff::{Field as GroupField, PrimeField},
        prime::PrimeCurveAffine,
        Curve, Group, GroupEncoding,
    },
    secp256k1::{self, Secp256k1Affine, Secp256k1Compressed},
};
use halo2_proofs::{
    circuit::{Layouter, Region, Value},
    plonk::{Column, ConstraintSystem, Error, Fixed},
};

/// Rlp encoding types
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RlpDecodeRule {
    /// The Padding RLP encoding type is a single byte 0x00
    Padding,
    /// The RLP encoding type is a empty string, i.e., 0x80
    Empty,
    /// The RLP encoding type is a uint96
    Uint64,
    /// The RLP encoding type is a uint96
    Uint96,
    /// The RLP encoding type is a address 20bytes i.e., 0x94xxxx
    Address,
    /// The RLP encoding type is a hash string 32bytes, i.e., 0xa0xxx
    Bytes32,
    /// The RLP encoding type is a string which is upto 48k bytes
    Bytes48K,
    /// The RLP encoding empty list type
    EmptyList,
    /// The RLP encoding empty long list type, upto 16M, i.e., 0xF9FFFFFF
    LongList,
}

impl RlpDecodeRule {
    /// load the decode rult table, like.:
    /// | tx_type(legacy/1559) | field | rlp type | byte[0] | decodable |
    /// | legacy               | nonce | uint96   | 0x00    | false     |
    /// | legacy               | nonce | uint96   | 0x01    | true      |
    ///  ...
    /// | legacy               | signS | byte32   | 0xa0    | true      |
    /// | legacy               | signS | byte32   | 0xa1    | false     |
    ///  ...
    pub fn load<F: Field>(
        &self,
        tx_type: &RlpTxTypeTag,
        tx_field_tag: &RlpTxFieldTag,
        table: &RlpDecoderTable,
        region: &mut Region<'_, F>,
        offset: usize,
    ) -> Result<(), Error> {
        let rule_table_rows = {
            (0..256u64)
                .map(|i| {
                    let (rlp_type, decodable) = match self {
                        RlpDecodeRule::Padding => (RlpDecodeTypeTag::DoNothing, true),
                        RlpDecodeRule::Empty => match i {
                            0x80 => (RlpDecodeTypeTag::SingleByte, true),
                            _ => (RlpDecodeTypeTag::DoNothing, false),
                        },
                        RlpDecodeRule::Uint64 => match i {
                            // 0 is error: non-canonical integer (leading zero bytes) for uint64
                            1..=0x80 => (RlpDecodeTypeTag::SingleByte, true),
                            0x81..=0x88 => (RlpDecodeTypeTag::ShortString, true),
                            _ => (RlpDecodeTypeTag::DoNothing, false),
                        },
                        RlpDecodeRule::Uint96 => match i {
                            // 0 is error: non-canonical integer (leading zero bytes) for uint96
                            1..=0x80 => (RlpDecodeTypeTag::SingleByte, true),
                            0x81..=0x8c => (RlpDecodeTypeTag::ShortString, true),
                            _ => (RlpDecodeTypeTag::DoNothing, false),
                        },
                        RlpDecodeRule::Address => match i {
                            0x94 => (RlpDecodeTypeTag::ShortString, true),
                            _ => (RlpDecodeTypeTag::DoNothing, false),
                        },
                        RlpDecodeRule::Bytes32 => match i {
                            // TODO: what if sig is less then 32 bytes?
                            0xa0 => (RlpDecodeTypeTag::ShortString, true),
                            _ => (RlpDecodeTypeTag::DoNothing, false),
                        },
                        RlpDecodeRule::Bytes48K => match i {
                            0 => (RlpDecodeTypeTag::SingleByte, true),        // 0x00
                            1..=0x80 => (RlpDecodeTypeTag::SingleByte, true), // 0x01..=0x80
                            0x81..=0xb7 => (RlpDecodeTypeTag::ShortString, true),
                            0xb8 => (RlpDecodeTypeTag::LongString1, true),
                            0xb9 => (RlpDecodeTypeTag::LongString2, true),
                            0xba => (RlpDecodeTypeTag::LongString3, true),
                            _ => (RlpDecodeTypeTag::DoNothing, false),
                        },
                        RlpDecodeRule::EmptyList => match i {
                            0xc0 => (RlpDecodeTypeTag::ShortString, false),
                            _ => (RlpDecodeTypeTag::DoNothing, false),
                        },
                        RlpDecodeRule::LongList => match i {
                            0xf8 => (RlpDecodeTypeTag::LongList1, true),
                            0xf9 => (RlpDecodeTypeTag::LongList2, true),
                            0xfa => (RlpDecodeTypeTag::LongList3, true),
                            _ => (RlpDecodeTypeTag::DoNothing, false),
                        },
                    };
                    [
                        *tx_type as u64,
                        *tx_field_tag as u64,
                        rlp_type as u64,
                        i,
                        decodable as u64,
                    ]
                })
                .collect::<Vec<[u64; 5]>>()
        };

        let mut offset = offset;
        for rule_table_row in rule_table_rows.iter() {
            // println!("rule_table_row: {:?} @ offset {}.", rule_table_row, offset);
            rule_table_row
                .iter()
                .zip([
                    table.tx_type,
                    table.tx_field_tag,
                    table.rlp_type,
                    table.byte_0,
                    table.decodable,
                ])
                .try_for_each(|(value, col)| {
                    region
                        .assign_fixed(
                            || "load rlp decoder table",
                            col,
                            offset,
                            || Value::known(F::from(*value)),
                        )
                        .map(|_| ())
                })?;
            offset += 1;
        }
        Ok(())
    }
}

/// Table that contains the fields of all possible RLP decodable fields
#[derive(Clone, Debug)]
pub struct RlpDecoderTable {
    /// The tx type tag
    pub tx_type: Column<Fixed>,
    /// The tx field tag
    pub tx_field_tag: Column<Fixed>,
    /// The RLP type
    pub rlp_type: Column<Fixed>,
    /// The first byte of the RLP encoded field
    pub byte_0: Column<Fixed>,
    /// Whether the field is decodable
    pub decodable: Column<Fixed>,
    /// The length of the field
    pub length: Column<Fixed>,
}

impl RlpDecoderTable {
    /// Construct a new RlpDecoderTable
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            tx_type: meta.fixed_column(),
            tx_field_tag: meta.fixed_column(),
            rlp_type: meta.fixed_column(),
            byte_0: meta.fixed_column(),
            decodable: meta.fixed_column(),
            length: meta.fixed_column(),
        }
    }

    /// Get the row num of the RLP decoding table
    pub fn table_size() -> usize {
        (RlpDecodeRule::LongList as usize + 1) * 256
    }

    /// Assign the values of the table to the circuit
    pub fn load<F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        challenges: &Challenges<Value<F>>,
    ) -> Result<(), Error> {
        // make a list with all member of rlpTxFieldTag literally
        let rlp_tx_field_decode_rules: Vec<(RlpTxTypeTag, RlpTxFieldTag, RlpDecodeRule)> = vec![
            (
                RlpTxTypeTag::TxLegacyType,
                RlpTxFieldTag::TxListRlpHeader,
                RlpDecodeRule::LongList,
            ),
            (
                RlpTxTypeTag::TxLegacyType,
                RlpTxFieldTag::TxRlpHeader,
                RlpDecodeRule::LongList,
            ),
            (
                RlpTxTypeTag::TxLegacyType,
                RlpTxFieldTag::Nonce,
                RlpDecodeRule::Uint96,
            ),
            (
                RlpTxTypeTag::TxLegacyType,
                RlpTxFieldTag::GasPrice,
                RlpDecodeRule::Uint96,
            ),
            (
                RlpTxTypeTag::TxLegacyType,
                RlpTxFieldTag::Gas,
                RlpDecodeRule::Uint96,
            ),
            (
                RlpTxTypeTag::TxLegacyType,
                RlpTxFieldTag::To,
                RlpDecodeRule::Address,
            ),
            (
                RlpTxTypeTag::TxLegacyType,
                RlpTxFieldTag::To,
                RlpDecodeRule::Empty,
            ),
            (
                RlpTxTypeTag::TxLegacyType,
                RlpTxFieldTag::Value,
                RlpDecodeRule::Uint96,
            ),
            (
                RlpTxTypeTag::TxLegacyType,
                RlpTxFieldTag::Data,
                RlpDecodeRule::Bytes48K,
            ),
            (
                RlpTxTypeTag::TxLegacyType,
                RlpTxFieldTag::SignV,
                RlpDecodeRule::Uint96,
            ),
            (
                RlpTxTypeTag::TxLegacyType,
                RlpTxFieldTag::SignR,
                RlpDecodeRule::Bytes32,
            ),
            (
                RlpTxTypeTag::TxLegacyType,
                RlpTxFieldTag::SignS,
                RlpDecodeRule::Bytes48K,
            ),
            (
                RlpTxTypeTag::TxLegacyType,
                RlpTxFieldTag::Padding,
                RlpDecodeRule::Padding,
            ),
        ];

        layouter.assign_region(
            || "load rlp decoder table",
            |mut region| {
                let mut offset = 0;
                for (tx_type, tx_field_tag, decode_rule) in rlp_tx_field_decode_rules.iter() {
                    decode_rule.load(tx_type, tx_field_tag, self, &mut region, offset)?;
                    offset += 256;
                }
                Ok(())
            },
        )?;

        Ok(())
    }
}

/// Table that contains the fields of possible state transitions
#[derive(Clone, Debug)]
pub struct TxFieldSwitchTable {
    /// The current tx field
    pub current_tx_field: Column<Fixed>,
    /// The next tx field
    pub next_tx_field: Column<Fixed>,
}

static TX_FIELD_TRANSITION_TABLE: [(RlpTxFieldTag, RlpTxFieldTag); 14] = [
    (RlpTxFieldTag::TxListRlpHeader, RlpTxFieldTag::TxRlpHeader),
    (RlpTxFieldTag::TxRlpHeader, RlpTxFieldTag::Nonce),
    (RlpTxFieldTag::Nonce, RlpTxFieldTag::GasPrice),
    (RlpTxFieldTag::GasPrice, RlpTxFieldTag::Gas),
    (RlpTxFieldTag::Gas, RlpTxFieldTag::To),
    (RlpTxFieldTag::To, RlpTxFieldTag::Value),
    (RlpTxFieldTag::Value, RlpTxFieldTag::Data),
    (RlpTxFieldTag::Data, RlpTxFieldTag::Data),
    (RlpTxFieldTag::Data, RlpTxFieldTag::SignV),
    (RlpTxFieldTag::SignV, RlpTxFieldTag::SignR),
    (RlpTxFieldTag::SignR, RlpTxFieldTag::SignS),
    (RlpTxFieldTag::SignS, RlpTxFieldTag::TxRlpHeader),
    (RlpTxFieldTag::SignS, RlpTxFieldTag::Padding),
    (RlpTxFieldTag::Padding, RlpTxFieldTag::Padding),
    // TODO: add 1559 fields
];

impl TxFieldSwitchTable {
    /// Construct a new RlpDecoderTable
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            current_tx_field: meta.fixed_column(),
            next_tx_field: meta.fixed_column(),
        }
    }

    /// Get the row num of the table
    pub fn table_size() -> usize {
        TX_FIELD_TRANSITION_TABLE.len()
    }

    /// Assign the values of the table to the circuit
    pub fn load<F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        challenges: &Challenges<Value<F>>,
    ) -> Result<(), Error> {
        // make a list with all member of rlpTxFieldTag literally
        let tx_field_trans_table = &TX_FIELD_TRANSITION_TABLE;

        layouter.assign_region(
            || "load rlp decoder table",
            |mut region| {
                let mut offset = 0;
                tx_field_trans_table
                    .iter()
                    .try_for_each(|(current_tx_field, next_tx_field)| {
                        region.assign_fixed(
                            || "current tx field",
                            self.current_tx_field,
                            offset,
                            || Value::known(F::from(*current_tx_field as u64)),
                        )?;
                        region.assign_fixed(
                            || "next tx field",
                            self.next_tx_field,
                            offset,
                            || Value::known(F::from(*next_tx_field as u64)),
                        )?;
                        offset += 1;
                        Ok(())
                    })
            },
        )
    }
}

/// Table that contains the pow of randomness
#[derive(Clone, Debug)]
pub struct RMultPowTable {
    /// pow number
    pub length: Column<Fixed>,
    /// pow of randomness
    pub r_mult: Column<Fixed>,
}

impl RMultPowTable {
    /// Construct a new RlpDecoderTable
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            length: meta.fixed_column(),
            r_mult: meta.fixed_column(),
        }
    }

    /// Get the row num of the table
    pub fn table_size() -> usize {
        MAX_BYTE_COLUMN_NUM
    }

    /// Assign the values of the table to the circuit
    pub fn load<F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        challenges: &Challenges<Value<F>>,
    ) -> Result<(), Error> {
        let mut randomness = F::zero();
        challenges.keccak_input().map(|r| randomness = r);

        (0..=MAX_BYTE_COLUMN_NUM).try_for_each(|i| {
            layouter.assign_region(
                || "load rlp r_mult table",
                |mut region| {
                    region.assign_fixed(
                        || "pow",
                        self.length,
                        i,
                        || Value::known(F::from(i as u64)),
                    )?;
                    region.assign_fixed(
                        || "r_mult",
                        self.r_mult,
                        i,
                        || Value::known(randomness.pow(&[i as u64, 0, 0, 0])),
                    )?;
                    Ok(())
                },
            )
        })?;
        Ok(())
    }
}
