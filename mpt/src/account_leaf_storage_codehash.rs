use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::range_lookups,
    mpt::FixedTableTag,
    param::{HASH_WIDTH, KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH},
};

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafStorageCodehashConfig {}

// Verifies the hash of a leaf is in the parent branch.
pub(crate) struct AccountLeafStorageCodehashChip<F> {
    config: AccountLeafStorageCodehashConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafStorageCodehashChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        inter_root: Column<Advice>,
        q_not_first: Column<Fixed>,
        not_first_level: Column<Advice>,
        is_account_leaf_storage_codehash: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        c_advices: [Column<Advice>; HASH_WIDTH],
        acc_r: F,
        acc: Column<Advice>,
        acc_mult: Column<Advice>,
        fixed_table: [Column<Fixed>; 3],
        s_mod_node_hash_rlc: Column<Advice>,
        c_mod_node_hash_rlc: Column<Advice>,
        sel1: Column<Advice>,
        sel2: Column<Advice>,
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
        is_storage_mod: Column<Advice>,
        is_nonce_mod: Column<Advice>,
        is_balance_mod: Column<Advice>,
        is_codehash_mod: Column<Advice>,
        is_s: bool,
    ) -> AccountLeafStorageCodehashConfig {
        let config = AccountLeafStorageCodehashConfig {};
        let one = Expression::Constant(F::one());

        // We don't need to check acc_mult because it's not used after this row.

        meta.create_gate("account leaf storage codehash", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let mut q_enable = q_not_first.clone()
                * meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

            let mut constraints = vec![];

            // We have storage length in s_rlp2 (which is 160 presenting 128 + 32).
            // We have storage hash in s_advices.
            // We have codehash length in c_rlp2 (which is 160 presenting 128 + 32).
            // We have codehash in c_advices.

            // Rows:
            // account leaf key
            // account leaf nonce balance S
            // account leaf nonce balance C
            // account leaf storage codeHash S
            // account leaf storage codeHash C

            let c160 = Expression::Constant(F::from(160));
            let rot = -2;
            let acc_prev = meta.query_advice(acc, Rotation(rot));
            let acc_mult_prev = meta.query_advice(acc_mult, Rotation(rot));
            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());
            constraints.push((
                "account leaf storage codehash s_rlp2",
                q_enable.clone() * (s_rlp2.clone() - c160.clone()),
            ));
            constraints.push((
                "account leaf storage codehash c_rlp2",
                q_enable.clone() * (c_rlp2.clone() - c160),
            ));

            let mut expr = acc_prev + s_rlp2 * acc_mult_prev.clone();

            let mut storage_root_rlc = Expression::Constant(F::zero());
            let mut curr_r = one.clone();
            for col in s_advices.iter() {
                let s = meta.query_advice(*col, Rotation::cur());
                storage_root_rlc = storage_root_rlc + s * curr_r.clone();
                curr_r = curr_r * acc_r;
            }
            let storage_root_stored = meta.query_advice(s_mod_node_hash_rlc, Rotation::cur());
            constraints.push((
                "storage root RLC",
                q_enable.clone() * (storage_root_rlc.clone() - storage_root_stored.clone()),
            ));

            expr = expr + storage_root_rlc * acc_mult_prev.clone() * acc_r;

            curr_r = curr_r * acc_mult_prev.clone() * acc_r;

            expr = expr + c_rlp2 * curr_r.clone();
            let old_curr_r = curr_r * acc_r;

            curr_r = one.clone();
            let mut codehash_rlc = Expression::Constant(F::zero());
            for col in c_advices.iter() {
                let c = meta.query_advice(*col, Rotation::cur());
                codehash_rlc = codehash_rlc + c * curr_r.clone();
                curr_r = curr_r * acc_r;
            }
            let codehash_stored = meta.query_advice(c_mod_node_hash_rlc, Rotation::cur());
            constraints.push((
                "codehash RLC",
                q_enable.clone() * (codehash_rlc.clone() - codehash_stored.clone()),
            ));

            if !is_s {
                let storage_root_s_from_prev =
                    meta.query_advice(s_mod_node_hash_rlc, Rotation::prev());
                let storage_root_s_from_cur = meta.query_advice(sel1, Rotation::cur());
                let codehash_s_from_prev = meta.query_advice(c_mod_node_hash_rlc, Rotation::prev());
                let codehash_s_from_cur = meta.query_advice(sel2, Rotation::cur());
                // We need correct previous storage root to enable lookup in storage codehash C
                // row:
                constraints.push((
                    "storage root prev RLC",
                    q_enable.clone()
                        * (storage_root_s_from_prev.clone() - storage_root_s_from_cur.clone()),
                ));
                // We need correct previous codehash to enable lookup in storage codehash C row:
                constraints.push((
                    "codehash prev RLC",
                    q_enable.clone() * (codehash_s_from_prev.clone() - codehash_s_from_cur.clone()),
                ));

                // Check there is only one modification at once:
                let is_storage_mod = meta.query_advice(is_storage_mod, Rotation::cur());
                let is_nonce_mod = meta.query_advice(is_nonce_mod, Rotation::cur());
                let is_balance_mod = meta.query_advice(is_balance_mod, Rotation::cur());
                let is_codehash_mod = meta.query_advice(is_codehash_mod, Rotation::cur());

                constraints.push((
                    "if nonce / balance / codehash mod: storage_root_s = storage_root_c",
                    q_enable.clone()
                        * (is_nonce_mod.clone() + is_balance_mod.clone() + is_codehash_mod.clone())
                        * (storage_root_s_from_cur.clone() - storage_root_stored.clone()),
                ));
                constraints.push((
                    "if nonce / balance / storage mod: codehash_s = codehash_c",
                    q_enable.clone()
                        * (is_nonce_mod.clone() + is_balance_mod.clone() + is_storage_mod.clone())
                        * (codehash_s_from_cur.clone() - codehash_stored.clone()),
                ));
            }

            expr = expr + codehash_rlc * old_curr_r;

            let acc = meta.query_advice(acc, Rotation::cur());
            constraints.push(("account leaf storage codehash acc", q_enable * (expr - acc)));

            constraints
        });

        // Check hash of a leaf to be state root when leaf without branch.
        // TODO: prepare test
        meta.lookup_any(
            "account first level leaf without branch - compared to root",
            |meta| {
                let mut constraints = vec![];
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let not_first_level = meta.query_advice(not_first_level, Rotation::cur());

                let mut is_account_leaf_storage_codehash =
                    meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

                let rlc = meta.query_advice(acc, Rotation::cur());
                let root = meta.query_advice(inter_root, Rotation::cur());

                constraints.push((
                    q_not_first.clone()
                        * is_account_leaf_storage_codehash.clone()
                        * (one.clone() - not_first_level.clone())
                        * rlc,
                    meta.query_fixed(keccak_table[0], Rotation::cur()),
                ));
                let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
                constraints.push((
                    q_not_first
                        * is_account_leaf_storage_codehash
                        * (one.clone() - not_first_level)
                        * root,
                    keccak_table_i,
                ));

                constraints
            },
        );

        // Check hash of a leaf.
        meta.lookup_any("account_leaf_storage_codehash: hash of a leaf", |meta| {
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());

            let mut is_account_leaf_storage_codehash =
                meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

            // TODO: test for account proof with only leaf (without branch)
            let mut leaf_without_branch = one.clone() - meta.query_fixed(q_not_first, Rotation(-3));
            if !is_s {
                leaf_without_branch = one.clone() - meta.query_fixed(q_not_first, Rotation(-4));
            }

            // Rotate into one of the branch rows (make sure the rotation will bring into
            // branch rows S as well as C row):
            let mut placeholder_leaf = meta.query_advice(sel1, Rotation(-7));
            if !is_s {
                placeholder_leaf = meta.query_advice(sel2, Rotation(-7));
            }

            // Note: accumulated in s (not in c) for c:
            let acc_s = meta.query_advice(acc, Rotation::cur());

            let mut constraints = vec![];
            constraints.push((
                not_first_level.clone()
                    * (one.clone() - leaf_without_branch.clone())
                    * (one.clone() - placeholder_leaf.clone())
                    * is_account_leaf_storage_codehash.clone()
                    * acc_s,
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            // Any rotation that lands into branch can be used instead of -17.
            let mut mod_node_hash_rlc_cur = meta.query_advice(s_mod_node_hash_rlc, Rotation(-17));
            if !is_s {
                mod_node_hash_rlc_cur = meta.query_advice(c_mod_node_hash_rlc, Rotation(-17));
            }
            let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
            constraints.push((
                not_first_level.clone()
                    * (one.clone() - leaf_without_branch.clone())
                    * (one.clone() - placeholder_leaf.clone())
                    * is_account_leaf_storage_codehash.clone()
                    * mod_node_hash_rlc_cur,
                keccak_table_i,
            ));

            constraints
        });

        let sel = |meta: &mut VirtualCells<F>| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let mut q_enable = q_not_first.clone()
                * meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

            q_enable
        };

        range_lookups(
            meta,
            sel.clone(),
            s_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            sel.clone(),
            c_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        // s_rlp1 and c_rlp1 not used
        range_lookups(
            meta,
            sel,
            [s_rlp2, c_rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        config
    }

    pub fn construct(config: AccountLeafStorageCodehashConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for AccountLeafStorageCodehashChip<F> {
    type Config = AccountLeafStorageCodehashConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
