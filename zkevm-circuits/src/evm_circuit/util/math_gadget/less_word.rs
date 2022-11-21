use super::CachedRegion;
use crate::{
    evm_circuit::{
        util::math_gadget::*,
        util::{self, constraint_builder::ConstraintBuilder, from_bytes, split_u256},
    },
    util::Expr,
};
use eth_types::{Field, ToLittleEndian, Word};
use halo2_proofs::plonk::{Error, Expression};

/// Returns `1` when `lhs < rhs`, and returns `0` otherwise.
/// lhs and rhs are both 256-bit word.
#[derive(Clone, Debug)]
pub struct LtWordGadget<F> {
    comparison_hi: ComparisonGadget<F, 16>,
    lt_lo: LtGadget<F, 16>,
}

impl<F: Field> LtWordGadget<F> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        lhs: &util::Word<F>,
        rhs: &util::Word<F>,
    ) -> Self {
        let comparison_hi = ComparisonGadget::construct(
            cb,
            from_bytes::expr(&lhs.cells[16..]),
            from_bytes::expr(&rhs.cells[16..]),
        );
        let lt_lo = LtGadget::construct(
            cb,
            from_bytes::expr(&lhs.cells[..16]),
            from_bytes::expr(&rhs.cells[..16]),
        );
        Self {
            comparison_hi,
            lt_lo,
        }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        let (hi_lt, hi_eq) = self.comparison_hi.expr();
        hi_lt + hi_eq * self.lt_lo.expr()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        lhs: Word,
        rhs: Word,
    ) -> Result<(), Error> {
        let (lhs_lo, lhs_hi) = split_u256(&lhs);
        let (rhs_lo, rhs_hi) = split_u256(&rhs);
        self.comparison_hi.assign(
            region,
            offset,
            F::from_u128(lhs_hi.as_u128()),
            F::from_u128(rhs_hi.as_u128()),
        )?;
        self.lt_lo.assign(
            region,
            offset,
            F::from_u128(lhs_lo.as_u128()),
            F::from_u128(rhs_lo.as_u128()),
        )?;
        Ok(())
    }
}

mod tests {
    use super::util::math_gadget::tests::*;
    use super::*;
    use eth_types::Word;
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::plonk::Error;

    #[test]
    fn test_ltword() {
        #[derive(Clone)]
        /// a < b
        struct LtWordTestContainer<F> {
            ltword_gadget: LtWordGadget<F>,
            a: util::Word<F>,
            b: util::Word<F>,
        }

        impl<F: Field> MathGadgetContainer<F> for LtWordTestContainer<F> {
            const NAME: &'static str = "LtWordGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let a = cb.query_word();
                let b = cb.query_word();
                let ltword_gadget = LtWordGadget::<F>::construct(cb, &a, &b);
                cb.require_equal("a < b", ltword_gadget.expr(), 1.expr());
                LtWordTestContainer {
                    ltword_gadget,
                    a,
                    b,
                }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let a = input_words[0];
                let b = input_words[1];
                let offset = 0;

                self.a.assign(region, offset, Some(a.to_le_bytes()))?;
                self.b.assign(region, offset, Some(b.to_le_bytes()))?;
                self.ltword_gadget.assign(region, 0, a, b)?;

                Ok(())
            }
        }

        test_math_gadget_container::<Fr, LtWordTestContainer<Fr>>(
            vec![Word::from(0), Word::from(1)],
            true,
        );

        test_math_gadget_container::<Fr, LtWordTestContainer<Fr>>(
            vec![Word::from(1), Word::MAX],
            true,
        );

        test_math_gadget_container::<Fr, LtWordTestContainer<Fr>>(
            vec![Word::from(1), Word::from(0)],
            false,
        );

        test_math_gadget_container::<Fr, LtWordTestContainer<Fr>>(
            vec![Word::MAX, Word::MAX],
            false,
        );
    }
}
