//! Shared structures for Plonkish proof systems.

use halo2_proofs::{halo2curves::ff::WithSmallOrderMulGroup, poly::EvaluationDomain};

use crate::util::chain;
use std::{fmt::Debug, ops::Range};

mod expression;

pub use crate::protocol::expression::{Expression, PolynomialRef, Query};

/// `Protocol` holds minimal information of a Plonkish proof system.
#[derive(Clone, Debug)]
pub struct Protocol<F> {
    k: usize,
    num_preprocessed_polys: usize,
    num_instance_polys: usize,
    phases: Vec<(usize, usize)>,
    constraints: Vec<Expression<F>>,
}

impl<F> Protocol<F> {
    /// Returns `Protocol` from parts.
    ///
    /// # Panics
    ///
    /// It panics if given `constraints` contain any `PolynomialRef` out of bound.
    pub fn new(
        k: usize,
        num_preprocessed_polys: usize,
        num_instance_polys: usize,
        phases: Vec<(usize, usize)>,
        constraints: Vec<Expression<F>>,
    ) -> Self
    where
        F: Clone,
    {
        let protocol = Self {
            k,
            num_preprocessed_polys,
            num_instance_polys,
            phases,
            constraints,
        };
        protocol.assert_valid();
        protocol
    }

    /// Returns log2 size of polynomials.
    pub fn k(&self) -> usize {
        self.k
    }

    /// Returns size of polynomials.
    pub fn n(&self) -> usize {
        1 << self.k
    }

    /// Returns interaction phases containing `(num_advice_polys, num_challenges)` in each phase,
    /// where the former is number of advice polynomials sent from prover to verifier, the latter
    /// is number of challenges sent back from verifier to prover.
    pub fn phases(&self) -> &[(usize, usize)] {
        &self.phases
    }

    /// Returns constraints that need to be satisfied.
    pub fn constraints(&self) -> &[Expression<F>] {
        &self.constraints
    }

    /// Returns max degree among all constraints.
    pub fn max_constraint_degree(&self) -> usize {
        self.constraints
            .iter()
            .map(Expression::degree)
            .max()
            .unwrap_or_default()
    }

    /// Returns number of preprocessed polynomials.
    pub fn num_preprocessed_polys(&self) -> usize {
        self.num_preprocessed_polys
    }

    /// Returns number of instance polynomials.
    pub fn num_instance_polys(&self) -> usize {
        self.num_instance_polys
    }

    /// Returns number of interaction phases.
    pub fn num_phases(&self) -> usize {
        self.phases.len()
    }

    /// Returns number of advice polynomials in all phases.
    pub fn num_advice_polys(&self) -> usize {
        self.phases.iter().map(|(n, _)| n).sum()
    }

    /// Returns number of challenges in all phases.
    pub fn num_challenges(&self) -> usize {
        self.phases.iter().map(|(_, n)| n).sum()
    }

    /// Returns number of all polynomials.
    pub fn num_opaque_polys(&self) -> usize {
        self.num_preprocessed_polys + self.num_instance_polys + self.num_advice_polys()
    }

    pub(crate) fn poly_range(&self) -> PolynomialRange {
        let mut opaque_ranges = lens_to_cont_ranges(chain![
            [self.num_preprocessed_polys, self.num_instance_polys],
            self.phases.iter().map(|(n, _)| *n),
        ]);
        PolynomialRange {
            preprocessed: opaque_ranges.next().unwrap(),
            instance: opaque_ranges.next().unwrap(),
            advices: opaque_ranges.collect(),
            challenges: lens_to_cont_ranges(self.phases.iter().map(|(_, n)| *n)).collect(),
        }
    }

    fn assert_valid(&self)
    where
        F: Clone,
    {
        let num_challenges = self.num_challenges();
        let num_opaque_polys = self.num_opaque_polys();
        for constraint in self.constraints.iter() {
            constraint.evaluate(
                &|inner| match inner {
                    PolynomialRef::Challenge(idx) => assert!(idx < num_challenges),
                    PolynomialRef::Opaque(query) => assert!(query.index < num_opaque_polys),
                    _ => (),
                },
                &|_| (),
                &|_, _| (),
                &|_, _| (),
            );
        }
    }
}

impl<F: WithSmallOrderMulGroup<3>> Protocol<F> {
    pub(crate) fn domain(&self) -> EvaluationDomain<F> {
        EvaluationDomain::new(self.max_constraint_degree() as u32, self.k() as u32)
    }
}

pub(crate) struct PolynomialRange {
    pub(crate) preprocessed: Range<usize>,
    pub(crate) instance: Range<usize>,
    pub(crate) advices: Vec<Range<usize>>,
    pub(crate) challenges: Vec<Range<usize>>,
}

fn lens_to_cont_ranges(
    lens: impl IntoIterator<Item = usize>,
) -> impl Iterator<Item = Range<usize>> {
    lens.into_iter().scan(0, |state, len| {
        let range = *state..*state + len;
        *state += len;
        Some(range)
    })
}
