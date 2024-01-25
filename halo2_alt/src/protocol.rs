use crate::util::chain;
use std::{fmt::Debug, ops::Range};

mod expression;

pub(crate) use crate::protocol::expression::{Expression, PolynomialRef, Query};

#[derive(Clone, Debug)]
pub struct Protocol<F> {
    pub k: usize,
    pub num_preprocessed_polys: usize,
    pub num_instance_polys: usize,
    pub phases: Vec<(usize, usize)>,
    pub constraints: Vec<Expression<F>>,
}

impl<F> Protocol<F> {
    pub(crate) fn assert_valid(&self)
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

    pub(crate) fn num_phases(&self) -> usize {
        self.phases.len()
    }

    pub(crate) fn num_advice_polys(&self) -> usize {
        self.phases.iter().map(|(n, _)| n).sum()
    }

    pub(crate) fn num_challenges(&self) -> usize {
        self.phases.iter().map(|(_, n)| n).sum()
    }

    pub(crate) fn num_opaque_polys(&self) -> usize {
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

    pub fn n(&self) -> usize {
        1 << self.k
    }

    pub fn degree(&self) -> usize {
        self.constraints
            .iter()
            .map(Expression::degree)
            .max()
            .unwrap_or_default()
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
