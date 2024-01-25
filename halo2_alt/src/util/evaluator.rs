use crate::{
    protocol::{Expression, PolynomialRef, Query},
    util::{izip, powers, squares},
};
use halo2_proofs::{
    arithmetic::parallelize,
    halo2curves::ff::{BatchInvert, Field, WithSmallOrderMulGroup},
    poly::{Coeff, EvaluationDomain, ExtendedLagrangeCoeff, Polynomial, Rotation},
};
use std::{
    fmt::Debug,
    ops::{Deref, Index},
};

#[derive(Clone, Debug)]
pub(crate) struct Evaluator<F: Field> {
    n: usize,
    domain: EvaluationDomain<F>,
    magnification: i32,
    extended_n: i32,
    reg: ExpressionRegistry<F>,
    vanishing_invs: Vec<F>,
}

impl<F: WithSmallOrderMulGroup<3>> Evaluator<F> {
    pub(crate) fn new(k: usize, constraint: &Expression<F>) -> Self {
        let domain = EvaluationDomain::<F>::new(constraint.degree() as u32, k as u32);
        let diff_k = domain.extended_k() - domain.k();
        let magnification = 1 << diff_k;
        let extended_n = 1 << domain.extended_k();
        let reg = ExpressionRegistry::new([constraint]);

        let vanishing_invs = {
            let zeta_to_n = [F::ZETA, F::ZETA.square()][(domain.k() & 1) as usize];
            let extended_omega_to_n = squares(domain.get_extended_omega()).nth(k).unwrap();
            let mut vanishing_invs = powers(extended_omega_to_n)
                .map(|value| zeta_to_n * value - F::ONE)
                .take(magnification)
                .collect::<Vec<_>>();
            vanishing_invs.batch_invert();
            vanishing_invs
        };

        Self {
            n: 1 << k,
            domain,
            magnification: magnification as i32,
            extended_n,
            reg,
            vanishing_invs,
        }
    }

    pub(crate) fn evaluate_quotient(
        &self,
        polys: &[&Polynomial<F, ExtendedLagrangeCoeff>],
        challenges: &[F],
    ) -> Polynomial<F, Coeff> {
        let reg = &self.reg;
        let polys = polys
            .iter()
            .map(|poly| PolynomialView::new(self.domain.extended_k() as usize, poly))
            .collect::<Vec<_>>();
        let extended_omega = self.domain.get_extended_omega();

        let mut q = self.domain.empty_extended();
        parallelize(&mut q[..], |q, start| {
            let mut buf = reg.buf(challenges);
            if reg.has_identity {
                buf[reg.offsets.identity()] = F::ZETA * extended_omega.pow([start as u64]);
            }

            izip!(start.., q).for_each(|(row, q)| {
                izip!(&mut buf[reg.offsets().polys()..], reg.polys()).for_each(|(value, query)| {
                    *value = polys[query.index][self.rotated_row(row, query.rotation)];
                });
                izip!(reg.calcs(), reg.offsets().calcs()..)
                    .for_each(|(calc, idx)| buf[idx] = calc.calculate(&buf));

                *q = *buf.last().unwrap() * self.vanishing_inv(row);

                if reg.has_identity {
                    buf[reg.offsets.identity()] *= extended_omega;
                }
            });
        });

        let mut q = self.domain.extended_to_coeff(q);
        q.truncate(self.domain.get_quotient_poly_degree() * self.n);
        Polynomial::new(q)
    }

    fn vanishing_inv(&self, row: usize) -> &F {
        &self.vanishing_invs[row % self.vanishing_invs.len()]
    }

    fn rotated_row(&self, row: usize, rotation: Rotation) -> usize {
        ((row as i32 + self.magnification * rotation.0).rem_euclid(self.extended_n)) as usize
    }
}

#[derive(Clone, Debug)]
struct ExpressionRegistry<F: Field> {
    offsets: Offsets,
    constants: Vec<F>,
    challenges: Vec<usize>,
    has_identity: bool,
    polys: Vec<Query>,
    raw_calcs: Vec<Calculation<ValueSource>>,
    calcs: Vec<Calculation<usize>>,
    raw_outputs: Vec<ValueSource>,
    outputs: Vec<usize>,
}

impl<F: Field> Default for ExpressionRegistry<F> {
    fn default() -> Self {
        Self {
            offsets: Default::default(),
            constants: vec![F::ZERO, F::ONE, F::ONE.double()],
            challenges: Default::default(),
            has_identity: Default::default(),
            polys: Default::default(),
            raw_calcs: Default::default(),
            calcs: Default::default(),
            raw_outputs: Default::default(),
            outputs: Default::default(),
        }
    }
}

impl<F: Field> ExpressionRegistry<F> {
    fn new<'a>(expressions: impl IntoIterator<Item = &'a Expression<F>>) -> Self {
        let mut reg = Self::default();
        expressions
            .into_iter()
            .for_each(|expression| reg.register(expression));
        reg
    }

    fn register(&mut self, expression: &Expression<F>) {
        let output = self.register_expression(expression);
        self.offsets = Offsets::new(
            self.constants.len(),
            self.challenges.len(),
            self.has_identity,
            self.polys.len(),
        );
        self.calcs = self
            .raw_calcs
            .iter()
            .map(|calc| calc.indexed(&self.offsets))
            .collect();
        self.raw_outputs.push(output);
        self.outputs = self
            .raw_outputs
            .iter()
            .map(|output| output.indexed(&self.offsets))
            .collect();
    }

    fn offsets(&self) -> &Offsets {
        &self.offsets
    }

    fn polys(&self) -> &[Query] {
        &self.polys
    }

    fn calcs(&self) -> &[Calculation<usize>] {
        &self.calcs
    }

    fn buf(&self, challenges: &[F]) -> Vec<F> {
        let mut buf = vec![F::ZERO; self.offsets.calcs() + self.calcs.len()];
        buf[..self.constants.len()].copy_from_slice(&self.constants);
        izip!(&mut buf[self.offsets.challenges()..], &self.challenges)
            .for_each(|(buf, idx)| *buf = challenges[*idx]);
        buf
    }

    fn register_constant(&mut self, constant: &F) -> ValueSource {
        ValueSource::Constant(position_or_insert(&mut self.constants, constant))
    }

    fn register_challenge(&mut self, idx: &usize) -> ValueSource {
        ValueSource::Challenge(position_or_insert(&mut self.challenges, idx))
    }

    fn register_identity(&mut self) -> ValueSource {
        self.has_identity = true;
        ValueSource::Identity
    }

    fn register_poly(&mut self, query: &Query) -> ValueSource {
        ValueSource::Polynomial(position_or_insert(&mut self.polys, query))
    }

    fn register_calc(&mut self, calculation: Calculation<ValueSource>) -> ValueSource {
        ValueSource::Calculation(position_or_insert(&mut self.raw_calcs, &calculation))
    }

    fn register_expression(&mut self, expr: &Expression<F>) -> ValueSource {
        match expr {
            Expression::Polynomial(term) => match term {
                PolynomialRef::Constant(constant) => self.register_constant(constant),
                PolynomialRef::Challenge(idx) => self.register_challenge(idx),
                PolynomialRef::Identity => self.register_identity(),
                PolynomialRef::Opaque(query) => self.register_poly(query),
                PolynomialRef::Lagrange(_) => unreachable!(),
            },
            Expression::Neg(value) => {
                if let Expression::Polynomial(PolynomialRef::Constant(constant)) = value.deref() {
                    self.register_constant(&-*constant)
                } else {
                    let value = self.register_expression(value);
                    if let ValueSource::Constant(idx) = value {
                        self.register_constant(&-self.constants[idx])
                    } else {
                        self.register_calc(Calculation::Neg(value))
                    }
                }
            }
            Expression::Sum(lhs, rhs) => match (lhs.deref(), rhs.deref()) {
                (minuend, Expression::Neg(subtrahend)) | (Expression::Neg(subtrahend), minuend) => {
                    let minuend = self.register_expression(minuend);
                    let subtrahend = self.register_expression(subtrahend);
                    match (minuend, subtrahend) {
                        (ValueSource::Constant(minuend), ValueSource::Constant(subtrahend)) => {
                            let output = self.constants[minuend] - self.constants[subtrahend];
                            self.register_constant(&output)
                        }
                        (ValueSource::Constant(0), _) => {
                            self.register_calc(Calculation::Neg(subtrahend))
                        }
                        (_, ValueSource::Constant(0)) => minuend,
                        _ => self.register_calc(Calculation::Sub(minuend, subtrahend)),
                    }
                }
                _ => {
                    let lhs = self.register_expression(lhs);
                    let rhs = self.register_expression(rhs);
                    match (lhs, rhs) {
                        (ValueSource::Constant(lhs), ValueSource::Constant(rhs)) => {
                            self.register_constant(&(self.constants[lhs] + self.constants[rhs]))
                        }
                        (ValueSource::Constant(0), other) | (other, ValueSource::Constant(0)) => {
                            other
                        }
                        _ => {
                            if lhs <= rhs {
                                self.register_calc(Calculation::Add(lhs, rhs))
                            } else {
                                self.register_calc(Calculation::Add(rhs, lhs))
                            }
                        }
                    }
                }
            },
            Expression::Product(lhs, rhs) => {
                let lhs = self.register_expression(lhs);
                let rhs = self.register_expression(rhs);
                match (lhs, rhs) {
                    (ValueSource::Constant(0), _) | (_, ValueSource::Constant(0)) => {
                        ValueSource::Constant(0)
                    }
                    (ValueSource::Constant(1), other) | (other, ValueSource::Constant(1)) => other,
                    (ValueSource::Constant(2), other) | (other, ValueSource::Constant(2)) => {
                        self.register_calc(Calculation::Add(other, other))
                    }
                    (lhs, rhs) => {
                        if lhs <= rhs {
                            self.register_calc(Calculation::Mul(lhs, rhs))
                        } else {
                            self.register_calc(Calculation::Mul(rhs, lhs))
                        }
                    }
                }
            }
        }
    }
}

fn position_or_insert<T: Clone + Eq>(values: &mut Vec<T>, item: &T) -> usize {
    if let Some(idx) = values.iter().position(|lhs| lhs == item) {
        idx
    } else {
        let idx = values.len();
        values.push(item.clone());
        idx
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct Offsets(usize, usize, usize, usize);

impl Offsets {
    fn new(
        num_constants: usize,
        num_challenges: usize,
        has_identity: bool,
        num_polys: usize,
    ) -> Self {
        let mut offset = Self::default();
        offset.0 = num_constants;
        offset.1 = offset.0 + num_challenges;
        offset.2 = offset.1 + has_identity as usize;
        offset.3 = offset.2 + num_polys;
        offset
    }

    fn challenges(&self) -> usize {
        self.0
    }

    fn identity(&self) -> usize {
        self.1
    }

    fn polys(&self) -> usize {
        self.2
    }

    fn calcs(&self) -> usize {
        self.3
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Calculation<T> {
    Neg(T),
    Add(T, T),
    Sub(T, T),
    Mul(T, T),
}

impl Calculation<ValueSource> {
    fn indexed(&self, offsets: &Offsets) -> Calculation<usize> {
        use Calculation::*;
        match self {
            Neg(value) => Neg(value.indexed(offsets)),
            Add(lhs, rhs) => Add(lhs.indexed(offsets), rhs.indexed(offsets)),
            Sub(lhs, rhs) => Sub(lhs.indexed(offsets), rhs.indexed(offsets)),
            Mul(lhs, rhs) => Mul(lhs.indexed(offsets), rhs.indexed(offsets)),
        }
    }
}

impl Calculation<usize> {
    fn calculate<F: Field>(&self, buf: &[F]) -> F {
        use Calculation::*;
        match self {
            Neg(idx) => -buf[*idx],
            Add(lhs, rhs) => buf[*lhs] + buf[*rhs],
            Sub(lhs, rhs) => buf[*lhs] - buf[*rhs],
            Mul(lhs, rhs) => buf[*lhs] * buf[*rhs],
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ValueSource {
    Constant(usize),
    Challenge(usize),
    Identity,
    Polynomial(usize),
    Calculation(usize),
}

impl ValueSource {
    fn indexed(&self, offsets: &Offsets) -> usize {
        use ValueSource::*;
        match self {
            Constant(idx) => *idx,
            Challenge(idx) => offsets.challenges() + idx,
            Identity => offsets.identity(),
            Polynomial(idx) => offsets.polys() + idx,
            Calculation(idx) => offsets.calcs() + idx,
        }
    }
}

struct PolynomialView<'a, F> {
    poly: &'a Polynomial<F, ExtendedLagrangeCoeff>,
    step: usize,
}

impl<'a, F> PolynomialView<'a, F> {
    fn new(extended_k: usize, poly: &'a Polynomial<F, ExtendedLagrangeCoeff>) -> Self {
        Self {
            poly,
            step: poly.len() >> extended_k,
        }
    }
}

impl<'a, F> Index<usize> for PolynomialView<'a, F> {
    type Output = F;

    fn index(&self, index: usize) -> &Self::Output {
        &self.poly[index * self.step]
    }
}
