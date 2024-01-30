use halo2_proofs::{halo2curves::ff::Field, poly::Rotation};
use std::{
    collections::BTreeSet,
    convert::identity,
    fmt::Debug,
    hash::{Hash, Hasher},
    iter::{Product, Sum},
    ops::{Add, Mul, Neg, Sub},
};

/// Query to a opaque polynomial.
#[derive(Clone, Copy, Debug, Eq)]
pub struct Query {
    pub(crate) index: usize,
    pub(crate) rotation: Rotation,
}

impl Query {
    /// Returns `Query`.
    pub fn new(index: usize, rotation: Rotation) -> Self {
        Self { index, rotation }
    }

    /// Returns index of opaque polynomial.
    pub fn index(&self) -> usize {
        self.index
    }

    /// Returns rotation of query.
    pub fn rotation(&self) -> Rotation {
        self.rotation
    }
}

impl From<(usize, i32)> for Query {
    fn from((index, rotation): (usize, i32)) -> Self {
        Self::new(index, Rotation(rotation))
    }
}

impl From<(usize, Rotation)> for Query {
    fn from((index, rotation): (usize, Rotation)) -> Self {
        Self::new(index, rotation)
    }
}

impl PartialEq for Query {
    fn eq(&self, other: &Self) -> bool {
        (self.index, self.rotation).eq(&(other.index, other.rotation))
    }
}

impl PartialOrd for Query {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        (self.index, self.rotation.0).partial_cmp(&(other.index, other.rotation.0))
    }
}

impl Ord for Query {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl Hash for Query {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.index.hash(state);
        self.rotation.0.hash(state);
    }
}

/// `PolynomialRef` represents different kinds of polynomials that might be used in a Plonkish
/// proof system.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PolynomialRef<F> {
    /// `f(X) = c`
    Constant(F),
    /// `f(X) = challenges[idx]`
    Challenge(usize),
    /// `f(X) = X`
    Identity,
    /// `f(X) = 1 if X == omega^i else 0 for X in omega^(0..n)`
    Lagrange(i32),
    /// `f(X)` without specific structure
    Opaque(Query),
}

impl<F> PolynomialRef<F> {
    /// Returns `PolynomialRef::Opaque(query)`.
    pub fn opaque(query: impl Into<Query>) -> Self {
        Self::Opaque(query.into())
    }

    /// Returns degree of the referenced polynomial.
    pub fn degree(&self) -> usize {
        match self {
            Self::Constant(_) | Self::Challenge(_) => 0,
            Self::Identity | Self::Lagrange(_) | Self::Opaque(_) => 1,
        }
    }

    /// Evaluate `PolynomialRef` using the provided closures to perform the operations.
    pub fn evaluate<T>(
        &self,
        constant: &impl Fn(F) -> T,
        challenge: &impl Fn(usize) -> T,
        identity: &impl Fn() -> T,
        lagrange: &impl Fn(i32) -> T,
        opaque: &impl Fn(Query) -> T,
    ) -> T
    where
        F: Clone,
    {
        match self {
            Self::Constant(value) => constant(value.clone()),
            Self::Challenge(value) => challenge(*value),
            Self::Identity => identity(),
            Self::Lagrange(value) => lagrange(*value),
            Self::Opaque(value) => opaque(*value),
        }
    }
}

/// Arithmetic expression of `PolynomialRef`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Expression<F> {
    /// It holds a `PolynomialRef`.
    Polynomial(PolynomialRef<F>),
    /// Negated `Expression`.
    Neg(Box<Self>),
    /// Sum of two `Expression`.
    Sum(Box<Self>, Box<Self>),
    /// Product of two `Expression`.
    Product(Box<Self>, Box<Self>),
}

impl<F> From<PolynomialRef<F>> for Expression<F> {
    fn from(poly: PolynomialRef<F>) -> Self {
        Expression::Polynomial(poly)
    }
}

impl<F> Expression<F> {
    /// Returns degree of the `Expression`.
    pub fn degree(&self) -> usize {
        match self {
            Self::Polynomial(inner) => inner.degree(),
            Self::Neg(inner) => inner.degree(),
            Self::Sum(lhs, rhs) => lhs.degree().max(rhs.degree()),
            Self::Product(lhs, rhs) => lhs.degree() + rhs.degree(),
        }
    }
}

impl<F: Clone> Expression<F> {
    /// Evaluate `Expression` using the provided closures to perform the operations.
    pub fn evaluate<T>(
        &self,
        poly: &impl Fn(PolynomialRef<F>) -> T,
        neg: &impl Fn(T) -> T,
        sum: &impl Fn(T, T) -> T,
        product: &impl Fn(T, T) -> T,
    ) -> T {
        let evaluate = |expr: &Self| expr.evaluate(poly, neg, sum, product);
        match self {
            Self::Polynomial(a) => poly(a.clone()),
            Self::Neg(a) => neg(evaluate(a)),
            Self::Sum(a, b) => sum(evaluate(a), evaluate(b)),
            Self::Product(a, b) => product(evaluate(a), evaluate(b)),
        }
    }

    /// Evaluate `Expression` using the provided closures which return field element.
    pub fn evaluate_felt(&self, poly: &impl Fn(PolynomialRef<F>) -> F) -> F
    where
        F: Field,
    {
        self.evaluate(poly, &|a| -a, &|a, b| a + b, &|a, b| a * b)
    }

    fn used_poly<T, I>(&self, poly: &impl Fn(PolynomialRef<F>) -> I) -> BTreeSet<T>
    where
        T: Clone + Ord,
        I: IntoIterator<Item = T>,
    {
        self.evaluate(
            &|a| BTreeSet::from_iter(poly(a)),
            &|a| a,
            &merge_set,
            &merge_set,
        )
    }

    /// Returns used `PolynomialRef::Lagrange` of the `Expression`.
    pub fn used_langrange(&self) -> BTreeSet<i32> {
        self.used_poly(&|poly| match poly {
            PolynomialRef::Lagrange(i) => i.into(),
            _ => None,
        })
    }

    /// Returns used `Query` of the `Expression`.
    pub fn used_query(&self) -> BTreeSet<Query> {
        self.used_poly(&|poly| match poly {
            PolynomialRef::Opaque(query) => query.into(),
            _ => None,
        })
    }

    /// Returns used `PolynomialRef::Challenge` of the `Expression`.
    pub fn used_challenge(&self) -> BTreeSet<usize> {
        self.used_poly(&|poly| match poly {
            PolynomialRef::Challenge(idx) => idx.into(),
            _ => None,
        })
    }
}

macro_rules! impl_ops {
    (@ $lhs:ty, $rhs:ty, $trait:ident, $op:ident, $variant:ident, $rhs_transformer:expr) => {
        impl<F: Clone> $trait<$rhs> for $lhs {
            type Output = Expression<F>;
            fn $op(self, rhs: $rhs) -> Self::Output {
                Expression::$variant(
                    (Expression::from(self)).into(),
                    $rhs_transformer(Expression::from(rhs)).into(),
                )
            }
        }

        impl<F: Clone> $trait<$rhs> for &$lhs {
            type Output = Expression<F>;
            fn $op(self, rhs: $rhs) -> Self::Output {
                Expression::$variant(
                    (Expression::from(self.clone())).into(),
                    $rhs_transformer(Expression::from(rhs)).into(),
                )
            }
        }

        impl<F: Clone> $trait<&$rhs> for $lhs {
            type Output = Expression<F>;
            fn $op(self, rhs: &$rhs) -> Self::Output {
                Expression::$variant(
                    (Expression::from(self)).into(),
                    $rhs_transformer(Expression::from(rhs.clone())).into(),
                )
            }
        }

        impl<F: Clone> $trait<&$rhs> for &$lhs {
            type Output = Expression<F>;
            fn $op(self, rhs: &$rhs) -> Self::Output {
                Expression::$variant(
                    (Expression::from(self.clone())).into(),
                    $rhs_transformer(Expression::from(rhs.clone())).into(),
                )
            }
        }
    };
    ($trait:ident, $op:ident, $variant:ident, $rhs_transformer:expr) => {
        impl_ops!(@ PolynomialRef<F>, PolynomialRef<F>, $trait, $op, $variant, $rhs_transformer);
        impl_ops!(@ PolynomialRef<F>, Expression<F>, $trait, $op, $variant, $rhs_transformer);
        impl_ops!(@ Expression<F>, PolynomialRef<F>, $trait, $op, $variant, $rhs_transformer);
        impl_ops!(@ Expression<F>, Expression<F>, $trait, $op, $variant, $rhs_transformer);
    };
    ($trait:ident, $op:ident, $variant:ident) => {
        impl_ops!($trait, $op, $variant, identity);
    };
}

impl_ops!(Mul, mul, Product);
impl_ops!(Add, add, Sum);
impl_ops!(Sub, sub, Sum, Neg::neg);

impl<F: Clone> Neg for PolynomialRef<F> {
    type Output = Expression<F>;
    fn neg(self) -> Self::Output {
        -Expression::from(self)
    }
}

impl<F: Clone> Neg for &PolynomialRef<F> {
    type Output = Expression<F>;
    fn neg(self) -> Self::Output {
        -Expression::from(self.clone())
    }
}

impl<F: Clone> Neg for Expression<F> {
    type Output = Expression<F>;
    fn neg(self) -> Self::Output {
        Expression::Neg(self.into())
    }
}

impl<F: Clone> Neg for &Expression<F> {
    type Output = Expression<F>;
    fn neg(self) -> Self::Output {
        -self.clone()
    }
}

macro_rules! impl_sum_product {
    ($name:ty) => {
        impl<'a, F: Field> Sum<&'a $name> for Expression<F> {
            fn sum<I: Iterator<Item = &'a $name>>(iter: I) -> Self {
                iter.cloned().sum()
            }
        }

        impl<F: Field> Sum<$name> for Expression<F> {
            fn sum<I: Iterator<Item = $name>>(iter: I) -> Self {
                iter.map(Expression::from)
                    .reduce(|acc, item| acc + item)
                    .unwrap_or_else(|| PolynomialRef::Constant(F::ZERO).into())
            }
        }

        impl<'a, F: Field> Product<&'a $name> for Expression<F> {
            fn product<I: Iterator<Item = &'a $name>>(iter: I) -> Self {
                iter.cloned().product()
            }
        }

        impl<F: Field> Product<$name> for Expression<F> {
            fn product<I: Iterator<Item = $name>>(iter: I) -> Self {
                iter.map(Expression::from)
                    .reduce(|acc, item| acc * item)
                    .unwrap_or_else(|| PolynomialRef::Constant(F::ONE).into())
            }
        }
    };
}

impl_sum_product!(Expression<F>);
impl_sum_product!(PolynomialRef<F>);

fn merge_set<T: Clone + Ord>(mut lhs: BTreeSet<T>, mut rhs: BTreeSet<T>) -> BTreeSet<T> {
    lhs.append(&mut rhs);
    lhs
}
