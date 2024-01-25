use halo2_proofs::halo2curves::ff::{Field, PrimeField};
use std::{
    iter,
    ops::{Add, Mul},
};

pub(crate) mod evaluator;
pub(crate) mod halo2;

pub(crate) fn gcd(mut n: usize, mut m: usize) -> usize {
    assert_ne!(n, 0);
    assert_ne!(m, 0);

    while n != m {
        if n > m {
            n -= m;
        } else {
            m -= n;
        }
    }
    n
}

pub(crate) fn lcm(n: usize, m: usize) -> usize {
    n * m / gcd(n, m)
}

pub(crate) fn log2_ceil(value: usize) -> usize {
    assert_ne!(value, 0);
    value.next_power_of_two().trailing_zeros() as usize
}

pub(crate) fn div_ceil(numer: usize, denom: usize) -> usize {
    (numer + denom - 1) / denom
}

pub(crate) fn squares<F: Field>(base: F) -> impl Iterator<Item = F> {
    iter::successors(Some(base), move |value| Some(value.square()))
}

pub(crate) fn powers<F: Field>(base: F) -> impl Iterator<Item = F> {
    iter::successors(Some(F::ONE), move |value| Some(base * value))
}

pub(crate) fn horner<T1, T2>(values: &[T1], x: &T2) -> T1
where
    T1: Clone + for<'a> Mul<&'a T2, Output = T1> + for<'a> Add<&'a T1, Output = T1>,
{
    let mut values = values.iter().rev();
    let last = values.next().unwrap().clone();
    values.fold(last, |acc, value| acc * x + value)
}

pub(crate) fn root_of_unity<F: PrimeField>(n: usize) -> F {
    assert!(
        n.is_power_of_two(),
        "Only power of 2 domain size is supported"
    );
    let k = log2_ceil(n);
    assert!(k <= F::S as usize);
    squares(F::ROOT_OF_UNITY).nth(F::S as usize - k).unwrap()
}

pub(crate) fn felt_from_bool<F: Field>(value: bool) -> F {
    if value {
        F::ONE
    } else {
        F::ZERO
    }
}

/// Copied and modified from `itertools`
macro_rules! chain {
    () => {
        core::iter::empty()
    };
    ($first:expr $(,$rest:expr)* $(,)?) => {{
        let iter = core::iter::IntoIterator::into_iter($first);
        $(let iter = core::iter::Iterator::chain(iter, core::iter::IntoIterator::into_iter($rest));)*
        iter
    }};
}

/// Copied and modified from `itertools`
macro_rules! izip {
    (@closure $p:pat => $tup:expr) => {
        |$p| $tup
    };
    (@closure $p:pat => ($($tup:tt)*) ,$_iter:expr $(, $tail:expr)*) => {
        $crate::util::izip!(@closure ($p, b) => ( $($tup)*, b ) $( , $tail )*)
    };
    ($first:expr $(,)*) => {
        core::iter::IntoIterator::into_iter($first)
    };
    ($first:expr, $second:expr $(,)*) => {
        $crate::util::izip!($first).zip($second)
    };
    ($first:expr $(, $rest:expr)* $(,)*) => {
        $crate::util::izip!($first)
            $(.zip($rest))*
            .map($crate::util::izip!(@closure a => (a) $(, $rest)*))
    };
}

pub(crate) use {chain, izip};
