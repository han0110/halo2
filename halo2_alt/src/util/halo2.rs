use crate::{
    protocol::{Expression, PolynomialRef},
    util::izip,
};
use halo2_proofs::{
    circuit::Value,
    halo2curves::{ff::Field, CurveAffine},
    plonk::{
        self, Advice, Any, Assigned, Assignment, Challenge, Column, Error, Fixed, Instance,
        Selector,
    },
    poly::Polynomial,
    transcript::{EncodedChallenge, TranscriptRead},
};
use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    io, iter, mem,
    ops::Range,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ColumnType {
    Selector,
    Fixed,
    Instance,
    Advice,
}

impl From<Any> for ColumnType {
    fn from(any: Any) -> Self {
        match any {
            Any::Advice(_) => Self::Advice,
            Any::Fixed => Self::Fixed,
            Any::Instance => Self::Instance,
        }
    }
}

pub(crate) fn convert_expressions<'a, F: Field>(
    expressions: impl IntoIterator<Item = &'a plonk::Expression<F>>,
    column_idx: &HashMap<(ColumnType, usize), usize>,
) -> Vec<Expression<F>> {
    expressions
        .into_iter()
        .map(|expression| convert_expression(expression, column_idx))
        .collect()
}

pub(crate) fn convert_expression<F: Field>(
    expression: &plonk::Expression<F>,
    column_idx: &HashMap<(ColumnType, usize), usize>,
) -> Expression<F> {
    expression.evaluate::<Expression<_>>(
        &|constant| PolynomialRef::Constant(constant).into(),
        &|selector| {
            let poly = column_idx[&(ColumnType::Selector, selector.index())];
            PolynomialRef::Opaque((poly, 0).into()).into()
        },
        &|query| {
            let poly = column_idx[&(ColumnType::Fixed, query.column_index())];
            PolynomialRef::Opaque((poly, query.rotation().0).into()).into()
        },
        &|query| {
            let poly = column_idx[&(ColumnType::Advice, query.column_index())];
            PolynomialRef::Opaque((poly, query.rotation().0).into()).into()
        },
        &|query| {
            let poly = column_idx[&(ColumnType::Instance, query.column_index())];
            PolynomialRef::Opaque((poly, query.rotation().0).into()).into()
        },
        &|_| unimplemented!(),
        &|value| -value,
        &|lhs, rhs| lhs + rhs,
        &|lhs, rhs| lhs * rhs,
        &|value, scalar| value * PolynomialRef::Constant(scalar),
    )
}

pub(crate) fn batch_invert_assigned<F: Field>(assigned: Vec<Vec<Assigned<F>>>) -> Vec<Vec<F>> {
    halo2_proofs::poly::batch_invert_assigned(assigned.into_iter().map(Polynomial::new).collect())
        .into_iter()
        .map(Polynomial::into_vec)
        .collect()
}

pub(crate) trait TranscriptReadVec<C: CurveAffine, E: EncodedChallenge<C>>:
    TranscriptRead<C, E>
{
    fn read_points(&mut self, n: usize) -> io::Result<Vec<C>> {
        iter::repeat_with(|| self.read_point()).take(n).collect()
    }

    fn read_scalars(&mut self, n: usize) -> io::Result<Vec<C::Scalar>> {
        iter::repeat_with(|| self.read_scalar()).take(n).collect()
    }
}

impl<C: CurveAffine, E: EncodedChallenge<C>, T: TranscriptRead<C, E>> TranscriptReadVec<C, E>
    for T
{
}

#[derive(Debug)]
pub(crate) struct PreprocessCollector<F: Field> {
    pub(crate) k: u32,
    pub(crate) fixeds: Vec<Vec<Assigned<F>>>,
    pub(crate) permutation: Permutation,
    pub(crate) selectors: Vec<Vec<bool>>,
    pub(crate) usable_rows: Range<usize>,
}

impl<F: Field> Assignment<F> for PreprocessCollector<F> {
    fn enter_region<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
    }

    fn exit_region(&mut self) {}

    fn annotate_column<A, AR>(&mut self, _: A, _: Column<Any>)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
    }

    fn enable_selector<A, AR>(&mut self, _: A, selector: &Selector, row: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row) {
            return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        };

        self.selectors[selector.index()][row] = true;

        Ok(())
    }

    fn query_instance(&self, _: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        if !self.usable_rows.contains(&row) {
            return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        }

        Ok(Value::unknown())
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        _: Column<Advice>,
        _: usize,
        _: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Fixed>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row) {
            return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        };

        *self
            .fixeds
            .get_mut(column.index())
            .and_then(|v| v.get_mut(row))
            .ok_or(Error::BoundsFailure)? = to().into_field().assign()?;

        Ok(())
    }

    fn copy(
        &mut self,
        lhs_column: Column<Any>,
        lhs_row: usize,
        rhs_column: Column<Any>,
        rhs_row: usize,
    ) -> Result<(), Error> {
        if !self.usable_rows.contains(&lhs_row) {
            return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        };
        if !self.usable_rows.contains(&rhs_row) {
            return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        };
        self.permutation
            .copy(lhs_column, lhs_row, rhs_column, rhs_row)
    }

    fn fill_from_row(
        &mut self,
        column: Column<Fixed>,
        from_row: usize,
        to: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        if !self.usable_rows.contains(&from_row) {
            return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        };

        let col = self
            .fixeds
            .get_mut(column.index())
            .ok_or(Error::BoundsFailure)?;

        let filler = to.assign()?;
        for row in self.usable_rows.clone().skip(from_row) {
            col[row] = filler;
        }

        Ok(())
    }

    fn get_challenge(&self, _: Challenge) -> Value<F> {
        Value::unknown()
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
    }

    fn pop_namespace(&mut self, _: Option<String>) {}
}

#[derive(Debug)]
pub(crate) struct Permutation {
    pub(crate) column_idx: HashMap<Column<Any>, usize>,
    pub(crate) cycles: Vec<HashSet<(usize, usize)>>,
    pub(crate) cycle_idx: HashMap<(usize, usize), usize>,
}

impl Permutation {
    pub(crate) fn new(columns: Vec<Column<Any>>) -> Self {
        Self {
            column_idx: izip!(columns, 0..).collect(),
            cycles: Default::default(),
            cycle_idx: Default::default(),
        }
    }

    fn copy(
        &mut self,
        lhs_column: Column<Any>,
        lhs_row: usize,
        rhs_column: Column<Any>,
        rhs_row: usize,
    ) -> Result<(), Error> {
        let lhs_idx = *self
            .column_idx
            .get(&lhs_column)
            .ok_or(Error::ColumnNotInPermutation(lhs_column))?;
        let rhs_idx = *self
            .column_idx
            .get(&rhs_column)
            .ok_or(Error::ColumnNotInPermutation(rhs_column))?;

        match (
            self.cycle_idx.get(&(lhs_idx, lhs_row)).copied(),
            self.cycle_idx.get(&(rhs_idx, rhs_row)).copied(),
        ) {
            (Some(lhs_cycle_idx), Some(rhs_cycle_idx)) => {
                for cell in self.cycles[rhs_cycle_idx].iter().copied() {
                    self.cycle_idx.insert(cell, lhs_cycle_idx);
                }
                let rhs_cycle = mem::take(&mut self.cycles[rhs_cycle_idx]);
                self.cycles[lhs_cycle_idx].extend(rhs_cycle);
            }
            cycle_idx => {
                let cycle_idx = if let (Some(cycle_idx), None) | (None, Some(cycle_idx)) = cycle_idx
                {
                    cycle_idx
                } else {
                    let cycle_idx = self.cycles.len();
                    self.cycles.push(Default::default());
                    cycle_idx
                };
                for cell in [(lhs_idx, lhs_row), (rhs_idx, rhs_row)] {
                    self.cycles[cycle_idx].insert(cell);
                    self.cycle_idx.insert(cell, cycle_idx);
                }
            }
        };

        Ok(())
    }

    pub(crate) fn into_cycles(self) -> Vec<Vec<(usize, usize)>> {
        self.cycles
            .into_iter()
            .filter_map(|cycle| {
                (!cycle.is_empty()).then(|| {
                    let mut cycle = cycle.into_iter().collect::<Vec<_>>();
                    cycle.sort();
                    cycle
                })
            })
            .collect()
    }
}

#[derive(Debug)]
pub(crate) struct WitnessCollector<'a, F: Field> {
    pub(crate) k: u32,
    pub(crate) phase: u8,
    pub(crate) instance_values: &'a [&'a [F]],
    pub(crate) advices: Vec<Vec<Assigned<F>>>,
    pub(crate) usable_rows: Range<usize>,
}

impl<'a, F: Field> Assignment<F> for WitnessCollector<'a, F> {
    fn enter_region<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
    }

    fn exit_region(&mut self) {}

    fn annotate_column<A, AR>(&mut self, _: A, _: Column<Any>)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
    }

    fn enable_selector<A, AR>(&mut self, _: A, _: &Selector, _: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        Ok(())
    }

    fn query_instance(&self, column: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        self.instance_values
            .get(column.index())
            .and_then(|column| column.get(row))
            .map(|v| Value::known(*v))
            .ok_or(Error::BoundsFailure)
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Advice>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if self.phase != column.column_type().phase() {
            return Ok(());
        }

        if !self.usable_rows.contains(&row) {
            return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        };

        *self
            .advices
            .get_mut(column.index())
            .and_then(|v| v.get_mut(row))
            .ok_or(Error::BoundsFailure)? = to().into_field().assign()?;

        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        _: Column<Fixed>,
        _: usize,
        _: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        Ok(())
    }

    fn copy(&mut self, _: Column<Any>, _: usize, _: Column<Any>, _: usize) -> Result<(), Error> {
        Ok(())
    }

    fn fill_from_row(
        &mut self,
        _: Column<Fixed>,
        _: usize,
        _: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn get_challenge(&self, _: Challenge) -> Value<F> {
        unimplemented!()
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
    }

    fn pop_namespace(&mut self, _: Option<String>) {}
}
