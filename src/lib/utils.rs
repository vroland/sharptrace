use crate::{Lit, Var};
use std::collections::BTreeSet;

pub fn vars_iter<'a>(lits: impl Iterator<Item = &'a Lit> + 'a) -> impl Iterator<Item = Var> + 'a {
    lits.map(|l| l.var())
}

pub fn vars_subset<'a, 'b>(
    lits: impl Iterator<Item = &'b Lit> + 'b,
    vars: &'a BTreeSet<Var>,
) -> bool {
    vars_iter(lits).all(|v| vars.contains(&v))
}

pub fn vars_disjoint<'a>(vars: impl Iterator<Item = &'a Lit> + 'a, other: &BTreeSet<Var>) -> bool {
    !vars_iter(vars).any(|v| other.contains(&v))
}
