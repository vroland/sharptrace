use crate::{Lit, Var};

pub fn vars_iter<'a>(lits: impl Iterator<Item = &'a Lit> + 'a) -> impl Iterator<Item = Var> + 'a {
    lits.map(|l| l.var())
}

pub fn vars_disjoint<'a>(vars: impl Iterator<Item = &'a Lit> + 'a, other: &[Var]) -> bool {
    !vars_iter(vars).any(|v| other.contains(&v))
}
