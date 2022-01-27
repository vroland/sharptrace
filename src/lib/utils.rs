use crate::{Lit, Var};

pub fn vars_iter<'a>(lits: impl Iterator<Item = &'a Lit> + 'a) -> impl Iterator<Item = Var> + 'a {
    lits.map(|l| l.var())
}

pub fn vars_disjoint<'a>(vars: impl Iterator<Item = &'a Lit> + 'a, other: &[Var]) -> bool {
    !vars_iter(vars).any(|v| other.binary_search(&v).is_ok())
}

pub fn restrict_clause<'a, 'b: 'a>(
    clause: impl Iterator<Item = &'a Lit> + 'a,
    vars: &'b [Var],
) -> impl Iterator<Item = Lit> + 'a {
    clause.filter_map(|l| {
        if vars.binary_search(&l.var()).is_ok() {
            Some(*l)
        } else {
            None
        }
    })
}
