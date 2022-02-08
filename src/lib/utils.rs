use crate::{Lit, Var};

pub fn vars_iter<'a>(lits: impl Iterator<Item = &'a Lit> + 'a) -> impl Iterator<Item = Var> + 'a {
    lits.map(|l| l.var())
}

pub fn vars_disjoint<'a>(vars: impl Iterator<Item = &'a Lit> + 'a, other: &[Var]) -> bool {
    !vars_iter(vars).any(|v| other.binary_search(&v).is_ok())
}

/// Restrict a *sorted* sequence of literals to a *sorted* sequence of variables
pub fn restrict_sorted_clause<'a, 'b: 'a>(
    clause: impl Iterator<Item = &'a Lit> + 'a,
    vars: &'b [Var],
) -> impl Iterator<Item = &'a Lit> + 'a {
    let mut vi = vars.iter().peekable();
    clause.filter(move |l| loop {
        let v = match vi.peek() {
            Some(v) => *v,
            None => return false,
        };
        if *v > l.var() {
            return false;
        }
        vi.next();
        if *v == l.var() {
            return true;
        }
    })
}

pub fn is_subset<T: PartialEq>(s1: &[T], s2: &[T]) -> bool {
    s1.iter().all(|v| s2.contains(v))
}

pub fn is_sorted_subset(s1: &[Var], s2: &[Var]) -> bool {
    s1.iter().all(|v| s2.binary_search(v).is_ok())
}
