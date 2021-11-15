use crate::*;
use radix_trie::{Trie, TrieCommon};
use thiserror::Error;
use varisat::{CnfFormula, ExtendFormula};

#[derive(Debug)]
pub struct Verifier {}

#[derive(Debug, Clone, Error)]
pub enum VerificationError {
    #[error("list {0} variables are not a subset of component variables")]
    InvalidListVariables(ListIndex),
    #[error("list {0} clauses are not a subset of component clauses")]
    InvalidListClauses(ListIndex),
    #[error("a model for list {0} is not a model")]
    NotAModel(ListIndex),
    #[error("clause {0} violates validity of model list {1}")]
    InvalidModelList(ClauseIndex, ListIndex),
    #[error("model list {0} is incomplete")]
    IncompleteModelList(ListIndex),
}

impl Verifier {
    fn is_model_of<'a>(
        trace: &Trace,
        model: &[Lit],
        mut clauses: impl Iterator<Item = &'a ClauseIndex>,
    ) -> bool {
        // FIXME: this can be accelerated, since model and clauses are sorted
        clauses.all(|c| trace.clauses[*c].lits.iter().any(|l| model.contains(l)))
    }

    fn restrict_clause(clause: &[Lit], vars: &BTreeSet<Var>) -> Vec<Lit> {
        clause
            .iter()
            .filter_map(|l| {
                if vars.contains(&l.abs()) {
                    Some(*l)
                } else {
                    None
                }
            })
            .collect()
    }

    fn negate_model<'a>(m: &'a [Lit]) -> impl Iterator<Item = Lit> + 'a {
        m.iter().map(|l| -l)
    }

    fn lits_to_varisat<'a>(
        lits: impl IntoIterator<Item = &'a Lit>,
        map: &BTreeMap<Var, Var>,
    ) -> Vec<varisat::Lit> {
        lits.into_iter()
            .map(|l| l.signum() * map.get(&l.abs()).unwrap())
            .map(|l| varisat::Lit::from_dimacs(l))
            .collect::<Vec<_>>()
    }

    /// generate a mapping of variables to variable indices
    /// from a set of variables
    fn local_variable_mapping(vars: &BTreeSet<Var>) -> BTreeMap<Var, Var> {
        let mut vec = vars.iter().map(|v| *v).collect::<Vec<_>>();
        vec.sort_unstable();
        BTreeMap::from_iter(vec.drain(..).enumerate().map(|(i, v)| (v, i as isize + 1)))
    }

    pub fn verify_list(trace: &Trace, list: ListIndex) -> Result<(), VerificationError> {
        let mlist = trace.get_list(list).unwrap();
        let comp = trace.components.get(&mlist.component).unwrap();

        if !mlist.vars.is_subset(&comp.vars) {
            return Err(VerificationError::InvalidListVariables(list));
        }

        if !mlist.clauses.is_subset(&comp.clauses) {
            return Err(VerificationError::InvalidListClauses(list));
        }

        // all models are models
        for model in mlist.models.keys() {
            if !Verifier::is_model_of(trace, model, mlist.clauses.iter()) {
                return Err(VerificationError::NotAModel(list));
            }
        }

        // validity condition
        let nolist_vars = comp.vars.difference(&mlist.vars).map(|v| *v).collect();
        let directly_implied: BTreeSet<_> = mlist
            .clauses
            .iter()
            .filter(|c| vars_set(&trace.clauses[**c].lits[..]).is_disjoint(&nolist_vars))
            .map(|c| *c)
            .collect();

        let map = Verifier::local_variable_mapping(&mlist.vars);
        let mut validation_formula = CnfFormula::new();
        validation_formula.set_var_count(mlist.vars.len());
        for l in &mlist.assm {
            let varisat_clause = Verifier::lits_to_varisat(&[*l], &map);
            validation_formula.add_clause(&varisat_clause);
        }
        for cl in &directly_implied {
            let restricted = Verifier::restrict_clause(&trace.clauses[*cl].lits, &mlist.vars);
            let varisat_clause = Verifier::lits_to_varisat(&restricted, &map);
            validation_formula.add_clause(&varisat_clause);
        }
        let mut solver = varisat::Solver::new();
        solver.add_formula(&validation_formula);

        for cl in mlist.clauses.difference(&directly_implied) {
            let restricted = Verifier::restrict_clause(&trace.clauses[*cl].lits, &mlist.vars);
            let negated: Vec<_> = Verifier::negate_model(&restricted).collect();
            let varisat_clause = Verifier::lits_to_varisat(&negated, &map);
            solver.assume(&varisat_clause);
            match solver.solve() {
                // clause is implied
                Ok(false) => continue,
                Ok(true) => return Err(VerificationError::InvalidModelList(mlist.index, *cl)),
                Err(e) => panic! {"sat solver error {:?}", e},
            }
        }

        // completeness
        let mut model_formula = varisat::CnfFormula::new();
        validation_formula.set_var_count(mlist.vars.len());

        for model in mlist.models.keys() {
            let negated: Vec<_> = Verifier::negate_model(&model).collect();
            let clause = Verifier::lits_to_varisat(&negated, &map);
            model_formula.add_clause(&clause);
        }
        solver.add_formula(&model_formula);
        match solver.solve() {
            Ok(false) => Ok(()),
            Ok(true) => return Err(VerificationError::IncompleteModelList(mlist.index)),
            Err(e) => panic! {"sat solver error {:?}", e},
        }
    }
}
