use crate::*;
use num_traits::identities::Zero;
use radix_trie::TrieCommon;
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
    #[error("assumption of list {0} is insufficient for the claim")]
    InsufficientAssumption(ListIndex),
    #[error("no claim found for some model in list {0}")]
    NoSupportingClaim(ListIndex),
    #[error("claimed count is wrong for a claim of component {0}")]
    WrongCount(ComponentIndex),
}

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

/// generate a mapping of variables to variable indices
/// from a set of variables
fn local_variable_mapping(vars: &BTreeSet<Var>) -> BTreeMap<Var, Var> {
    let mut vec = vars.iter().map(|v| *v).collect::<Vec<_>>();
    vec.sort_unstable();
    BTreeMap::from_iter(vec.drain(..).enumerate().map(|(i, v)| (v, i as isize + 1)))
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

impl Verifier {
    /// checks that a given list matches the associated component
    /// variables and clauses and returns list and component.
    fn list_matches_component(
        trace: &Trace,
        list: ListIndex,
    ) -> Result<(&ModelList, &Component), VerificationError> {
        let mlist = trace.get_list(list).unwrap();
        let comp = trace.components.get(&mlist.component).unwrap();

        if !mlist.vars.is_subset(&comp.vars) {
            return Err(VerificationError::InvalidListVariables(list));
        }

        if !mlist.clauses.is_subset(&comp.clauses) {
            return Err(VerificationError::InvalidListClauses(list));
        }
        Ok((mlist, comp))
    }

    pub fn verify_list(trace: &Trace, list: ListIndex) -> Result<(), VerificationError> {
        let (mlist, comp) = Verifier::list_matches_component(trace, list)?;

        // all models are models
        for model in mlist.models.keys() {
            if !is_model_of(trace, model, mlist.clauses.iter()) {
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

        let map = local_variable_mapping(&mlist.vars);
        let mut validation_formula = CnfFormula::new();
        validation_formula.set_var_count(mlist.vars.len());
        for l in &mlist.assm {
            let varisat_clause = lits_to_varisat(&[*l], &map);
            validation_formula.add_clause(&varisat_clause);
        }
        for cl in &directly_implied {
            let restricted = restrict_clause(&trace.clauses[*cl].lits, &mlist.vars);
            let varisat_clause = lits_to_varisat(&restricted, &map);
            validation_formula.add_clause(&varisat_clause);
        }
        let mut solver = varisat::Solver::new();
        solver.add_formula(&validation_formula);

        for cl in mlist.clauses.difference(&directly_implied) {
            let restricted = restrict_clause(&trace.clauses[*cl].lits, &mlist.vars);
            let negated: Vec<_> = negate_model(&restricted).collect();
            let varisat_clause = lits_to_varisat(&negated, &map);
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
            let negated: Vec<_> = negate_model(&model).collect();
            let clause = lits_to_varisat(&negated, &map);
            model_formula.add_clause(&clause);
        }
        solver.add_formula(&model_formula);
        match solver.solve() {
            Ok(false) => Ok(()),
            Ok(true) => return Err(VerificationError::IncompleteModelList(mlist.index)),
            Err(e) => panic! {"sat solver error {:?}", e},
        }
    }

    pub fn verify_composition(
        trace: &Trace,
        composition: &CompositionClaim,
    ) -> Result<(), VerificationError> {
        let (mlist, _comp) = Verifier::list_matches_component(trace, composition.list)?;

        let list_assm = BTreeSet::from_iter(mlist.assm.iter());
        let claim_assm = BTreeSet::from_iter(composition.assm.iter());

        if !list_assm.is_subset(&claim_assm) {
            return Err(VerificationError::InsufficientAssumption(composition.list));
        }

        let mut count = BigUint::zero();
        // FIXME: optimize
        for m in mlist.models.keys() {
            let model_set = BTreeSet::from_iter(m.iter());
            if !model_set.is_superset(&claim_assm) {
                continue;
            }
            if let Some(claim) = trace.claims.get(&mlist.component).unwrap().get(m) {
                count += claim.count();
            } else {
                return Err(VerificationError::NoSupportingClaim(composition.list));
            }
        }

        if count != composition.count {
            return Err(VerificationError::WrongCount(mlist.component));
        }

        Ok(())
    }

    pub fn verify_claim(trace: &Trace, claim: &Claim) -> Result<(), VerificationError> {
        match claim {
            Claim::Composition(c) => Verifier::verify_composition(trace, c),
            _ => Ok(()),
        }
    }
}
