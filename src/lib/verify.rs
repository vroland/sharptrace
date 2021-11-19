use crate::*;
use num_traits::identities::{One, Zero};
use radix_trie::TrieCommon;
use std::collections::HashMap;
use thiserror::Error;
use varisat::{CnfFormula, ExtendFormula};

#[derive(Debug)]
pub struct Verifier<'t> {
    // sets of assigned variables proven exhaustive for a given model list
    implicitly_proven: HashMap<(ListIndex, Vec<Var>), ()>,
    trace: &'t Trace,
}

#[derive(Debug, Clone, Error)]
pub enum VerificationError {
    #[error("list {0} variables are not a subset of component variables")]
    InvalidListVariables(ListIndex),
    #[error("assumption variables are not a subset of component {0} variables")]
    InvalidAssumptionVariables(ComponentIndex),
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
    #[error("child component variables are not a subset of parent variables {0}")]
    ChildVarsInvalid(ComponentIndex),
    #[error("child component clauses are not a subset of parent clauses {0}")]
    ChildClausesInvalid(ComponentIndex),
    #[error("child component variables do not cover parent component {0}")]
    ChildVarsInsufficient(ComponentIndex),
    #[error("child component clauses do not cover parent component {0}")]
    ChildClausesInsufficient(ComponentIndex),
    #[error("the join assumption does not cover variable intersection")]
    JoinAssumptionInsufficient(),
    #[error("clause {0} of the child component {1} is illegal in join")]
    IllegalClause(ClauseIndex, ComponentIndex),
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

impl<'t> Verifier<'t> {
    pub fn new(trace: &'t Trace) -> Self {
        Verifier {
            implicitly_proven: HashMap::new(),
            trace,
        }
    }

    /// checks that a given list matches the associated component
    /// variables and clauses and returns list and component.
    fn list_matches_component(
        &self,
        list: ListIndex,
    ) -> Result<(&ModelList, &Component), VerificationError> {
        let mlist = self.trace.get_list(list).unwrap();
        let comp = self.trace.components.get(&mlist.component).unwrap();

        if !mlist.vars.is_subset(&comp.vars) {
            return Err(VerificationError::InvalidListVariables(list));
        }

        if !mlist.clauses.is_subset(&comp.clauses) {
            return Err(VerificationError::InvalidListClauses(list));
        }
        Ok((mlist, comp))
    }

    pub fn verify_list(&self, list: ListIndex) -> Result<(), VerificationError> {
        let (mlist, comp) = self.list_matches_component(list)?;

        // all models are models
        for model in mlist.models.keys() {
            if !is_model_of(self.trace, model, mlist.clauses.iter()) {
                return Err(VerificationError::NotAModel(list));
            }
        }

        // validity condition
        let nolist_vars = comp.vars.difference(&mlist.vars).map(|v| *v).collect();
        let directly_implied: BTreeSet<_> = mlist
            .clauses
            .iter()
            .filter(|c| vars_set(&self.trace.clauses[**c].lits[..]).is_disjoint(&nolist_vars))
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
            let restricted = restrict_clause(&self.trace.clauses[*cl].lits, &mlist.vars);
            let varisat_clause = lits_to_varisat(&restricted, &map);
            validation_formula.add_clause(&varisat_clause);
        }
        let mut solver = varisat::Solver::new();
        solver.add_formula(&validation_formula);

        for cl in mlist.clauses.difference(&directly_implied) {
            let restricted = restrict_clause(&self.trace.clauses[*cl].lits, &mlist.vars);
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
        &self,
        composition: &CompositionClaim,
    ) -> Result<(), VerificationError> {
        let (mlist, _comp) = self.list_matches_component(composition.list)?;

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
            if let Some(claim) = self.trace.claims.get(&mlist.component).unwrap().get(m) {
                count += claim.count();
            } else {
                eprintln! {"no claim matching {:?} for child {}", m, mlist.component};
                return Err(VerificationError::NoSupportingClaim(composition.list));
            }
        }

        if count != composition.count {
            return Err(VerificationError::WrongCount(mlist.component));
        }

        Ok(())
    }

    fn is_implicit_claim(&mut self, component: ComponentIndex, implicit_assm: &[Lit]) -> bool {
        let comp_claims = self.trace.claims.get(&component).unwrap();
        let assm_vars = vars(&implicit_assm);

        for l in 0..implicit_assm.len() - 1 {
            let prefix = Vec::from(&implicit_assm[0..l]);
            if let Some(Claim::Composition(parent)) = comp_claims.get(&prefix) {
                let mlist = self.trace.get_list(parent.list).unwrap();
                // cache hit
                if self
                    .implicitly_proven
                    .contains_key(&(parent.list, assm_vars.clone()))
                {
                    return true;
                }

                let sibling_count = comp_claims
                    .subtrie(&prefix)
                    .unwrap()
                    .iter()
                    .filter(|(assm, _)| vars(assm) == assm_vars)
                    .filter(|(_, claim)| {
                        if let Claim::Composition(c) = claim {
                            c.list == mlist.index
                        } else {
                            false
                        }
                    })
                    .map(|(_, claim)| claim.count())
                    .fold(BigUint::zero(), |acc, c| acc + c);

                // siblings complete, we can instantiate an implicit claim
                if sibling_count == parent.count {
                    self.implicitly_proven
                        .insert((parent.list, assm_vars.clone()), ());
                    return true;
                }
            }
        }
        return false;
    }

    pub fn verify_join(&mut self, join: &JoinClaim) -> Result<(), VerificationError> {
        let assm_vars = BTreeSet::from_iter(vars(&join.assm));
        let component = self.trace.components.get(&join.component).unwrap();
        let children = join
            .child_components
            .iter()
            .map(|idx| self.trace.components.get(&idx).unwrap())
            .collect::<Vec<_>>();

        if !assm_vars.is_subset(&component.vars) {
            return Err(VerificationError::InvalidAssumptionVariables(
                join.component,
            ));
        }

        if children.iter().any(|c| !c.vars.is_subset(&component.vars)) {
            return Err(VerificationError::ChildVarsInvalid(join.component));
        }
        if children
            .iter()
            .any(|c| !c.clauses.is_subset(&component.clauses))
        {
            return Err(VerificationError::ChildClausesInvalid(join.component));
        }

        // do subcomponents cover parent components?
        let vars_union = children.iter().fold(BTreeSet::new(), |acc, comp| {
            BTreeSet::from_iter(acc.union(&comp.vars).map(|v| *v))
        });

        if vars_union != component.vars {
            return Err(VerificationError::ChildVarsInsufficient(join.component));
        }

        let clauses_union = children.iter().fold(BTreeSet::new(), |acc, comp| {
            BTreeSet::from_iter(acc.union(&comp.clauses).map(|c| *c))
        });
        if clauses_union != component.clauses {
            return Err(VerificationError::ChildClausesInsufficient(join.component));
        }

        // are subcomponents mutually compatible?
        for child_i in &children {
            for child_j in &children {
                if child_i.index == child_j.index {
                    continue;
                }

                let intersection_vars = child_i.vars.intersection(&child_j.vars);
                let intersection_vars = intersection_vars.map(|v| *v).collect();

                if !assm_vars.is_superset(&intersection_vars) {
                    return Err(VerificationError::JoinAssumptionInsufficient());
                }

                let i_only_vars = component.vars.difference(&child_i.vars);
                let i_only_vars = i_only_vars.map(|v| *v).collect();

                for cl in &child_i.clauses {
                    let clause = &self.trace.clauses[*cl];
                    if vars_set(&clause.lits).intersection(&i_only_vars).count() != 0 {
                        return Err(VerificationError::IllegalClause(*cl, child_i.index));
                    }
                }
            }
        }

        let mut count = BigUint::one();
        for child_i in &children {
            let child_assm = restrict_clause(&join.assm, &child_i.vars);
            if let Some(claim) = self
                .trace
                .claims
                .get(&child_i.index)
                .unwrap()
                .get(&child_assm)
            {
                count *= claim.count();
            } else {
                if self.is_implicit_claim(child_i.index, &child_assm) {
                    count = BigUint::zero();
                } else {
                    eprintln! {"no claim matching {:?} for child {}", child_assm, child_i.index};
                    return Err(VerificationError::NoSupportingClaim(join.component));
                }
            }
        }

        if count != join.count {
            eprintln! {"component: {}, claimed count: {}, verified count: {}, assm: {:?}", join.component, join.count, count, join.assm};
            return Err(VerificationError::WrongCount(join.component));
        }

        Ok(())
    }

    pub fn verify_claim(&mut self, claim: &Claim) -> Result<(), VerificationError> {
        match claim {
            Claim::Composition(c) => self.verify_composition(c),
            Claim::Join(c) => self.verify_join(c),
            _ => Ok(()),
        }
    }
}
