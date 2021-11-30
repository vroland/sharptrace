use crate::prefixes::PrefixSet;
use crate::utils::{vars_disjoint, vars_iter};
use crate::*;
use num_bigint::BigUint;
use num_traits::identities::{One, Zero};
use std::collections::{BTreeSet, HashSet};
use thiserror::Error;
use varisat::{CnfFormula, ExtendFormula};

#[derive(Debug)]
pub struct Verifier<'t> {
    // sets of proven component - subcomponent combinations for join
    valid_join_subcomps: HashSet<(ComponentIndex, Vec<ComponentIndex>)>,
    trace: &'t Trace,
}

#[derive(Debug, Clone, Error)]
pub enum VerificationError {
    #[error("prefix variables are not a subset of component variables")]
    InvalidPrefixVariables(),
    #[error("assumption variables are not a subset of component variables")]
    InvalidAssumptionVariables(),
    #[error("the assignment {0:?} is not a model")]
    NotAModel(Box<Model>),
    #[error("prefix set {0} is invalid for component {1}")]
    InvalidPrefixSet(PrefixSetIndex, ComponentIndex),
    #[error("assumption of prefix set is insufficient for the claim")]
    InsufficientAssumption(),
    #[error("no claim found for assumption {0:?}")]
    NoSupportingClaim(Box<Model>),
    #[error("claimed count is {0}, but verified count is {1}")]
    WrongCount(BigUint, BigUint),
    #[error("child component variables are not a subset of parent variables")]
    ChildVarsInvalid(),
    #[error("child component clauses are not a subset of parent clauses")]
    ChildClausesInvalid(),
    #[error("child component variables do not cover parent component")]
    ChildVarsInsufficient(),
    #[error("child component clauses do not cover parent component")]
    ChildClausesInsufficient(),
    #[error("the join assumption does not cover variable intersection")]
    JoinAssumptionInsufficient(),
    #[error("clause {0} of the child component {1} is illegal in join")]
    IllegalJoinClause(ClauseIndex, ComponentIndex),
    #[error("clause {0} of the child component {1} is illegal in extension")]
    IllegalExtensionClause(ClauseIndex, ComponentIndex),
    #[error("the assumption of this model claim is not a model")]
    AssumptionNotAModel(),
}

fn restrict_clause<'a, 'b: 'a>(
    clause: impl Iterator<Item = &'a Lit> + 'a,
    vars: &'b BTreeSet<Var>,
) -> impl Iterator<Item = Lit> + 'a {
    clause.filter_map(|l| {
        if vars.contains(&l.var()) {
            Some(*l)
        } else {
            None
        }
    })
}

fn negate_model<'a>(m: impl Iterator<Item = Lit> + 'a) -> impl Iterator<Item = Lit> + 'a {
    m.map(|l| -l)
}

fn lits_to_varisat(lits: impl IntoIterator<Item = Lit>) -> Vec<varisat::Lit> {
    lits.into_iter()
        .map(|l| l.signum() * l.var())
        .map(varisat::Lit::from_dimacs)
        .collect::<Vec<_>>()
}

impl<'t> Verifier<'t> {
    pub fn new(trace: &'t Trace) -> Self {
        Verifier {
            valid_join_subcomps: HashSet::new(),
            trace,
        }
    }

    /// checks that a given prefix set definition matches the associated component
    /// returns prefix set and component.
    fn prefix_set_matches_comp(
        &self,
        set_idx: PrefixSetIndex,
    ) -> Result<(&PrefixSet, &Component), VerificationError> {
        let prefixes = self.trace.get_prefixes(set_idx).unwrap();
        let comp = self.trace.components.get(&prefixes.component).unwrap();

        if !prefixes.vars.is_subset(&comp.vars) {
            return Err(VerificationError::InvalidPrefixVariables());
        }

        Ok((prefixes, comp))
    }

    pub fn verify_prefixes(&self, set_idx: PrefixSetIndex) -> Result<(), VerificationError> {
        let (prefixes, comp) = self.prefix_set_matches_comp(set_idx)?;

        // validity condition
        let mut validation_formula = CnfFormula::new();
        validation_formula.set_var_count(self.trace.n_vars);

        for cl in &comp.clauses {
            let lits = &self.trace.clauses[*cl].lits;
            let restricted = restrict_clause(lits.iter(), &comp.vars);
            let varisat_clause = lits_to_varisat(restricted);
            validation_formula.add_clause(&varisat_clause);
        }
        for l in &prefixes.assm {
            let varisat_clause = lits_to_varisat([*l]);
            validation_formula.add_clause(&varisat_clause);
        }
        for model in prefixes.all_models() {
            let negated = negate_model(model.iter().copied());
            let clause = lits_to_varisat(negated);
            validation_formula.add_clause(&clause);
        }

        let mut solver = varisat::Solver::new();
        solver.add_formula(&validation_formula);

        match solver.solve() {
            // clause is implied
            Ok(false) => Ok(()),
            // clause is not implied
            Ok(true) => {
                let lits: Vec<_> = solver
                    .model()
                    .unwrap()
                    .iter()
                    .map(|l| Lit::from_dimacs(l.to_dimacs()))
                    .collect();
                eprintln! {"{:?}", restrict_clause(lits.iter(), &prefixes.vars).collect::<Vec<_>>()};
                return Err(VerificationError::InvalidPrefixSet(set_idx, comp.index));
            }
            Err(e) => panic! {"sat solver error {:?}", e},
        }
    }

    pub fn verify_composition(
        &mut self,
        composition: &CompositionClaim,
    ) -> Result<(), VerificationError> {
        let (prefixes, comp) = self.prefix_set_matches_comp(composition.prefixes)?;
        let comp_id = comp.index;

        if !prefixes.assm.is_subset(&composition.assm) {
            return Err(VerificationError::InsufficientAssumption());
        }

        let mut count = BigUint::zero();
        for m in prefixes.find_models(&composition.assm) {
            count += self.lookup_subclaim_count(comp_id, &m)?;
        }

        if count != composition.count {
            return Err(VerificationError::WrongCount(
                composition.count.clone(),
                count,
            ));
        }

        Ok(())
    }

    fn lookup_subclaim_count(
        &self,
        component: ComponentIndex,
        assm: &Assumption,
    ) -> Result<BigUint, VerificationError> {
        if let Some(claim) = self.trace.find_claim(component, assm) {
            Ok(claim.count())
        } else {
            Err(VerificationError::NoSupportingClaim(Box::new(assm.clone())))
        }
    }

    fn join_subcomponents_valid(
        &mut self,
        component: &Component,
        children: &[&Component],
    ) -> Result<(), VerificationError> {
        let key = (
            component.index,
            children.iter().map(|comp| comp.index).collect(),
        );
        if self.valid_join_subcomps.contains(&key) {
            return Ok(());
        }

        if children.iter().any(|c| !c.vars.is_subset(&component.vars)) {
            return Err(VerificationError::ChildVarsInvalid());
        }
        if children
            .iter()
            .any(|c| !c.clauses.is_subset(&component.clauses))
        {
            return Err(VerificationError::ChildClausesInvalid());
        }

        // do subcomponents cover parent components?
        let vars_union = children.iter().fold(BTreeSet::new(), |acc, comp| {
            BTreeSet::from_iter(acc.union(&comp.vars).copied())
        });

        if vars_union != component.vars {
            return Err(VerificationError::ChildVarsInsufficient());
        }

        let clauses_union = children.iter().fold(BTreeSet::new(), |acc, comp| {
            BTreeSet::from_iter(acc.union(&comp.clauses).copied())
        });
        if clauses_union != component.clauses {
            return Err(VerificationError::ChildClausesInsufficient());
        }

        // are subcomponents compatible?
        for child_i in children {
            let i_only_vars = component.vars.difference(&child_i.vars);
            let i_only_vars = i_only_vars.copied().collect();

            for cl in &child_i.clauses {
                let clause = &self.trace.clauses[*cl];
                if !vars_disjoint(clause.lits.iter(), &i_only_vars) {
                    return Err(VerificationError::IllegalJoinClause(*cl, child_i.index));
                }
            }
        }

        self.valid_join_subcomps.insert(key);
        Ok(())
    }

    pub fn verify_join(&mut self, join: &JoinClaim) -> Result<(), VerificationError> {
        let component = self.trace.components.get(&join.component).unwrap();
        let assm_vars: BTreeSet<_> = vars_iter(join.assm.iter()).collect();
        let children: Vec<_> = join
            .child_components
            .iter()
            .map(|idx| self.trace.components.get(idx).unwrap())
            .collect();

        // check child component validity
        self.join_subcomponents_valid(component, &children)?;

        if !assm_vars.is_subset(&component.vars) {
            return Err(VerificationError::InvalidAssumptionVariables());
        }

        // are subcomponents mutually compatible?
        for child_i in &children {
            for child_j in &children {
                if child_i.index == child_j.index {
                    continue;
                }

                let intersection_vars = child_i.vars.intersection(&child_j.vars);
                let intersection_vars: BTreeSet<_> = intersection_vars.copied().collect();

                if !intersection_vars.is_subset(&assm_vars) {
                    return Err(VerificationError::JoinAssumptionInsufficient());
                }
            }
        }

        let mut count = BigUint::one();
        for child_i in &children {
            let child_assm = restrict_clause(join.assm.iter(), &child_i.vars).collect();
            count *= self.lookup_subclaim_count(child_i.index, &child_assm)?;
        }

        if count != join.count {
            return Err(VerificationError::WrongCount(join.count.clone(), count));
        }

        Ok(())
    }

    pub fn verify_extension(
        &mut self,
        extension: &ExtensionClaim,
    ) -> Result<(), VerificationError> {
        let comp = self.trace.components.get(&extension.component).unwrap();
        let subcomp = self.trace.components.get(&extension.subcomponent).unwrap();

        if !subcomp.vars.is_subset(&comp.vars) {
            return Err(VerificationError::ChildVarsInvalid());
        }
        if !subcomp.clauses.is_subset(&comp.clauses) {
            return Err(VerificationError::ChildClausesInvalid());
        }

        // check allowed clauses
        let introduced_vars = comp.vars.difference(&subcomp.vars).copied().collect();
        let restricted_assm = restrict_clause(extension.assm.iter(), &introduced_vars).collect();
        for cl in &subcomp.clauses {
            if !self.trace.clauses[*cl].lits.is_disjoint(&restricted_assm) {
                return Err(VerificationError::IllegalExtensionClause(
                    *cl,
                    subcomp.index,
                ));
            }
        }

        let child_assm = restrict_clause(extension.assm.iter(), &subcomp.vars).collect();
        let count = self.lookup_subclaim_count(subcomp.index, &child_assm)?;

        if count != extension.count {
            return Err(VerificationError::WrongCount(
                extension.count.clone(),
                count,
            ));
        }

        Ok(())
    }

    pub fn verify_model_claim(&mut self, mc: &ModelClaim) -> Result<(), VerificationError> {
        let comp = self.trace.components.get(&mc.component).unwrap();
        let mc_vars = vars_iter(mc.model.iter()).collect();
        if comp.vars != mc_vars {
            return Err(VerificationError::InvalidAssumptionVariables());
        }
        for cl in &comp.clauses {
            if !mc
                .model
                .iter()
                .any(|l| self.trace.clauses[*cl].lits.contains(l))
            {
                return Err(VerificationError::AssumptionNotAModel());
            }
        }
        Ok(())
    }

    pub fn verify_claim(&mut self, claim: &Claim) -> Result<(), VerificationError> {
        match claim {
            Claim::Composition(c) => self.verify_composition(c),
            Claim::Join(c) => self.verify_join(c),
            Claim::Extension(c) => self.verify_extension(c),
            Claim::Model(c) => self.verify_model_claim(c),
        }
    }
}
