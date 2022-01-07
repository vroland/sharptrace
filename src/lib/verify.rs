use crate::proofs::ExhaustivenessProof;
use crate::utils::{vars_disjoint, vars_iter};
use crate::*;
use num_bigint::BigUint;
use num_traits::identities::{One, Zero};
use std::collections::{BTreeSet, HashSet};
use thiserror::Error;

#[derive(Debug)]
pub struct Verifier<'t> {
    // sets of proven component - subcomponent combinations for join
    valid_join_subcomps: HashSet<(ComponentIndex, Vec<ComponentIndex>)>,
    trace: &'t Trace,
}

#[derive(Debug, Clone, Error)]
pub enum VerificationError {
    #[error("the exhaustiveness proof {0} is not applicable for the claim with assm {1:?}")]
    NoApplicableProof(ProofIndex, Box<Assumption>),
    #[error("assumption variables are not a subset of component variables")]
    InvalidAssumptionVariables(),
    #[error("the assignment {0:?} is not a model")]
    NotAModel(Box<Assumption>),
    #[error("exhaustiveness proof {0} is invalid for component {1}")]
    InvalidExhaustivenessProof(ProofIndex, ComponentIndex),
    #[error("assumption of proof is insufficient for the claim")]
    InsufficientAssumption(),
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
    #[error("no claim found for assumption {0:?}")]
    NoSupportingClaim(Box<Assumption>),
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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum BcpResult {
    Success,
    Conflict,
}

impl<'t> Verifier<'t> {
    pub fn new(trace: &'t Trace) -> Self {
        Verifier {
            valid_join_subcomps: HashSet::new(),
            trace,
        }
    }

    /// checks that a given proof matches the claim
    /// returns proof and chosed exhaustiveness statement.
    fn proof_for_claim(
        &self,
        claim: &CompositionClaim,
    ) -> Result<(&ExhaustivenessProof, &(Assumption, BTreeSet<Var>)), VerificationError> {
        let proof = self.trace.get_proof(claim.proof).unwrap();
        let comp = self.trace.components.get(&proof.component).unwrap();

        for stmt in &proof.claimed_exhaustive_for {
            if stmt.1.is_subset(&comp.vars) && stmt.0 == claim.assm {
                return Ok((proof, stmt));
            }
        }
        Err(VerificationError::NoApplicableProof(
            claim.proof,
            Box::new(claim.assm.clone()),
        ))
    }

    pub fn verify_exhaustiveness(
        &self,
        proof: &ExhaustivenessProof,
        assm: &Assumption,
        pvars: &BTreeSet<Var>,
    ) -> Result<(), VerificationError> {
        let comp = self.trace.components.get(&proof.component).unwrap();

        let mut formula = vec![];

        // exhaustiveness formula - assumption
        for lit in assm {
            formula.push(vec![*lit]);
        }

        // exhaustiveness formula - component clauses
        for cl in &comp.clauses {
            let lits = &self.trace.clauses[*cl].lits;
            let restricted = restrict_clause(lits.iter(), &comp.vars);
            formula.push(restricted.collect());
        }

        let claims = self.trace.find_claims(comp.index, pvars.clone()).unwrap();

        for claim in claims {
            let negated = negate_model(claim.assumption().iter().copied());
            formula.push(negated.collect());
        }

        // the final empty clause step
        let final_step = [vec![]];

        for step in proof.steps.iter().chain(final_step.iter()) {
            if !Self::is_rup_inference(&formula, &step) {
                return Err(VerificationError::InvalidExhaustivenessProof(
                    proof.index,
                    comp.index,
                ));
            }
            formula.push(step.clone());
        }
        Ok(())
    }

    fn unit_propagate(clauses: &mut Vec<Vec<Lit>>) -> BcpResult {
        loop {
            if clauses.is_empty() {
                return BcpResult::Success;
            }

            let (unit, cli) = match clauses.iter().enumerate().find(|c| c.1.len() == 1) {
                Some((idx, u)) => (u[0], idx),
                None => return BcpResult::Success,
            };

            for cl in clauses.iter_mut() {
                if cl.contains(&-unit) {
                    cl.retain(|l| *l != -unit);
                    if cl.len() == 0 {
                        return BcpResult::Conflict;
                    }
                }
            }

            // remove the propagated unit clause
            let last = clauses.len() - 1;
            clauses.swap(cli, last);
            clauses.pop();
        }
    }

    fn is_rup_inference(clauses: &Vec<Vec<Lit>>, clause: &Vec<Lit>) -> bool {
        let mut pre = clauses.clone();
        for unit in negate_model(clause.iter().copied()) {
            pre.push(vec![unit]);
        }
        Self::unit_propagate(&mut pre) == BcpResult::Conflict
    }

    pub fn verify_composition(
        &mut self,
        composition: &CompositionClaim,
    ) -> Result<(), VerificationError> {
        let (proof, (assm, vars)) = self.proof_for_claim(composition)?;

        self.verify_exhaustiveness(proof, assm, vars)?;

        let mut count = BigUint::zero();
        for claim in self
            .trace
            .find_claims(proof.component, vars.clone())
            .unwrap()
            .filter(|claim| claim.assumption().is_superset(&composition.assm))
        {
            count += claim.count()
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
        let mc_vars = vars_iter(mc.assm.iter()).collect();
        if comp.vars != mc_vars {
            return Err(VerificationError::InvalidAssumptionVariables());
        }
        for cl in &comp.clauses {
            if !mc
                .assm
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
