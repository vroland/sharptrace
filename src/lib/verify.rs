use crate::utils::{restrict_sorted_clause, vars_disjoint, vars_iter};
use crate::*;
use num_bigint::BigUint;
use num_traits::identities::{One, Zero};
use std::collections::HashSet;
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

fn is_subset<T: PartialEq>(s1: &[T], s2: &[T]) -> bool {
    s1.iter().all(|v| s2.contains(v))
}

fn is_sorted_subset(s1: &[Var], s2: &[Var]) -> bool {
    s1.iter().all(|v| s2.binary_search(v).is_ok())
}

fn difference<T: PartialEq + Copy + Ord>(s1: &[T], s2: &[T]) -> Vec<T> {
    s1.iter()
        .filter(|v| !s2.binary_search(v).is_ok())
        .copied()
        .collect()
}

fn intersection<T: PartialEq + Copy + Ord>(s1: &[T], s2: &[T]) -> Vec<T> {
    s1.iter()
        .filter(|v| s2.binary_search(v).is_ok())
        .copied()
        .collect()
}

impl<'t> Verifier<'t> {
    pub fn new(trace: &'t Trace) -> Self {
        Verifier {
            valid_join_subcomps: HashSet::new(),
            trace,
        }
    }

    pub fn verify_composition(
        &self,
        composition: &CompositionClaim,
    ) -> Result<(), VerificationError> {
        let proof = self.trace.get_proof(composition.proof).unwrap();
        let comp = self.trace.get_component(&proof.component).unwrap();

        if !proof.is_exhaustive_for(&composition.assm) {
            return Err(VerificationError::InvalidExhaustivenessProof(
                proof.index,
                comp.index,
            ));
        }

        let mut count = BigUint::zero();
        for claim in self
            .trace
            .find_claims(proof.component, &proof.get_previx_vars())
            .unwrap()
            .filter(|claim| is_subset(&composition.assm, claim.assumption()))
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
        &self,
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

        if children
            .iter()
            .any(|c| !is_sorted_subset(&c.vars, &component.vars))
        {
            return Err(VerificationError::ChildVarsInvalid());
        }
        if children
            .iter()
            .any(|c| !is_sorted_subset(&c.clauses, &component.clauses))
        {
            return Err(VerificationError::ChildClausesInvalid());
        }

        // do subcomponents cover parent components?
        let mut vars_union = children.iter().fold(Vec::new(), |mut acc, comp| {
            acc.extend_from_slice(&comp.vars);
            acc
        });
        vars_union.sort_unstable();
        vars_union.dedup();

        if vars_union != component.vars {
            return Err(VerificationError::ChildVarsInsufficient());
        }

        let mut clauses_union = children.iter().fold(Vec::new(), |mut acc, comp| {
            acc.extend_from_slice(&comp.clauses);
            acc
        });
        clauses_union.sort_unstable();
        clauses_union.dedup();

        if clauses_union != component.clauses {
            return Err(VerificationError::ChildClausesInsufficient());
        }

        // are subcomponents compatible?
        for child_i in children {
            let i_only_vars = difference(&component.vars, &child_i.vars);

            for cl in &child_i.clauses {
                let clause = &self.trace.clauses[*cl as usize];
                if !vars_disjoint(clause.lits.iter(), &i_only_vars) {
                    return Err(VerificationError::IllegalJoinClause(*cl, child_i.index));
                }
            }
        }

        //self.valid_join_subcomps.insert(key);
        Ok(())
    }

    pub fn verify_join(&self, join: &JoinClaim) -> Result<(), VerificationError> {
        let component = self.trace.get_component(&join.component).unwrap();
        let assm_vars: Vec<_> = vars_iter(join.assm.iter()).collect();
        let children: Vec<_> = join
            .child_components
            .iter()
            .map(|idx| self.trace.get_component(idx).unwrap())
            .collect();

        // check child component validity
        self.join_subcomponents_valid(component, &children)?;

        if !is_sorted_subset(&assm_vars, &component.vars) {
            return Err(VerificationError::InvalidAssumptionVariables());
        }

        // are subcomponents mutually compatible?
        for child_i in &children {
            for child_j in &children {
                if child_i.index == child_j.index {
                    continue;
                }

                let intersection_vars = intersection(&child_i.vars, &child_j.vars);
                if !is_sorted_subset(&intersection_vars, &assm_vars) {
                    return Err(VerificationError::JoinAssumptionInsufficient());
                }
            }
        }

        let mut count = BigUint::one();
        for child_i in &children {
            let child_assm = restrict_sorted_clause(join.assm.iter(), &child_i.vars)
                .copied()
                .collect();
            count *= self.lookup_subclaim_count(child_i.index, &child_assm)?;
        }

        if count != join.count {
            return Err(VerificationError::WrongCount(join.count.clone(), count));
        }

        Ok(())
    }

    pub fn verify_extension(&self, extension: &ExtensionClaim) -> Result<(), VerificationError> {
        let comp = self.trace.get_component(&extension.component).unwrap();
        let subcomp = self.trace.get_component(&extension.subcomponent).unwrap();

        if !is_sorted_subset(&subcomp.vars, &comp.vars) {
            return Err(VerificationError::ChildVarsInvalid());
        }
        if !is_sorted_subset(&subcomp.clauses, &comp.clauses) {
            return Err(VerificationError::ChildClausesInvalid());
        }

        // check allowed clauses
        let introduced_vars = difference(&comp.vars, &subcomp.vars);
        let restricted_assm: Vec<_> =
            restrict_sorted_clause(extension.assm.iter(), &introduced_vars)
                .copied()
                .collect();
        for cl in &subcomp.clauses {
            if self.trace.clauses[*cl as usize]
                .lits
                .iter()
                .any(|l| restricted_assm.contains(l))
            {
                return Err(VerificationError::IllegalExtensionClause(
                    *cl,
                    subcomp.index,
                ));
            }
        }

        let child_assm = restrict_sorted_clause(extension.assm.iter(), &subcomp.vars)
            .copied()
            .collect();
        let count = self.lookup_subclaim_count(subcomp.index, &child_assm)?;

        if count != extension.count {
            return Err(VerificationError::WrongCount(
                extension.count.clone(),
                count,
            ));
        }

        Ok(())
    }

    pub fn verify_model_claim(&self, mc: &ModelClaim) -> Result<(), VerificationError> {
        let comp = self.trace.get_component(&mc.component).unwrap();
        let mut mc_vars: Vec<_> = vars_iter(mc.assm.iter()).collect();
        mc_vars.sort_unstable();
        if comp.vars != mc_vars {
            return Err(VerificationError::InvalidAssumptionVariables());
        }
        for cl in &comp.clauses {
            if !mc
                .assm
                .iter()
                .any(|l| self.trace.clauses[*cl as usize].lits.contains(l))
            {
                return Err(VerificationError::AssumptionNotAModel());
            }
        }
        Ok(())
    }

    pub fn verify_claim(&self, claim: &Claim) -> Result<(), VerificationError> {
        match claim {
            Claim::Composition(c) => self.verify_composition(c),
            Claim::Join(c) => self.verify_join(c),
            Claim::Extension(c) => self.verify_extension(c),
            Claim::Model(c) => self.verify_model_claim(c),
        }
    }
}
