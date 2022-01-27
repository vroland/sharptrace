use crate::proofs::ExhaustivenessProof;
use crate::utils::vars_iter;
use crate::{Assumption, ClauseIndex, ComponentIndex, Index, IntegrityError, Lit, ProofIndex, Var};
use num_bigint::BigUint;
use num_traits::identities::One;
use std::collections::{BTreeMap, HashMap};
use std::fmt;

#[derive(Debug, Clone)]
pub struct Clause {
    pub index: ClauseIndex,
    pub lits: Vec<Lit>,
}

#[derive(Debug, Clone)]
pub struct Component {
    pub index: ComponentIndex,
    pub vars: Vec<Var>,
    pub clauses: Vec<ClauseIndex>,
}

#[derive(Debug, Clone)]
pub struct ModelClaim {
    pub component: ComponentIndex,
    pub assm: Assumption,
}

#[derive(Debug, Clone)]
pub struct CompositionClaim {
    pub proof: ProofIndex,
    pub count: BigUint,
    pub assm: Assumption,
}

#[derive(Debug, Clone)]
pub struct JoinClaim {
    pub component: ComponentIndex,
    pub count: BigUint,
    pub assm: Assumption,
    pub child_components: Vec<ComponentIndex>,
}

#[derive(Debug, Clone)]
pub struct ExtensionClaim {
    pub component: ComponentIndex,
    pub subcomponent: ComponentIndex,
    pub count: BigUint,
    pub assm: Assumption,
}

#[derive(Debug, Clone)]
pub enum Claim {
    Model(ModelClaim),
    Composition(CompositionClaim),
    Join(JoinClaim),
    Extension(ExtensionClaim),
}

impl Claim {
    pub fn tag(&self) -> &'static str {
        match self {
            Claim::Model(_) => "Model",
            Claim::Composition(_) => "Composition",
            Claim::Join(_) => "Join",
            Claim::Extension(_) => "Extension",
        }
    }
    pub fn count(&self) -> BigUint {
        match self {
            Claim::Model(_) => BigUint::one(),
            Claim::Composition(claim) => claim.count.clone(),
            Claim::Join(claim) => claim.count.clone(),
            Claim::Extension(claim) => claim.count.clone(),
        }
    }

    pub fn assumption(&self) -> &Assumption {
        match self {
            Claim::Model(claim) => &claim.assm,
            Claim::Composition(claim) => &claim.assm,
            Claim::Join(claim) => &claim.assm,
            Claim::Extension(claim) => &claim.assm,
        }
    }
}

impl fmt::Display for Claim {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} claim: {} models under {:?}",
            self.tag(),
            self.count(),
            self.assumption()
        )
    }
}

#[derive(Debug)]
pub struct Trace {
    pub n_vars: Index,
    pub n_orig_clauses: Index,
    pub clauses: Vec<Clause>,
    components: HashMap<ComponentIndex, Component>,
    proofs: BTreeMap<ProofIndex, ExhaustivenessProof>,
    claims: BTreeMap<ComponentIndex, Vec<Claim>>,
}

impl Trace {
    /// returns true if v is a valid variable of this trace.
    pub fn check_var(&self, v: Var) -> bool {
        v > 0 && (v as Index) <= self.n_vars
    }

    /// returns true if l is a valid literal of a variable of this trace.
    pub fn check_lit(&self, l: Lit) -> bool {
        self.check_var(l.var())
    }

    pub fn new(vars: Index, clauses: Index) -> Self {
        Trace {
            n_vars: vars,
            n_orig_clauses: clauses,
            clauses: Vec::new(),
            components: HashMap::new(),
            proofs: BTreeMap::new(),
            claims: BTreeMap::new(),
        }
    }

    pub fn comp_id_of(&self, claim: &Claim) -> ComponentIndex {
        match claim {
            Claim::Model(c) => c.component,
            Claim::Extension(c) => c.component,
            Claim::Join(c) => c.component,
            Claim::Composition(c) => self.get_proof(c.proof).unwrap().component,
        }
    }

    pub fn get_proof(&self, proof: ProofIndex) -> Option<&ExhaustivenessProof> {
        self.proofs.get(&proof)
    }

    pub fn get_claims(&self) -> impl Iterator<Item = &Claim> {
        self.claims.values().map(|t| t.iter()).flatten()
    }

    pub fn get_component(&self, index: &ComponentIndex) -> Option<&Component> {
        self.components.get(index)
    }

    pub fn get_components(&self) -> impl Iterator<Item = &Component> {
        self.components.values()
    }

    pub fn get_component_claims(
        &self,
        comp: ComponentIndex,
    ) -> Option<impl Iterator<Item = &Claim>> {
        self.claims.get(&comp).map(|t| t.iter())
    }

    pub fn add_exhaustiveness_proof(
        &mut self,
        proof: ExhaustivenessProof,
    ) -> Result<(), IntegrityError> {
        if !self.components.contains_key(&proof.component) {
            return Err(IntegrityError::MissingComponentDef(proof.component));
        }
        let proof_index = proof.index;
        if self.proofs.insert(proof_index, proof).is_some() {
            return Err(IntegrityError::DuplicateProofId(proof_index));
        }
        Ok(())
    }

    pub fn has_join_claims(&self, comp: ComponentIndex) -> bool {
        self.get_component_claims(comp)
            .map(|mut cl| {
                cl.find(|c| match c {
                    Claim::Join(_) => true,
                    _ => false,
                })
                .is_some()
            })
            .unwrap_or(false)
    }

    pub fn insert_component(&mut self, comp: Component) -> Result<(), IntegrityError> {
        let index = comp.index;
        if self.components.insert(index, comp).is_some() {
            return Err(IntegrityError::DuplicateComponentId(index));
        }
        self.claims.insert(index, vec![]);
        Ok(())
    }

    pub fn find_claims<'a, 'b: 'a>(
        &'a self,
        comp: ComponentIndex,
        assm_vars: &'b [Var],
    ) -> Option<impl Iterator<Item = &'a Claim>> {
        self.claims.get(&comp).map(move |c| {
            c.iter().filter(|claim| {
                claim.assumption().len() == assm_vars.len()
                    && vars_iter(claim.assumption().iter()).all(|v| assm_vars.contains(&v))
            })
        })
    }

    pub fn find_claim(&self, comp: ComponentIndex, assm: &Assumption) -> Option<&Claim> {
        self.claims
            .get(&comp)
            .and_then(move |c| c.iter().find(move |claim| claim.assumption() == assm))
    }

    fn insert_claim_unchecked(
        &mut self,
        comp: ComponentIndex,
        claim: Claim,
    ) -> Result<(), IntegrityError> {
        if !self.components.contains_key(&comp) {
            return Err(IntegrityError::MissingComponentDef(comp));
        }

        // check for duplicate claims
        let duplicate = self.find_claim(comp, claim.assumption()).is_some();

        if duplicate {
            return Err(IntegrityError::DuplicateClaim(comp));
        }
        assert! {self.claims.contains_key(&comp)};
        self.claims.get_mut(&comp).unwrap().push(claim);
        Ok(())
    }

    pub fn insert_composition_claim(
        &mut self,
        claim: CompositionClaim,
    ) -> Result<(), IntegrityError> {
        let comp_id = match self.proofs.get(&claim.proof) {
            Some(l) => l.component,
            None => return Err(IntegrityError::MissingExhaustivenessProof(claim.proof)),
        };
        self.insert_claim_unchecked(comp_id, Claim::Composition(claim))
    }

    pub fn insert_model_claim(&mut self, claim: ModelClaim) -> Result<(), IntegrityError> {
        self.insert_claim_unchecked(claim.component, Claim::Model(claim))
    }

    pub fn insert_join_claim(&mut self, claim: JoinClaim) -> Result<(), IntegrityError> {
        self.insert_claim_unchecked(claim.component, Claim::Join(claim))
    }

    pub fn insert_extension_claim(&mut self, claim: ExtensionClaim) -> Result<(), IntegrityError> {
        if !self.components.contains_key(&claim.component) {
            return Err(IntegrityError::MissingComponentDef(claim.component));
        };
        if !self.components.contains_key(&claim.subcomponent) {
            return Err(IntegrityError::MissingComponentDef(claim.subcomponent));
        }
        self.insert_claim_unchecked(claim.component, Claim::Extension(claim))
    }

    pub fn print_stats(&self) {
        eprintln! {"clauses: {}", self.n_orig_clauses};
        eprintln! {"variables: {}", self.n_vars};
        eprintln! {"components: {}", self.components.len()};
        eprintln! {"proofs: {} with {} steps in total", self.proofs.len(), self.proofs.values().fold(0, |acc, l| acc + l.len())};
        eprintln! {"claims: {}", self.claims.values().fold(0, |acc, t| acc + t.len())};
    }

    pub fn find_root_claim(&self) -> Result<&Claim, IntegrityError> {
        match self
            .components
            .values()
            .find(|c| {
                c.vars.len() == self.n_vars as usize
                    && c.clauses.len() == self.n_orig_clauses as usize
            })
            .and_then(|c| self.find_claim(c.index, &Vec::new()))
        {
            Some(claim) => Ok(claim),
            None => Err(IntegrityError::NoRootClaim()),
        }
    }
}
