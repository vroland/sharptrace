use crate::proofs::ExhaustivenessProof;
use crate::{Assumption, ClauseIndex, ComponentIndex, Index, IntegrityError, Lit, ProofIndex, Var};
use num_bigint::BigUint;
use num_traits::identities::One;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;
use std::hash::{Hash, Hasher};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
    pub index: ClauseIndex,
    pub lits: Vec<Lit>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Component {
    pub index: ComponentIndex,
    pub vars: Vec<Var>,
    pub clauses: Vec<ClauseIndex>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModelClaim {
    pub component: ComponentIndex,
    pub assm: Assumption,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompositionClaim {
    pub component: ComponentIndex,
    pub proof: ProofIndex,
    pub count: BigUint,
    pub assm: Assumption,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JoinClaim {
    pub component: ComponentIndex,
    pub count: BigUint,
    pub assm: Assumption,
    pub child_components: Vec<ComponentIndex>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtensionClaim {
    pub component: ComponentIndex,
    pub subcomponent: ComponentIndex,
    pub count: BigUint,
    pub assm: Assumption,
}

#[derive(Debug, Clone, Eq)]
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

    pub fn component(&self) -> ComponentIndex {
        match self {
            Claim::Model(claim) => claim.component,
            Claim::Composition(claim) => claim.component,
            Claim::Join(claim) => claim.component,
            Claim::Extension(claim) => claim.component,
        }
    }
}

impl Hash for Claim {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.assumption().hash(state);
        self.component().hash(state);
    }
}

// FIXME: a bit hacky to use eq for this, but this makes
// it easier to use a built-in hashmap for de-duplication
impl PartialEq for Claim {
    fn eq(&self, other: &Self) -> bool {
        self.component() == other.component() && self.assumption() == other.assumption()
    }
}

impl PartialOrd for Claim {
    fn partial_cmp(&self, other: &Claim) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Claim {
    fn cmp(&self, other: &Claim) -> Ordering {
        (self.component(), self.assumption()).cmp(&(other.component(), other.assumption()))
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
    proofs: BTreeMap<(ComponentIndex, ProofIndex), ExhaustivenessProof>,
    claims: BTreeMap<ComponentIndex, BTreeSet<Claim>>,
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

    pub fn get_proof(
        &self,
        comp: ComponentIndex,
        proof: ProofIndex,
    ) -> Option<&ExhaustivenessProof> {
        self.proofs.get(&(comp, proof))
    }

    pub fn get_proofs(&self) -> impl Iterator<Item = &ExhaustivenessProof> {
        self.proofs.values()
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
        let comp = proof.component;
        if !self.components.contains_key(&comp) {
            return Err(IntegrityError::MissingComponentDef(comp));
        }
        let proof_index = proof.index;
        if self.proofs.insert((comp, proof_index), proof).is_some() {
            return Err(IntegrityError::AmbiguousProofId(comp, proof_index));
        }
        Ok(())
    }

    pub fn has_join_claims(&self, comp: ComponentIndex) -> bool {
        self.get_component_claims(comp)
            .map(|mut cl| cl.any(|c| matches! {c, Claim::Join(_)}))
            .unwrap_or(false)
    }

    pub fn insert_component(&mut self, mut comp: Component) -> Result<(), IntegrityError> {
        let index = comp.index;
        comp.vars.shrink_to_fit();
        comp.clauses.shrink_to_fit();
        if self.components.insert(index, comp).is_some() {
            return Err(IntegrityError::DuplicateComponentId(index));
        }
        self.claims.insert(index, BTreeSet::new());
        Ok(())
    }

    pub fn find_claims<'a, 'b: 'a>(
        &'a self,
        comp: ComponentIndex,
        assm_vars: &'b [Var],
        assm: &'b [Lit],
    ) -> Option<impl Iterator<Item = &'a Claim>> {
        let f = |v: &Var, other| {
            if let Some(l) = assm.iter().find(|l| l.var() == *v) {
                *l
            } else {
                Lit::from_dimacs(other)
            }
        };
        let low_assm = assm_vars
            .iter()
            .map(|v| f(v, -(*v as i32)))
            .collect::<Vec<_>>();
        let high_assm = assm_vars
            .iter()
            .map(|v| f(v, *v as i32))
            .collect::<Vec<_>>();
        let norm_assm = assm_vars.iter().map(|v| f(v, 0)).collect::<Vec<_>>();
        let lowerbound = Claim::Model(ModelClaim {
            component: comp,
            assm: low_assm,
        });
        let upperbound = Claim::Model(ModelClaim {
            component: comp,
            assm: high_assm,
        });
        self.claims.get(&comp).map(move |s| {
            s.range(lowerbound..=upperbound).filter(move |c| {
                assm_vars.len() == c.assumption().len()
                    && c.assumption()
                        .iter()
                        .zip(assm_vars.iter())
                        .zip(norm_assm.iter())
                        .all(|((l, v), n)| l.var() == *v && (n.var() == 0 || n == l))
            })
        })
    }

    pub fn find_claim(&self, comp: ComponentIndex, assm: &[Lit]) -> Option<&Claim> {
        let dummy = Claim::Model(ModelClaim {
            assm: assm.to_vec(),
            component: comp,
        });
        self.claims.get(&comp).and_then(|c| c.get(&dummy))
    }

    /// check if this component may depend on itself for a join
    pub fn is_possibly_cyclic(&self, jc: &JoinClaim) -> bool {
        let jcomp = self.get_component(&jc.component).unwrap();
        let mut candidates = jc.child_components.clone();
        while let Some(c) = candidates.pop() {
            if jc.component == c {
                return true;
            }
            let comp = self.get_component(&c).unwrap();
            if jcomp.vars != comp.vars || jcomp.clauses != comp.clauses {
                continue;
            }
            for claim in self.get_component_claims(c).unwrap() {
                if let Claim::Join(join) = claim {
                    for child in &join.child_components {
                        if !candidates.contains(child) {
                            candidates.push(*child);
                        }
                    }
                }
            }
        }
        false
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

        let comp_claims = self.claims.get_mut(&comp).unwrap();
        comp_claims.insert(claim);
        Ok(())
    }

    pub fn insert_composition_claim(
        &mut self,
        mut claim: CompositionClaim,
    ) -> Result<(), IntegrityError> {
        if self.proofs.get(&(claim.component, claim.proof)).is_none() {
            return Err(IntegrityError::MissingProofForComp(
                claim.proof,
                claim.component,
            ));
        };
        claim.assm.shrink_to_fit();
        self.insert_claim_unchecked(claim.component, Claim::Composition(claim))
    }

    pub fn insert_model_claim(&mut self, mut claim: ModelClaim) -> Result<(), IntegrityError> {
        claim.assm.shrink_to_fit();
        self.insert_claim_unchecked(claim.component, Claim::Model(claim))
    }

    pub fn insert_join_claim(&mut self, mut claim: JoinClaim) -> Result<(), IntegrityError> {
        claim.assm.shrink_to_fit();
        self.insert_claim_unchecked(claim.component, Claim::Join(claim))
    }

    pub fn insert_extension_claim(
        &mut self,
        mut claim: ExtensionClaim,
    ) -> Result<(), IntegrityError> {
        claim.assm.shrink_to_fit();
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
        let is_tautology =
            |clause: &Clause| clause.lits.iter().any(|l| clause.lits.contains(&(-*l)));

        let result = self
            .components
            .values()
            .find(|c| {
                if c.vars.len() != self.n_vars as usize {
                    return false;
                }

                // input clauses that the component does not cover.
                // the first dummy clause is skipped.
                let mut missing_clauses = self.clauses[1..]
                    .iter()
                    .filter(|cl| !c.clauses.contains(&cl.index));

                // if some tautologies are not covered, we ignore them
                missing_clauses.all(is_tautology)
            })
            .and_then(|c| self.find_claim(c.index, &Vec::new()));

        match result {
            Some(claim) => Ok(claim),
            None => Err(IntegrityError::NoRootClaim()),
        }
    }
}
