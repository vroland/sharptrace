use crate::prefixes::*;
use crate::utils::vars_iter;
use crate::{
    Assumption, ClauseIndex, ComponentIndex, IntegrityError, Lit, Model, PrefixSetIndex, Var,
};
use num_bigint::BigUint;
use num_traits::identities::One;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt;

#[derive(Debug, Clone)]
pub struct Clause {
    pub index: ClauseIndex,
    pub lits: BTreeSet<Lit>,
}

#[derive(Debug, Clone)]
pub struct Component {
    pub index: ComponentIndex,
    pub vars: BTreeSet<Var>,
    pub clauses: BTreeSet<ClauseIndex>,
}

#[derive(Debug, Clone)]
pub struct ModelClaim {
    pub component: ComponentIndex,
    pub model: Model,
}

#[derive(Debug, Clone)]
pub struct CompositionClaim {
    pub prefixes: PrefixSetIndex,
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
            Claim::Model(claim) => &claim.model,
            Claim::Composition(claim) => &claim.assm,
            Claim::Join(claim) => &claim.assm,
            Claim::Extension(claim) => &claim.assm,
        }
    }

    pub fn component(&self) -> ComponentIndex {
        match self {
            Claim::Model(claim) => claim.component,
            Claim::Composition(claim) => claim.prefixes,
            Claim::Join(claim) => claim.component,
            Claim::Extension(claim) => claim.component,
        }
    }
}

impl fmt::Display for Claim {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} claim: {} models for component/prefix set {} under {:?}",
            self.tag(),
            self.count(),
            self.component(),
            self.assumption()
        )
    }
}

#[derive(Debug, Clone)]
pub struct Trace {
    pub n_vars: usize,
    pub n_orig_clauses: usize,
    pub clauses: Vec<Clause>,
    pub components: BTreeMap<ComponentIndex, Component>,
    prefix_sets: BTreeMap<PrefixSetIndex, PrefixSet>,
    claims: HashMap<ComponentIndex, BTreeMap<Assumption, Claim>>,
}

impl Trace {
    /// returns true if v is a valid variable of this trace.
    pub fn check_var(&self, v: Var) -> bool {
        v > 0 && (v as usize) <= self.n_vars
    }

    /// returns true if l is a valid literal of a variable of this trace.
    pub fn check_lit(&self, l: Lit) -> bool {
        self.check_var(l.var())
    }

    pub fn new(vars: usize, clauses: usize) -> Self {
        Trace {
            n_vars: vars,
            n_orig_clauses: clauses,
            clauses: Vec::new(),
            components: BTreeMap::new(),
            prefix_sets: BTreeMap::new(),
            claims: HashMap::new(),
        }
    }

    /// Insert a prefix set.
    pub fn insert_prefixes(&mut self, set: PrefixSet) -> Result<(), IntegrityError> {
        if !self.components.contains_key(&set.component) {
            return Err(IntegrityError::MissingComponentDef(set.component));
        }
        let set_index = set.index;
        if self.prefix_sets.insert(set_index, set).is_some() {
            return Err(IntegrityError::DuplicateSetId(set_index));
        }
        Ok(())
    }

    pub fn insert_model(
        &mut self,
        set: PrefixSetIndex,
        model: Model,
    ) -> Result<(), IntegrityError> {
        let pset = match self.prefix_sets.get_mut(&set) {
            Some(l) => l,
            None => return Err(IntegrityError::MissingPrefixSet(set)),
        };
        let model_vars = BTreeSet::from_iter(vars_iter(model.iter()));
        if model_vars != pset.vars {
            eprintln! {"assumption vars: {:?} prefix vars: {:?}", model_vars, pset.vars};
            return Err(IntegrityError::InvalidModel(Box::new(model)));
        }
        if !pset.insert(model) {
            return Err(IntegrityError::DuplicateModel(set));
        }
        Ok(())
    }

    pub fn get_prefixes(&self, set: PrefixSetIndex) -> Option<&PrefixSet> {
        self.prefix_sets.get(&set)
    }

    pub fn get_prefix_sets(&self) -> impl Iterator<Item = &PrefixSetIndex> {
        self.prefix_sets.keys()
    }

    pub fn get_claims(&self) -> impl Iterator<Item = &Claim> {
        self.claims.values().map(|t| t.values()).flatten()
    }

    pub fn has_join_claims(&self, comp: ComponentIndex) -> bool {
        self.claims
            .get(&comp)
            .and_then(|v| {
                Some(v.values().any(|c| match c {
                    Claim::Join(_) => true,
                    _ => false,
                }))
            })
            .unwrap_or(false)
    }

    pub fn component_claims(&self, comp: ComponentIndex) -> Option<&BTreeMap<Assumption, Claim>> {
        self.claims.get(&comp)
    }

    pub fn find_claim(&self, comp: ComponentIndex, assm: &Assumption) -> Option<&Claim> {
        self.claims.get(&comp).and_then(|c| c.get(assm))
    }

    fn insert_claim_unchecked(
        &mut self,
        comp: ComponentIndex,
        assm: Assumption,
        claim: Claim,
    ) -> Result<(), IntegrityError> {
        if !self.components.contains_key(&comp) {
            return Err(IntegrityError::MissingComponentDef(comp));
        }
        let comp_claims = match self.claims.get_mut(&comp) {
            Some(claims) => claims,
            None => {
                self.claims.insert(comp, BTreeMap::new());
                self.claims.get_mut(&comp).unwrap()
            }
        };
        if comp_claims.insert(assm, claim).is_some() {
            return Err(IntegrityError::DuplicateClaim(comp));
        }
        Ok(())
    }

    pub fn insert_composition_claim(
        &mut self,
        claim: CompositionClaim,
    ) -> Result<(), IntegrityError> {
        let comp_id = match self.prefix_sets.get(&claim.prefixes) {
            Some(l) => l.component,
            None => return Err(IntegrityError::MissingPrefixSet(claim.prefixes)),
        };
        self.insert_claim_unchecked(comp_id, claim.assm.clone(), Claim::Composition(claim))
    }

    pub fn insert_model_claim(&mut self, claim: ModelClaim) -> Result<(), IntegrityError> {
        self.insert_claim_unchecked(claim.component, claim.model.clone(), Claim::Model(claim))
    }

    pub fn insert_join_claim(&mut self, claim: JoinClaim) -> Result<(), IntegrityError> {
        self.insert_claim_unchecked(claim.component, claim.assm.clone(), Claim::Join(claim))
    }

    pub fn insert_extension_claim(&mut self, claim: ExtensionClaim) -> Result<(), IntegrityError> {
        if !self.components.contains_key(&claim.component) {
            return Err(IntegrityError::MissingComponentDef(claim.component));
        };
        if !self.components.contains_key(&claim.subcomponent) {
            return Err(IntegrityError::MissingComponentDef(claim.subcomponent));
        }
        self.insert_claim_unchecked(claim.component, claim.assm.clone(), Claim::Extension(claim))
    }

    pub fn print_stats(&self) {
        eprintln! {"clauses: {}", self.n_orig_clauses};
        eprintln! {"variables: {}", self.n_vars};
        eprintln! {"components: {}", self.components.len()};
        eprintln! {"prefix sets: {} with {} models in total", self.prefix_sets.len(), self.prefix_sets.values().fold(0, |acc, l| acc + l.len())};
        eprintln! {"claims: {}", self.claims.values().fold(0, |acc, t| acc + t.len())};
    }

    pub fn find_root_claim(&self) -> Result<&Claim, IntegrityError> {
        match self
            .components
            .values()
            .find(|c| c.vars.len() == self.n_vars && c.clauses.len() == self.n_orig_clauses)
            .and_then(|c| self.claims.get(&c.index).unwrap().get(&BTreeSet::new()))
        {
            Some(claim) => Ok(claim),
            None => Err(IntegrityError::NoRootClaim()),
        }
    }
}
