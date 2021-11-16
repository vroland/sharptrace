use num_bigint::BigUint;
use num_traits::identities::One;
use radix_trie::{Trie, TrieCommon};
use std::collections::{BTreeMap, BTreeSet};

mod parse;
mod verify;

pub use parse::{BodyParser, HeaderParser, IntegrityError, ParseError};
pub use verify::{VerificationError, Verifier};

pub type Var = isize;
pub type Lit = isize;

/// A clause index.
pub type ClauseIndex = usize;
/// A component index.
pub type ComponentIndex = usize;
/// A model list index.
pub type ListIndex = usize;

pub fn vars(lits: &[Lit]) -> Vec<Var> {
    lits.iter().map(|l| l.abs()).collect()
}

pub fn vars_set(lits: &[Lit]) -> BTreeSet<Var> {
    BTreeSet::from_iter(lits.iter().map(|l| l.abs()))
}

#[derive(Debug, Clone)]
pub struct Clause {
    pub index: ClauseIndex,
    pub lits: Vec<Lit>,
}

#[derive(Debug, Clone)]
pub struct Component {
    pub index: ComponentIndex,
    pub vars: BTreeSet<Var>,
    pub clauses: BTreeSet<ClauseIndex>,
}

#[derive(Debug, Clone)]
pub struct ModelList {
    pub index: ListIndex,
    pub component: ComponentIndex,
    pub vars: BTreeSet<Var>,
    pub clauses: BTreeSet<ClauseIndex>,
    pub assm: Vec<Lit>,
    pub models: Trie<Vec<Lit>, ()>,
}

#[derive(Debug, Clone)]
pub struct ModelClaim {
    pub list: ListIndex,
    pub model: Vec<Lit>,
}

#[derive(Debug, Clone)]
pub struct CompositionClaim {
    pub list: ListIndex,
    pub count: BigUint,
    pub assm: Vec<Lit>,
}

#[derive(Debug, Clone)]
pub struct JoinClaim {
    pub component: ComponentIndex,
    pub count: BigUint,
    pub assm: Vec<Lit>,
    pub child_components: Vec<ComponentIndex>,
}

#[derive(Debug, Clone)]
pub struct ExtensionClaim {
    pub list: ListIndex,
    pub subcomponent: ComponentIndex,
    pub count: BigUint,
    pub assm: Vec<Lit>,
}

#[derive(Debug, Clone)]
pub enum Claim {
    Model(ModelClaim),
    Composition(CompositionClaim),
    Join(JoinClaim),
    Extension(ExtensionClaim),
}

impl Claim {
    pub fn count(&self) -> BigUint {
        match self {
            Claim::Model(_) => BigUint::one(),
            Claim::Composition(claim) => claim.count.clone(),
            Claim::Join(claim) => claim.count.clone(),
            Claim::Extension(claim) => claim.count.clone(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Trace {
    pub n_vars: usize,
    pub n_clauses: usize,
    pub clauses: Vec<Clause>,
    pub components: BTreeMap<ComponentIndex, Component>,
    lists: BTreeMap<ListIndex, ModelList>,
    claims: BTreeMap<ComponentIndex, Trie<Vec<Lit>, Claim>>,
}

pub fn litcmp(l1: &Lit, l2: &Lit) -> std::cmp::Ordering {
    l1.abs().cmp(&l2.abs())
}

impl Trace {
    /// returns true if v is a valid variable of this trace.
    pub fn check_var(&self, v: Var) -> bool {
        v > 0 && (v as usize) <= self.n_vars
    }

    /// returns true if l is a valid literal of a variable of this trace.
    pub fn check_lit(&self, l: Lit) -> bool {
        self.check_var(l.abs())
    }

    pub fn new(vars: usize, clauses: usize) -> Self {
        Trace {
            n_vars: vars,
            n_clauses: clauses,
            clauses: Vec::new(),
            components: BTreeMap::new(),
            lists: BTreeMap::new(),
            claims: BTreeMap::new(),
        }
    }

    /// Insert a model list.
    pub fn insert_list(&mut self, list: ModelList) -> Result<(), IntegrityError> {
        if !self.components.contains_key(&list.component) {
            return Err(IntegrityError::MissingComponentDef(list.component));
        }
        let list_index = list.index;
        if self.lists.insert(list_index, list).is_some() {
            return Err(IntegrityError::DuplicateListId(list_index));
        }
        Ok(())
    }

    pub fn insert_model(&mut self, list: ListIndex, model: Vec<Lit>) -> Result<(), IntegrityError> {
        let mlist = match self.lists.get_mut(&list) {
            Some(l) => l,
            None => return Err(IntegrityError::MissingModelList(list)),
        };
        if vars_set(&model) != mlist.vars {
            return Err(IntegrityError::InvalidModel(list));
        }
        if mlist.models.insert(model, ()).is_some() {
            return Err(IntegrityError::DuplicateModel(list));
        }
        Ok(())
    }

    pub fn get_list(&self, list: ListIndex) -> Option<&ModelList> {
        self.lists.get(&list)
    }

    pub fn get_lists(&self) -> impl Iterator<Item = &ListIndex> {
        self.lists.keys()
    }

    pub fn get_claims(&self) -> impl Iterator<Item = &Claim> {
        self.claims.values().map(|t| t.values()).flatten()
    }

    pub fn get_component_claims(&self, comp: ComponentIndex) -> Option<&Trie<Vec<Lit>, Claim>> {
        self.claims.get(&comp)
    }

    fn insert_claim_unchecked(
        &mut self,
        comp: ComponentIndex,
        assm: Vec<Lit>,
        claim: Claim,
    ) -> Result<(), IntegrityError> {
        if !self.components.contains_key(&comp) {
            return Err(IntegrityError::MissingComponentDef(comp));
        }
        let comp_claims = match self.claims.get_mut(&comp) {
            Some(claims) => claims,
            None => {
                self.claims.insert(comp, Trie::new());
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
        let comp_id = match self.lists.get(&claim.list) {
            Some(l) => l.component,
            None => return Err(IntegrityError::MissingModelList(claim.list)),
        };
        self.insert_claim_unchecked(comp_id, claim.assm.clone(), Claim::Composition(claim))
    }

    pub fn insert_model_claim(&mut self, claim: ModelClaim) -> Result<(), IntegrityError> {
        let comp_id = match self.lists.get(&claim.list) {
            Some(l) => l.component,
            None => return Err(IntegrityError::MissingModelList(claim.list)),
        };
        self.insert_claim_unchecked(comp_id, claim.model.clone(), Claim::Model(claim))
    }

    pub fn insert_join_claim(&mut self, claim: JoinClaim) -> Result<(), IntegrityError> {
        self.insert_claim_unchecked(claim.component, claim.assm.clone(), Claim::Join(claim))
    }

    pub fn insert_extension_claim(&mut self, claim: ExtensionClaim) -> Result<(), IntegrityError> {
        let comp_id = match self.lists.get(&claim.list) {
            Some(l) => l.component,
            None => return Err(IntegrityError::MissingModelList(claim.list)),
        };
        if !self.components.contains_key(&claim.subcomponent) {
            return Err(IntegrityError::MissingComponentDef(claim.subcomponent));
        }
        self.insert_claim_unchecked(comp_id, claim.assm.clone(), Claim::Extension(claim))
    }

    pub fn print_stats(&self) {
        eprintln! {"clauses: {}", self.n_clauses};
        eprintln! {"variables: {}", self.n_vars};
        eprintln! {"components: {}", self.components.len()};
        eprintln! {"model lists: {} with {} models in total", self.lists.len(), self.lists.values().fold(0, |acc, l| acc + l.models.values().count())};
        eprintln! {"claims: {}", self.claims.values().fold(0, |acc, t| acc + t.values().count())};
    }
}
