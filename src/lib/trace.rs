use crate::list::*;
use crate::utils::vars_subset;
use crate::{Assumption, ClauseIndex, ComponentIndex, IntegrityError, ListIndex, Lit, Model, Var};
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
    pub list: ListIndex,
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
            Claim::Composition(claim) => claim.list,
            Claim::Join(claim) => claim.component,
            Claim::Extension(claim) => claim.component,
        }
    }
}

impl fmt::Display for Claim {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} claim: {} models for component/list {} under {:?}",
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
    pub n_clauses: usize,
    pub clauses: Vec<Clause>,
    pub components: BTreeMap<ComponentIndex, Component>,
    lists: BTreeMap<ListIndex, ModelList>,
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
            n_clauses: clauses,
            clauses: Vec::new(),
            components: BTreeMap::new(),
            lists: BTreeMap::new(),
            claims: HashMap::new(),
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

    pub fn insert_model(&mut self, list: ListIndex, model: Model) -> Result<(), IntegrityError> {
        let mlist = match self.lists.get_mut(&list) {
            Some(l) => l,
            None => return Err(IntegrityError::MissingModelList(list)),
        };
        if !vars_subset(model.iter(), &mlist.vars) {
            return Err(IntegrityError::InvalidModel(list));
        }
        if !mlist.insert(model) {
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

    pub fn has_claims(&self, comp: ComponentIndex) -> bool {
        self.claims.get(&comp).is_some()
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
        let comp_id = match self.lists.get(&claim.list) {
            Some(l) => l.component,
            None => return Err(IntegrityError::MissingModelList(claim.list)),
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
        let comp_id = match self.lists.get(&claim.component) {
            Some(l) => l.component,
            None => return Err(IntegrityError::MissingComponentDef(claim.component)),
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
        eprintln! {"model lists: {} with {} models in total", self.lists.len(), self.lists.values().fold(0, |acc, l| acc + l.len())};
        eprintln! {"claims: {}", self.claims.values().fold(0, |acc, t| acc + t.len())};
    }

    pub fn find_root_claim(&self) -> Result<&Claim, IntegrityError> {
        match self
            .components
            .values()
            .find(|c| c.vars.len() == self.n_vars && c.clauses.len() == self.n_clauses)
            .and_then(|c| self.claims.get(&c.index).unwrap().get(&BTreeSet::new()))
        {
            Some(claim) => Ok(claim),
            None => Err(IntegrityError::NoRootClaim()),
        }
    }
}
