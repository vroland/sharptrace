use num_bigint::BigUint;
use num_traits::identities::One;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::str::FromStr;

mod parse;
mod verify;

pub use parse::{BodyParser, HeaderParser, IntegrityError, ParseError};
pub use verify::{VerificationError, Verifier};

pub type Var = isize;

#[derive(Debug, Clone, Copy, Eq, Ord, Hash)]
pub struct Lit(isize);

impl Lit {
    pub fn from_dimacs(l: isize) -> Self {
        Lit(l)
    }

    pub fn signum(self) -> isize {
        self.0.signum()
    }

    pub fn var(self) -> Var {
        self.0.abs()
    }

    pub fn neg(self) -> Lit {
        Lit(-self.0)
    }
}

impl PartialEq for Lit {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl PartialOrd for Lit {
    fn partial_cmp(&self, other: &Lit) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl FromStr for Lit {
    type Err = <usize as FromStr>::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        isize::from_str(s).map(|l| Self::from_dimacs(l))
    }
}

/// A clause index.
pub type ClauseIndex = usize;
/// A component index.
pub type ComponentIndex = usize;
/// A model list index.
pub type ListIndex = usize;
pub type Model = BTreeSet<Lit>;
pub type Assumption = BTreeSet<Lit>;

pub fn vars_iter<'a>(lits: impl Iterator<Item = &'a Lit> + 'a) -> impl Iterator<Item = Var> + 'a {
    lits.map(|l| l.var())
}

pub fn vars_subset<'a, 'b>(
    lits: impl Iterator<Item = &'b Lit> + 'b,
    vars: &'a BTreeSet<Var>,
) -> bool {
    !vars_iter(lits).any(|v| !vars.contains(&v))
}

pub fn vars_disjoint<'a>(vars: impl Iterator<Item = &'a Lit> + 'a, other: &BTreeSet<Var>) -> bool {
    !vars_iter(vars).any(|v| other.contains(&v))
}

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
pub struct ModelList {
    pub index: ListIndex,
    pub component: ComponentIndex,
    pub vars: BTreeSet<Var>,
    pub clauses: BTreeSet<ClauseIndex>,
    pub assm: Assumption,
    pub models: BTreeSet<Model>,
}

#[derive(Debug, Clone)]
pub struct ModelClaim {
    pub list: ListIndex,
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
        if !mlist.models.insert(model) {
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

    pub fn get_component_claims(
        &self,
        comp: ComponentIndex,
    ) -> Option<&BTreeMap<Assumption, Claim>> {
        self.claims.get(&comp)
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
        eprintln! {"model lists: {} with {} models in total", self.lists.len(), self.lists.values().fold(0, |acc, l| acc + l.models.len())};
        eprintln! {"claims: {}", self.claims.values().fold(0, |acc, t| acc + t.len())};
    }
}
