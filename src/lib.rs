use radix_trie::Trie;

pub type Var = isize;
pub type Lit = isize;

/// A clause index.
pub type ClauseIndex = usize;
/// A component index.
pub type ComponentIndex = usize;
/// A model list index.
pub type ListIndex = usize;

pub struct Clause {
    index: ClauseIndex,
    lits: Vec<Lit>,
}

pub struct Component {
    index: ComponentIndex,
    vars: Vec<Var>,
    clauses: Vec<ClauseIndex>,
}

pub struct ModelList {
    index: ListIndex,
    component: ComponentIndex,
    vars: Vec<Var>,
    clauses: Vec<ClauseIndex>,
    models: Trie<Lit, ()>,
}

pub struct Trace {
    pub n_vars: usize,
    pub n_clauses: usize,
    pub clauses: Vec<Clause>,
    pub components: Vec<Component>,
    pub lists: Vec<ModelList>,
}
