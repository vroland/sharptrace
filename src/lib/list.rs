use crate::utils::vars_iter;
use crate::*;

/// Model list data stricture allowing for efficient model search.
#[derive(Debug, Clone)]
pub struct ModelList {
    pub index: ListIndex,
    pub component: ComponentIndex,
    pub vars: BTreeSet<Var>,
    pub clauses: BTreeSet<ClauseIndex>,
    pub assm: Assumption,
    models: BTreeSet<u64>,
}

impl ModelList {
    pub fn new(
        index: ListIndex,
        component: ComponentIndex,
        vars: BTreeSet<Var>,
        clauses: BTreeSet<ClauseIndex>,
        assm: Assumption,
    ) -> Self {
        ModelList {
            index,
            component,
            vars,
            clauses,
            assm,
            models: BTreeSet::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.models.len()
    }

    fn binary_model(&self, assm: &Assumption) -> u64 {
        let mut key = 0;
        for (i, v) in self.vars.iter().rev().enumerate() {
            if assm.contains(&Lit::from_dimacs(*v)) {
                key |= 1 << i;
            }
        }
        key
    }

    fn bin_to_model(&self, bin: u64) -> Model {
        self.vars
            .iter()
            .rev()
            .enumerate()
            .map(|(i, v)| {
                if bin & (1 << i) > 0 {
                    Lit::from_dimacs(*v)
                } else {
                    Lit::from_dimacs(-v)
                }
            })
            .collect()
    }

    fn generate_ranges(
        combinations: &[u64],
        path: u64,
        result: &mut Vec<std::ops::RangeInclusive<u64>>,
    ) {
        if combinations.len() > 1 {
            Self::generate_ranges(&combinations[1..], path, result);
            Self::generate_ranges(&combinations[1..], path | combinations[0], result);
        } else {
            result.push(path..=(path | combinations[0]));
        }
    }

    pub fn all_models(&self) -> impl Iterator<Item = Model> + '_ {
        self.models.iter().map(|bm| self.bin_to_model(*bm))
    }

    pub fn find_models(&self, assm: &Assumption) -> impl Iterator<Item = Model> + '_ {
        let base_index = self.binary_model(assm);
        let mut assm_mask: u64 = 0;
        for (i, v) in self.vars.iter().rev().enumerate() {
            if assm.iter().any(|l| l.var() == *v) {
                assm_mask |= 1 << i;
            }
        }

        let mut elements: Vec<_> = self
            .vars
            .iter()
            .rev()
            .enumerate()
            .filter(|(_i, v)| !vars_iter(assm.iter()).any(|av| av == **v))
            .map(|(i, _)| 1 << i)
            .collect();

        elements.reverse();

        let mut ranges = vec![];
        Self::generate_ranges(&elements[..], base_index, &mut ranges);

        ranges
            .into_iter()
            .map(|r| self.models.range(r))
            .flatten()
            .filter(move |bm| *bm & assm_mask == base_index)
            .map(|bm| self.bin_to_model(*bm))
    }

    pub fn insert(&mut self, model: Model) -> bool {
        assert! {model.len() == self.vars.len()};
        self.models.insert(self.binary_model(&model))
    }
}
