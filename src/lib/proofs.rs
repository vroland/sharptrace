use crate::*;

/// Exhaustiveness proof data structures
#[derive(Debug, Clone)]
pub struct ExhaustivenessProof {
    pub index: ProofIndex,
    pub component: ComponentIndex,
    pub steps: Vec<Vec<Lit>>,
    // pairs of assumptions and prefix
    // variables this proof is claimed to be exhaustive for
    pub claimed_exhaustive_for: Vec<(Assumption, Vec<Var>)>,
}

impl ExhaustivenessProof {
    pub fn new(index: ProofIndex, component: ComponentIndex) -> Self {
        ExhaustivenessProof {
            index,
            component,
            steps: vec![],
            claimed_exhaustive_for: vec![],
        }
    }

    pub fn len(&self) -> usize {
        self.steps.len()
    }

    pub fn add_step(&mut self, step: Vec<Lit>) {
        self.steps.push(step);
    }
}
