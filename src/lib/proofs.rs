use crate::utils::restrict_clause;
use crate::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum BcpResult {
    Success,
    Conflict,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum LitAssignment {
    Unknown,
    Pos,
    Neg,
}

impl LitAssignment {
    pub fn from_lit(lit: Lit) -> LitAssignment {
        if lit.as_int() == 0 {
            LitAssignment::Unknown
        } else if lit.as_int() > 0 {
            LitAssignment::Pos
        } else {
            LitAssignment::Neg
        }
    }
}

/// Exhaustiveness proof data structures
#[derive(Debug, Clone)]
pub struct ProofBody {
    pub index: ProofIndex,
    pub component: ComponentIndex,
    steps: Vec<Vec<Lit>>,
}

const CLAUSE_SEPARATOR: Lit = Lit::from_dimacs(0);

impl ProofBody {
    pub fn new(index: ProofIndex, component: ComponentIndex) -> Self {
        ProofBody {
            component,
            index,
            steps: vec![],
        }
    }

    pub fn add_step(&mut self, step: Vec<Lit>) {
        self.steps.push(step);
    }

    pub fn finalize(
        mut self,
        pvars: &[Var],
        trace: &Trace,
    ) -> Result<ExhaustivenessProof, IntegrityError> {
        let comp = match trace.get_component(&self.component) {
            Some(c) => c,
            None => return Err(IntegrityError::MissingComponentDef(self.component)),
        };
        let mut formula: Vec<Lit> = vec![];
        let mut clause_offsets = vec![];

        // restricted component clauses
        for cl in &comp.clauses {
            let lits = &trace.clauses[*cl as usize].lits;
            let restricted = restrict_clause(lits.iter(), &comp.vars);
            clause_offsets.push(formula.len());
            formula.extend(restricted);
            formula.push(CLAUSE_SEPARATOR);
        }

        let claims = trace.find_claims(comp.index, Vec::from(pvars)).unwrap();

        // inverse assumption clauses
        for claim in claims {
            let negated = negate_model(claim.assumption().iter().copied());
            clause_offsets.push(formula.len());
            formula.extend(negated);
            formula.push(CLAUSE_SEPARATOR);
        }

        // add final empty clause step if necessary
        if self.steps.last().map(|s| s.len() != 0).unwrap_or(true) {
            self.steps.push(vec![]);
        }

        let num_vars = formula.iter().map(|l| l.var()).max().unwrap() as usize;
        Ok(ExhaustivenessProof {
            index: self.index,
            component: self.component,
            steps: self.steps,
            pvars: Vec::from(pvars),
            formula,
            clause_offsets,
            num_vars,
        })
    }
}

/// Exhaustiveness proof data structures
#[derive(Debug, Clone)]
pub struct ExhaustivenessProof {
    pub index: ProofIndex,
    pub component: ComponentIndex,

    /// the proof formula as packed clauses
    /// without the proof assumption
    formula: Vec<Lit>,
    clause_offsets: Vec<usize>,

    /// The proof steps.
    steps: Vec<Vec<Lit>>,

    num_vars: usize,

    /// The prefix variables.
    pvars: Vec<Var>,
}

fn negate_model<'a>(m: impl Iterator<Item = Lit> + 'a) -> impl Iterator<Item = Lit> + 'a {
    m.map(|l| -l)
}

struct RUPContext {
    formula: Vec<Lit>,
    assignment: Vec<LitAssignment>,
    clause_offsets: Vec<usize>,
}

impl RUPContext {
    fn is_solved(&self, l: Lit) -> bool {
        return self.assignment[l.var() as usize] == LitAssignment::from_lit(l);
    }

    fn is_unassigned(&self, l: Lit) -> bool {
        return self.assignment[l.var() as usize] == LitAssignment::Unknown;
    }

    fn assign(&mut self, l: Lit) {
        self.assignment[l.var() as usize] = LitAssignment::from_lit(l);
    }
}

impl ExhaustivenessProof {
    pub fn get_previx_vars(&self) -> &[Var] {
        &self.pvars
    }

    fn unit_propagate(context: &mut RUPContext) -> BcpResult {
        // the empty formula is always successful
        if context.formula.is_empty() {
            return BcpResult::Success;
        }

        let mut new_unit_discovered = true;
        while new_unit_discovered {
            new_unit_discovered = false;

            // search for clauses to propagate
            'clauseloop: for offs in &context.clause_offsets {
                let clause = &context.formula[*offs..];
                let clauseiter = clause
                    .iter()
                    .copied()
                    .take_while(|l| *l != CLAUSE_SEPARATOR);

                let mut newunit = None;
                for (i, l) in clauseiter.enumerate() {
                    if context.is_solved(l) {
                        // bring solved literal to the front
                        context.formula.swap(*offs, offs + i);
                        continue 'clauseloop;
                    }

                    if context.is_unassigned(l) {
                        // first unassigned lit we encounter
                        if newunit.is_none() {
                            newunit = Some(l);
                        // there is another unassigned lit
                        } else {
                            continue 'clauseloop;
                        }
                    }
                }

                // we found an unsatisfiable clause
                match newunit {
                    None => return BcpResult::Conflict,
                    Some(l) => {
                        // is equivalent to context.assign(l),
                        // mut makes borrowchk happy;
                        context.assignment[l.var() as usize] = LitAssignment::from_lit(l);
                        new_unit_discovered = true
                    }
                }
            }
        }
        return BcpResult::Success;
    }

    fn is_rup_inference(assm: &[Lit], step: &[Lit], context: &mut RUPContext) -> bool {
        context.assignment.fill(LitAssignment::Unknown);

        // fill assumptions into the assignment
        for l in assm
            .iter()
            .copied()
            .chain(negate_model(step.iter().copied()))
        {
            context.assign(l);
        }

        Self::unit_propagate(context) == BcpResult::Conflict
    }

    pub fn is_exhaustive_for(&self, assm: &[Lit]) -> bool {
        let mut context = RUPContext {
            formula: self.formula.clone(),
            clause_offsets: self.clause_offsets.clone(),
            assignment: vec![LitAssignment::Unknown; self.num_vars as usize + 1],
        };

        let mut valid = true;
        let mut step_idx = 0;
        while step_idx < self.steps.len() {
            let step = self.steps[step_idx].clone();

            if !Self::is_rup_inference(&assm, &step, &mut context) {
                eprintln! {"step failed: {:?} in proof {}", step, self.index};
                valid = false;
            } else {
                context.clause_offsets.push(context.formula.len());
                context.formula.extend(step.iter());
                context.formula.push(CLAUSE_SEPARATOR);
            }
            step_idx += 1;
        }
        valid
    }

    pub fn len(&self) -> usize {
        self.steps.len()
    }
}
