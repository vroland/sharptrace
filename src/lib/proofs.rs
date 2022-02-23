use crate::utils::restrict_sorted_clause;
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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct ClauseInfo {
    pub offset: usize,
    pub len: usize,
}

impl LitAssignment {
    pub fn from_lit(lit: Lit) -> LitAssignment {
        match lit.as_int().cmp(&0) {
            Ordering::Equal => LitAssignment::Unknown,
            Ordering::Greater => LitAssignment::Pos,
            Ordering::Less => LitAssignment::Neg,
        }
    }
}

/// Exhaustiveness proof data structures
#[derive(Debug, Clone)]
pub struct ProofBody {
    pub index: ProofIndex,
    steps: Vec<Vec<Lit>>,
}

const CLAUSE_SEPARATOR: Lit = Lit::from_dimacs(0);

impl ProofBody {
    pub fn new(index: ProofIndex) -> Self {
        ProofBody {
            index,
            steps: vec![],
        }
    }

    pub fn add_step(&mut self, step: Vec<Lit>) {
        self.steps.push(step);
    }

    fn greedy_resolve(formula: &mut Vec<Lit>, offsets: &mut Vec<ClauseInfo>) {
        loop {
            let n_clauses = offsets.len();
            if n_clauses < 2 {
                break;
            }
            let current_info = *offsets.last().unwrap();
            // stop here to avoid special-casing unit clauses or conflicts
            if current_info.len <= 2 {
                break;
            }

            let last_info = &mut offsets[n_clauses - 2];
            let cur_prefix =
                &formula[current_info.offset..(current_info.offset + current_info.len - 1)];
            let cur_lit = formula[current_info.offset + current_info.len - 1];
            let last_prefix = &formula[last_info.offset..(last_info.offset + last_info.len - 1)];
            let last_lit = formula[last_info.offset + last_info.len - 1];

            // resolve clauses
            if cur_prefix == last_prefix && cur_lit == -last_lit {
                last_info.len -= 1;
                formula.truncate(last_info.offset + last_info.len + 1);
                formula.push(CLAUSE_SEPARATOR);
                offsets.pop();
            } else {
                break;
            }
        }
    }

    pub fn finalize(
        mut self,
        pvars: &[Var],
        trace: &Trace,
        assm: Assumption,
        component: ComponentIndex,
    ) -> Result<ExhaustivenessProof, IntegrityError> {
        let comp = match trace.get_component(&component) {
            Some(c) => c,
            None => return Err(IntegrityError::MissingComponentDef(component)),
        };
        let mut formula: Vec<Lit> = Vec::with_capacity(comp.clauses.len() * 2);
        let mut clause_offsets = Vec::with_capacity(comp.clauses.len());

        // add assumption to formula
        for l in &assm {
            clause_offsets.push(ClauseInfo {
                offset: formula.len(),
                len: 1,
            });
            formula.push(*l);
            formula.push(CLAUSE_SEPARATOR);
        }

        // restricted component clauses
        for cl in &comp.clauses {
            let lits = &trace.clauses[*cl as usize].lits;
            let restricted = restrict_sorted_clause(lits.iter(), &comp.vars);
            let offset = formula.len();
            formula.extend(restricted);
            clause_offsets.push(ClauseInfo {
                offset,
                len: formula.len() - offset,
            });
            formula.push(CLAUSE_SEPARATOR);
        }

        // find matching claims
        let claims = trace.find_claims(comp.index, pvars, &assm).unwrap();

        // inverse assumption clauses
        for claim in claims {
            let negated = negate_model(claim.assumption().iter().copied());
            clause_offsets.push(ClauseInfo {
                offset: formula.len(),
                len: claim.assumption().len(),
            });
            formula.extend(negated);
            formula.push(CLAUSE_SEPARATOR);
            Self::greedy_resolve(&mut formula, &mut clause_offsets);
        }

        // add final empty clause step if necessary
        if self.steps.last().map(|s| !s.is_empty()).unwrap_or(true) {
            self.steps.push(vec![]);
        }

        formula.shrink_to_fit();

        let num_vars = formula.iter().map(|l| l.var()).max().unwrap_or(0) as usize;
        Ok(ExhaustivenessProof {
            index: self.index,
            component,
            steps: self.steps,
            pvars: Vec::from(pvars),
            formula,
            assm,
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
    pub assm: Assumption,

    /// the proof formula as packed clauses
    /// without the proof assumption
    formula: Vec<Lit>,
    clause_offsets: Vec<ClauseInfo>,

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
    clause_offsets: Vec<ClauseInfo>,
    assigned_units: usize,
}

impl RUPContext {
    #[inline]
    fn is_solved(&self, l: Lit) -> bool {
        self.assignment[l.var() as usize] == LitAssignment::from_lit(l)
    }

    #[inline]
    fn is_unassigned(&self, l: Lit) -> bool {
        self.assignment[l.var() as usize] == LitAssignment::Unknown
    }

    #[inline]
    fn assign(&mut self, l: Lit) {
        if self.is_unassigned(l) {
            self.assigned_units += 1;
        }
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
            'clauseloop: for info in &context.clause_offsets {
                if context.assigned_units + 1 < info.len {
                    continue;
                }

                let clause = &context.formula[info.offset..(info.offset + info.len)];

                let mut newunit = None;
                for (i, l) in clause.iter().enumerate() {
                    if context.is_solved(*l) {
                        // bring solved literal to the front
                        if i > 0 {
                            context.formula.swap(info.offset, info.offset + i);
                        }
                        continue 'clauseloop;
                    }

                    if context.is_unassigned(*l) {
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
                        if context.is_unassigned(*l) {
                            context.assignment[l.var() as usize] = LitAssignment::from_lit(*l);
                            context.assigned_units += 1;
                        }
                        new_unit_discovered = true
                    }
                }
            }
        }
        BcpResult::Success
    }

    fn is_rup_inference(&self, step: &[Lit], context: &mut RUPContext) -> bool {
        context.assignment.fill(LitAssignment::Unknown);
        context.assigned_units = 0;

        // fill assumptions into the assignment
        for l in &self.assm {
            context.assign(*l);
        }
        for l in negate_model(step.iter().copied()) {
            context.assign(l);
        }

        Self::unit_propagate(context) == BcpResult::Conflict
    }

    pub fn is_exhaustive(&self) -> bool {
        let mut context = RUPContext {
            formula: self.formula.clone(),
            clause_offsets: self.clause_offsets.clone(),
            assignment: vec![LitAssignment::Unknown; self.num_vars as usize + 1],
            assigned_units: 0,
        };

        let mut valid = true;
        let mut step_idx = 0;
        while step_idx < self.steps.len() {
            let step = self.steps[step_idx].clone();

            if !self.is_rup_inference(&step, &mut context) {
                eprintln! {"step failed: {:?} in proof {}", step, self.index};
                valid = false;
            } else {
                context.clause_offsets.push(ClauseInfo {
                    offset: context.formula.len(),
                    len: step.len(),
                });
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
