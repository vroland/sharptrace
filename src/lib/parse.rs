use crate::proofs::ExhaustivenessProof;
use crate::*;
use num_bigint::BigUint;
use std::collections::HashMap;
use std::fs::File;
use std::io;
use std::io::{BufRead, BufReader, Lines};
use std::iter::{Enumerate, Iterator};
use std::path::Path;
use std::str::FromStr;
use thiserror::Error;

#[derive(Debug, Clone)]
pub enum TraceLine {
    Problem {
        nvars: usize,
        nclauses: usize,
    },
    Clause {
        index: ClauseIndex,
        lits: Vec<Lit>,
    },
    ComponentDef {
        index: ComponentIndex,
        vars: Vec<Var>,
        clauses: Vec<ClauseIndex>,
    },
    ExhaustivenessDef {
        index: ProofIndex,
        component: ComponentIndex,
    },
    ExhaustivenessStep {
        proof: ProofIndex,
        lits: Vec<Lit>,
    },
    ExhaustivenessStatement {
        proof: ProofIndex,
        vars: Vec<Var>,
        assm: Vec<Lit>,
    },
    ModelClaim {
        component: ComponentIndex,
        model: Vec<Lit>,
    },
    CompositionClaim {
        proof: ProofIndex,
        count: BigUint,
        assm: Vec<Lit>,
    },
    JoinChild {
        child: ComponentIndex,
        component: ComponentIndex,
    },
    JoinClaim {
        component: ComponentIndex,
        count: BigUint,
        assm: Vec<Lit>,
    },
    ExtensionClaim {
        component: ComponentIndex,
        subcomponent: ComponentIndex,
        count: BigUint,
        assm: Vec<Lit>,
    },
}

#[derive(Error, Debug)]
pub enum IntegrityError {
    #[error("the clause with index {0} is not defined")]
    InvalidClauseIndex(ClauseIndex),
    #[error("the variable is invalid")]
    InvalidVariable(),
    #[error("the literal is invalid, because its variable is invalid")]
    InvalidLiteral(),
    #[error("variable / literal list contains duplicate elements (or is not sorted, which is an implementation error)")]
    ListInconsistent(),
    #[error("the component id {0} is not unique")]
    DuplicateComponentId(ComponentIndex),
    #[error("proof id {0} is not unique")]
    DuplicateProofId(ProofIndex),
    #[error("a claim with the same assumption already exists for component {0}")]
    DuplicateClaim(ComponentIndex),
    #[error("component {0} this claim references is not (yet) defined")]
    MissingComponentDef(ComponentIndex),
    #[error("the proof {0} this claim references is not (yet) defined")]
    MissingExhaustivenessProof(ProofIndex),
    #[error("a claim for component {0} was given before all join children where specified")]
    ClaimBeforeJoinChild(ComponentIndex),
    #[error("the join child {0} is redundant for component {1}")]
    RedundantJoinChild(ComponentIndex, ComponentIndex),
    #[error("a misplaced problem line within the trace")]
    UnexpectedProblemLine(),
    #[error("a misplaced clause line within the trace")]
    UnexpectedClause(),
    #[error("no root claim was specified")]
    NoRootClaim(),
}

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("i/o error")]
    IOError(#[from] io::Error),
    #[error("could not parse this line as integer numbers")]
    IntParseFailed(<isize as FromStr>::Err),
    #[error("integer type conversion error")]
    ConversionError(),
    #[error("the proof line is malformed, e.g. is not 0-terminated.")]
    MalformedLine(),
    #[error("unknown line type {0}.")]
    UnknownLineType(String),
    #[error("the trace must start with a problem line")]
    InvalidFirstLine(),
    #[error("a trace line was given before all clauses where defined")]
    ClausesNotFinished(),
    #[error("the trace header is incomplete")]
    IncompleteTraceHeader(),
    #[error("a data integrity error")]
    IntegrityError(#[from] IntegrityError),
}

#[derive(Debug)]
pub struct LineParser {
    reader: Enumerate<Lines<BufReader<File>>>,
}

impl LineParser {
    pub fn from_file(path: &Path) -> io::Result<Self> {
        Ok(LineParser {
            reader: BufReader::new(File::open(path)?).lines().enumerate(),
        })
    }

    fn parsenum<T: FromStr>(val: &str) -> Result<T, ParseError> {
        val.parse::<T>().map_err(|_e| ParseError::ConversionError())
    }

    fn parsevec<T: FromStr + Ord>(val: &[&str]) -> Result<Vec<T>, ParseError> {
        val.iter()
            .map(|i| LineParser::parsenum(*i))
            .collect::<Result<Vec<_>, _>>()
            .map(|mut v| {
                v.sort_unstable();
                v
            })
    }

    fn parselits(val: &[&str]) -> Result<Vec<Lit>, ParseError> {
        val.iter()
            .map(|i| LineParser::parsenum(*i))
            .collect::<Result<Vec<Lit>, _>>()
            .map(|mut v| {
                v.sort_unstable_by(|a, b| a.var().partial_cmp(&b.var()).unwrap());
                v
            })
    }

    fn parse_line(t: &str, data: &[&str]) -> Result<TraceLine, ParseError> {
        match t {
            "p" => match data {
                ["st", nv, nc, "0"] => Ok(TraceLine::Problem {
                    nvars: LineParser::parsenum(nv)?,
                    nclauses: LineParser::parsenum(nc)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "f" => match data {
                [idx, l @ .., "0"] => Ok(TraceLine::Clause {
                    index: LineParser::parsenum(idx)?,
                    lits: LineParser::parselits(l)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "d" => match &data.split(|v| v == &"0").collect::<Vec<_>>()[..] {
                [[idx, v @ ..], [c @ ..], []] => Ok(TraceLine::ComponentDef {
                    index: LineParser::parsenum(idx)?,
                    vars: LineParser::parsevec(v)?,
                    clauses: LineParser::parsevec(c)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "xp" => match data {
                [idx, comp, "0"] => Ok(TraceLine::ExhaustivenessDef {
                    index: LineParser::parsenum(idx)?,
                    component: LineParser::parsenum(comp)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "xf" => match &data.split(|v| v == &"0").collect::<Vec<_>>()[..] {
                [[idx, v @ ..], [a @ ..], []] => Ok(TraceLine::ExhaustivenessStatement {
                    proof: LineParser::parsenum(idx)?,
                    vars: LineParser::parsevec(v)?,
                    assm: LineParser::parselits(a)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "xs" => match data {
                [idx, l @ .., "0"] => Ok(TraceLine::ExhaustivenessStep {
                    proof: LineParser::parsenum(idx)?,
                    lits: LineParser::parselits(l)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "m" => match data {
                [comp, "1", a @ .., "0"] => Ok(TraceLine::ModelClaim {
                    component: LineParser::parsenum(comp)?,
                    model: LineParser::parselits(a)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "a" => match data {
                [proof, count, a @ .., "0"] => Ok(TraceLine::CompositionClaim {
                    proof: LineParser::parsenum(proof)?,
                    count: LineParser::parsenum(count)?,
                    assm: LineParser::parselits(a)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "jc" => match data {
                [child, comp, "0"] => Ok(TraceLine::JoinChild {
                    child: LineParser::parsenum(child)?,
                    component: LineParser::parsenum(comp)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "j" => match data {
                [comp, count, a @ .., "0"] => Ok(TraceLine::JoinClaim {
                    component: LineParser::parsenum(comp)?,
                    count: LineParser::parsenum(count)?,
                    assm: LineParser::parselits(a)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "e" => match data {
                [comp, subcomp, count, a @ .., "0"] => Ok(TraceLine::ExtensionClaim {
                    component: LineParser::parsenum(comp)?,
                    subcomponent: LineParser::parsenum(subcomp)?,
                    count: LineParser::parsenum(count)?,
                    assm: LineParser::parselits(a)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            _ => Err(ParseError::UnknownLineType(t.into())),
        }
    }
}

impl Iterator for LineParser {
    type Item = (usize, Result<TraceLine, ParseError>);

    fn next(&mut self) -> Option<Self::Item> {
        match self.reader.next() {
            Some((ln, Ok(data))) => {
                let mut line = data.trim().split_whitespace();
                match line.next() {
                    // empty line
                    None => self.next(),
                    // comment line
                    Some("c") => self.next(),
                    Some(t) => {
                        let data = line.collect::<Vec<_>>();
                        Some((ln + 1, LineParser::parse_line(t, &data)))
                    }
                }
            }
            Some((ln, Err(e))) => Some((ln + 1, Err(ParseError::IOError(e)))),
            None => None,
        }
    }
}

fn checked_litset(trace: &Trace, vec: Vec<Lit>) -> Result<Vec<Lit>, IntegrityError> {
    if vec.iter().any(|v| !trace.check_lit(*v)) {
        return Err(IntegrityError::InvalidVariable());
    }

    if !vec.windows(2).all(|w| w[0].var() <= w[1].var()) {
        return Err(IntegrityError::ListInconsistent());
    };
    Ok(vec)
}

fn checked_varset(trace: &Trace, mut vec: Vec<Var>) -> Result<Vec<Var>, IntegrityError> {
    if vec.iter().any(|v| !trace.check_var(*v)) {
        return Err(IntegrityError::InvalidVariable());
    }

    if !vec.windows(2).all(|w| w[0] <= w[1]) {
        return Err(IntegrityError::ListInconsistent());
    };

    Ok(vec)
}

fn checked_clauseset(
    trace: &Trace,
    mut vec: Vec<ClauseIndex>,
) -> Result<Vec<ClauseIndex>, IntegrityError> {
    let index_invalid = |c: &ClauseIndex| -> bool { !(*c > 0 && *c <= trace.clauses.len()) };
    if vec.iter().any(index_invalid) {
        Err(IntegrityError::InvalidClauseIndex(
            vec.iter().copied().find(index_invalid).unwrap(),
        ))
    } else {
        if !vec.windows(2).all(|w| w[0] <= w[1]) {
            return Err(IntegrityError::ListInconsistent());
        };
        Ok(vec)
    }
}

#[derive(Debug)]
pub struct BodyParser {
    trace: Trace,
    lp: LineParser,
    join_children: HashMap<ComponentIndex, Vec<ComponentIndex>>,
}

// FIXME: eventually, this should work in a streaming fashion
impl BodyParser {
    fn parse_line(&mut self, line: TraceLine, ln: usize) -> Result<(), (usize, IntegrityError)> {
        match line {
            TraceLine::ComponentDef {
                index,
                vars,
                clauses,
            } => {
                let comp = Component {
                    index,
                    vars: checked_varset(&self.trace, vars).map_err(|e| (ln, e))?,
                    clauses: checked_clauseset(&self.trace, clauses).map_err(|e| (ln, e))?,
                };
                if self.trace.components.insert(comp.index, comp).is_some() {
                    return Err((ln, IntegrityError::DuplicateComponentId(index)));
                }
            }
            TraceLine::ExhaustivenessDef { index, component } => self
                .trace
                .add_proof(ExhaustivenessProof::new(index, component))
                .map_err(|e| (ln, e))?,
            TraceLine::ExhaustivenessStep { proof, lits } => self
                .trace
                .add_proof_step(proof, lits)
                .map_err(|e| (ln, e))?,
            TraceLine::ExhaustivenessStatement { proof, assm, vars } => {
                let assm = checked_litset(&self.trace, assm).map_err(|e| (ln, e))?;
                let vars = checked_varset(&self.trace, vars).map_err(|e| (ln, e))?;
                self.trace
                    .add_exhaustiveness_for(proof, assm, vars)
                    .map_err(|e| (ln, e))?
            }
            TraceLine::ModelClaim { component, model } => self
                .trace
                .insert_model_claim(ModelClaim {
                    component,
                    assm: checked_litset(&self.trace, model).map_err(|e| (ln, e))?,
                })
                .map_err(|e| (ln, e))?,
            TraceLine::CompositionClaim { proof, count, assm } => self
                .trace
                .insert_composition_claim(CompositionClaim {
                    proof,
                    count,
                    assm: checked_litset(&self.trace, assm).map_err(|e| (ln, e))?,
                })
                .map_err(|e| (ln, e))?,
            TraceLine::JoinChild { child, component } => {
                if !self.trace.components.contains_key(&child) {
                    return Err((ln, IntegrityError::MissingComponentDef(child)));
                };
                if !self.trace.components.contains_key(&component) {
                    return Err((ln, IntegrityError::MissingComponentDef(component)));
                };
                if self.trace.has_join_claims(component) {
                    return Err((ln, IntegrityError::ClaimBeforeJoinChild(component)));
                }
                let children = match self.join_children.get_mut(&component) {
                    Some(l) => l,
                    None => {
                        self.join_children.insert(component, Vec::new());
                        self.join_children.get_mut(&component).unwrap()
                    }
                };
                children.push(child);
            }
            TraceLine::JoinClaim {
                component,
                count,
                assm,
            } => self
                .trace
                .insert_join_claim(JoinClaim {
                    component,
                    count,
                    assm: checked_litset(&self.trace, assm).map_err(|e| (ln, e))?,
                    child_components: match self.join_children.remove(&component) {
                        Some(l) => l,
                        None => return Err((ln, IntegrityError::ClaimBeforeJoinChild(component))),
                    },
                })
                .map_err(|e| (ln, e))?,
            TraceLine::ExtensionClaim {
                component,
                subcomponent,
                count,
                assm,
            } => self
                .trace
                .insert_extension_claim(ExtensionClaim {
                    component,
                    subcomponent,
                    count,
                    assm: checked_litset(&self.trace, assm).map_err(|e| (ln, e))?,
                })
                .map_err(|e| (ln, e))?,
            TraceLine::Problem { .. } => return Err((ln, IntegrityError::UnexpectedProblemLine())),
            TraceLine::Clause { .. } => return Err((ln, IntegrityError::UnexpectedClause())),
        }
        Ok(())
    }

    pub fn parse_complete(mut self) -> Result<Trace, (usize, ParseError)> {
        while let Some((ln, line)) = self.lp.next() {
            self.parse_line(line.map_err(|e| (ln, e))?, ln)
                .map_err(|(ln, e)| (ln, e.into()))?;
        }
        Ok(self.trace)
    }
}

#[derive(Debug)]
pub struct HeaderParser {
    lp: LineParser,
}

impl HeaderParser {
    pub fn from_file(path: &Path) -> io::Result<Self> {
        Ok(HeaderParser {
            lp: LineParser::from_file(path)?,
        })
    }

    pub fn read_to_body(mut self) -> Result<BodyParser, (usize, ParseError)> {
        let mut problem = match self.lp.next() {
            Some((_ln, Ok(TraceLine::Problem { nvars, nclauses }))) => Trace::new(nvars, nclauses),
            Some((ln, Ok(_))) => return Err((ln, ParseError::InvalidFirstLine())),
            Some((ln, Err(e))) => return Err((ln, e)),
            None => return Err((0, ParseError::IncompleteTraceHeader())),
        };

        // fill with dummy clause 0
        problem.clauses.resize(
            problem.n_orig_clauses + 1,
            Clause {
                index: 0,
                lits: Vec::new(),
            },
        );

        let mut clauses_read = 0;

        // read clauses
        while clauses_read < problem.n_orig_clauses {
            match self.lp.next() {
                Some((ln, Ok(TraceLine::Clause { index, mut lits }))) => {
                    if index < 1
                        || index > problem.n_orig_clauses
                        || problem.clauses[index].index != 0
                    {
                        return Err((ln, IntegrityError::InvalidClauseIndex(index).into()));
                    }
                    lits = match checked_litset(&problem, lits) {
                        Ok(l) => l,
                        Err(e) => return Err((ln, ParseError::IntegrityError(e))),
                    };
                    problem.clauses[index] = Clause { index, lits };
                    clauses_read += 1;
                }
                Some((ln, Ok(_))) => return Err((ln, ParseError::ClausesNotFinished())),
                Some((ln, Err(e))) => return Err((ln, e)),
                None => return Err((0, ParseError::IncompleteTraceHeader())),
            }
        }

        Ok(BodyParser {
            trace: problem,
            lp: self.lp,
            join_children: HashMap::new(),
        })
    }
}
