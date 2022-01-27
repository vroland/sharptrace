use crate::proofs::ProofBody;
use crate::*;
use nom::{
    branch::alt,
    bytes::streaming::{tag, take_till, take_while},
    character::streaming::{multispace0, one_of, space0, space1},
    combinator::{map, map_res, recognize},
    multi::many0,
    sequence::{pair, preceded, tuple},
    IResult,
};
use num_bigint::BigUint;
use std::collections::HashMap;
use std::io;
use std::io::BufRead;
use std::iter::Iterator;
use std::str::FromStr;
use thiserror::Error;

pub type Index = u32;

#[derive(Debug, Clone)]
pub enum TraceLine {
    Problem {
        nvars: Index,
        nclauses: Index,
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
    #[error("Integrity error: {0}")]
    IntegrityError(#[from] IntegrityError),
}

fn parse_idx(input: &str) -> IResult<&str, Index> {
    map_res(
        recognize(pair(one_of("123456789"), many0(one_of("0123456789")))),
        |out: &str| out.parse::<Index>(),
    )(input)
}

fn parse_count(input: &str) -> IResult<&str, BigUint> {
    map_res(
        recognize(pair(one_of("123456789"), many0(one_of("0123456789")))),
        |out: &str| out.parse::<BigUint>(),
    )(input)
}

fn parse_lit(input: &str) -> IResult<&str, Lit> {
    map_res(
        recognize(tuple((
            alt((tag("-"), tag(""))),
            one_of("123456789"),
            many0(one_of("0123456789")),
        ))),
        |out: &str| out.parse::<Lit>(),
    )(input)
}

fn parse_idxlist(input: &str) -> IResult<&str, Vec<Index>> {
    map(nom::multi::separated_list0(tag(" "), parse_idx), |mut l| {
        l.sort_unstable();
        l.dedup();
        l
    })(input)
}

fn parse_litlist(input: &str) -> IResult<&str, Vec<Lit>> {
    map(nom::multi::separated_list0(tag(" "), parse_lit), |mut l| {
        l.sort_unstable_by(|a, b| a.var().partial_cmp(&b.var()).unwrap());
        l
    })(input)
}

fn lineend(input: &str) -> IResult<&str, ()> {
    map(
        tuple((space0, tag("0"), nom::character::streaming::line_ending)),
        |_| (),
    )(input)
}

fn nullsep(input: &str) -> IResult<&str, ()> {
    map(tuple((space0, tag("0"), space1)), |_| ())(input)
}

fn linetag(prefix: &'static str) -> impl FnMut(&str) -> IResult<&str, ()> {
    move |i| map(pair(tag(prefix), space1), |_| ())(i)
}

pub struct LineParser<R> {
    reader: R,
    lineno: usize,
    current_line: String,
}

// alt(multispace0,
fn parse_line(input: &str) -> IResult<&str, Option<TraceLine>> {
    let problem = map(
        tuple((
            linetag("p"),
            linetag("st"),
            parse_idx,
            space1,
            parse_idx,
            lineend,
        )),
        |(_, _, nvars, _, nclauses, _)| Some(TraceLine::Problem { nvars, nclauses }),
    );

    let clause = map(
        tuple((linetag("f"), parse_idx, space1, parse_litlist, lineend)),
        |(_, index, _, lits, _)| Some(TraceLine::Clause { index, lits }),
    );

    let proof_def = map(
        tuple((linetag("xp"), parse_idx, space1, parse_idx, lineend)),
        |(_, index, _, component, _)| Some(TraceLine::ExhaustivenessDef { index, component }),
    );

    let proof_step = map(
        tuple((linetag("xs"), parse_idx, space1, parse_litlist, lineend)),
        |(_, proof, _, lits, _)| Some(TraceLine::ExhaustivenessStep { proof, lits }),
    );

    let proof_fin = map(
        tuple((
            linetag("xf"),
            parse_idx,
            space1,
            parse_idxlist,
            nullsep,
            parse_litlist,
            lineend,
        )),
        |(_, proof, _, vars, _, assm, _)| {
            Some(TraceLine::ExhaustivenessStatement { proof, vars, assm })
        },
    );

    let component = map(
        tuple((
            linetag("d"),
            parse_idx,
            space1,
            parse_idxlist,
            nullsep,
            parse_idxlist,
            lineend,
        )),
        |(_, index, _, vars, _, clauses, _)| {
            Some(TraceLine::ComponentDef {
                index,
                vars,
                clauses,
            })
        },
    );

    let model = map(
        tuple((
            linetag("m"),
            parse_idx,
            space1,
            tag("1"),
            space1,
            parse_litlist,
            lineend,
        )),
        |(_, component, _, _, _, model, _)| Some(TraceLine::ModelClaim { component, model }),
    );

    let composition = map(
        tuple((
            linetag("a"),
            parse_idx,
            space1,
            parse_count,
            space1,
            parse_litlist,
            lineend,
        )),
        |(_, proof, _, count, _, assm, _)| Some(TraceLine::CompositionClaim { proof, count, assm }),
    );

    let join = map(
        tuple((
            linetag("j"),
            parse_idx,
            space1,
            parse_count,
            space1,
            parse_litlist,
            lineend,
        )),
        |(_, component, _, count, _, assm, _)| {
            Some(TraceLine::JoinClaim {
                component,
                count,
                assm,
            })
        },
    );

    let extension = map(
        tuple((
            linetag("e"),
            parse_idx,
            space1,
            parse_idx,
            space1,
            parse_count,
            space1,
            parse_litlist,
            lineend,
        )),
        |(_, component, _, subcomponent, _, count, _, assm, _)| {
            Some(TraceLine::ExtensionClaim {
                component,
                subcomponent,
                count,
                assm,
            })
        },
    );

    let join_child = map(
        tuple((linetag("jc"), parse_idx, space1, parse_idx, lineend)),
        |(_, child, _, component, _)| Some(TraceLine::JoinChild { child, component }),
    );

    let empty = map(
        tuple((space0, nom::character::streaming::line_ending)),
        |_: (&str, &str)| None,
    );

    let comment = map(
        tuple((
            tag("c"),
            take_till(|c| c == '\n'),
            nom::character::streaming::line_ending,
        )),
        |_: (&str, &str, &str)| None,
    );

    alt((
        comment,
        proof_step,
        join_child,
        composition,
        join,
        extension,
        model,
        component,
        proof_def,
        proof_fin,
        clause,
        problem,
        empty,
    ))(input)
}

impl<R: BufRead> LineParser<R> {
    pub fn from(reader: R) -> io::Result<Self> {
        Ok(LineParser {
            reader,
            lineno: 0,
            current_line: String::new(),
        })
    }

    fn parse_line(&self, t: &str, line: &str) -> Result<TraceLine, ParseError> {
        match t {
            /*
            "p" => {
                let caps = self
                    .re_problem
                    .captures(line)
                    .ok_or(ParseError::MalformedLine())?;
                Ok(TraceLine::Problem {
                    nvars: parsenum(caps.name("nv").unwrap().as_str())?,
                    nclauses: parsenum(caps.name("nc").unwrap().as_str())?,
                })
            }
            "f" => {
                let caps = self
                    .re_clause
                    .captures(line)
                    .ok_or(ParseError::MalformedLine())?;
                Ok(TraceLine::Clause {
                    index: parsenum(caps.name("id").unwrap().as_str())?,
                    lits: parselits(caps.name("lits").unwrap().as_str())?,
                })
            }
            "xp" => match &self.current_line[..] {
                [idx, comp, "0"] => Ok(TraceLine::ExhaustivenessDef {
                    index: LineParser::parsenum(idx)?,
                    component: LineParser::parsenum(comp)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "d" => match &self.current_line[..] {
                [idx, numbers @ .., "0"] => {
                    let mut params = numbers.split(|s| *s == "0");
                    let v = match params.next() {
                        Some(v) => v,
                        _ => return Err(ParseError::MalformedLine()),
                    };
                    let c = match params.next() {
                        Some(c) => c,
                        _ => return Err(ParseError::MalformedLine()),
                    };
                    if params.next().is_some() {
                        Err(ParseError::MalformedLine())
                    } else {
                        Ok(TraceLine::ComponentDef {
                            index: LineParser::parsenum(idx)?,
                            vars: LineParser::parsevec(v)?,
                            clauses: LineParser::parsevec(c)?,
                        })
                    }
                }
                _ => Err(ParseError::MalformedLine()),
            },
            "xf" => match &self.current_line[..] {
                [idx, numbers @ .., "0"] => {
                    let mut params = numbers.split(|s| *s == "0");
                    let v = match params.next() {
                        Some(v) => v,
                        _ => return Err(ParseError::MalformedLine()),
                    };
                    let a = match params.next() {
                        Some(a) => a,
                        _ => return Err(ParseError::MalformedLine()),
                    };
                    if params.next().is_some() {
                        Err(ParseError::MalformedLine())
                    } else {
                        Ok(TraceLine::ExhaustivenessStatement {
                            proof: LineParser::parsenum(idx)?,
                            vars: LineParser::parsevec(v)?,
                            assm: LineParser::parselits(a)?,
                        })
                    }
                }
                _ => Err(ParseError::MalformedLine()),
            },
            "xs" => match &self.current_line[..] {
                [idx, l @ .., "0"] => Ok(TraceLine::ExhaustivenessStep {
                    proof: LineParser::parsenum(idx)?,
                    lits: LineParser::parselits(l)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "m" => match &self.current_line[..] {
                [comp, "1", a @ .., "0"] => Ok(TraceLine::ModelClaim {
                    component: LineParser::parsenum(comp)?,
                    model: LineParser::parselits(a)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "a" => match &self.current_line[..] {
                [proof, count, a @ .., "0"] => Ok(TraceLine::CompositionClaim {
                    proof: LineParser::parsenum(proof)?,
                    count: LineParser::parsenum(count)?,
                    assm: LineParser::parselits(a)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "jc" => match &self.current_line[..] {
                [child, comp, "0"] => Ok(TraceLine::JoinChild {
                    child: LineParser::parsenum(child)?,
                    component: LineParser::parsenum(comp)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "j" => match &self.current_line[..] {
                [comp, count, a @ .., "0"] => Ok(TraceLine::JoinClaim {
                    component: LineParser::parsenum(comp)?,
                    count: LineParser::parsenum(count)?,
                    assm: LineParser::parselits(a)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "e" => match &self.current_line[..] {
                [comp, subcomp, count, a @ .., "0"] => Ok(TraceLine::ExtensionClaim {
                    component: LineParser::parsenum(comp)?,
                    subcomponent: LineParser::parsenum(subcomp)?,
                    count: LineParser::parsenum(count)?,
                    assm: LineParser::parselits(a)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            */
            _ => Err(ParseError::UnknownLineType(t.into())),
        }
    }
}

impl<R: BufRead> Iterator for LineParser<R> {
    type Item = (usize, Result<TraceLine, ParseError>);

    fn next(&mut self) -> Option<Self::Item> {
        self.lineno += 1;
        self.current_line.clear();
        match self.reader.read_line(&mut self.current_line) {
            Err(e) => return Some((self.lineno, Err(ParseError::IOError(e)))),
            Ok(0) => return None,
            _ => (),
        }
        self.current_line.push_str("\n");
        match parse_line(self.current_line.as_str()) {
            Ok((_, Some(pl))) => Some((self.lineno, Ok(pl))),
            Ok((_, None)) => self.next(),
            Err(e) => panic! {"nom error: {:?}", e},
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

fn checked_varset(trace: &Trace, vec: Vec<Var>) -> Result<Vec<Var>, IntegrityError> {
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
    vec: Vec<ClauseIndex>,
) -> Result<Vec<ClauseIndex>, IntegrityError> {
    let index_invalid =
        |c: &ClauseIndex| -> bool { !(*c > 0 && *c <= trace.clauses.len().try_into().unwrap()) };
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

pub struct BodyParser<R> {
    trace: Trace,
    lp: LineParser<R>,
    join_children: HashMap<ComponentIndex, Vec<ComponentIndex>>,
    proof_bodies: HashMap<ProofIndex, ProofBody>,
}

// FIXME: eventually, this should work in a streaming fashion
impl<R: BufRead> BodyParser<R> {
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
                self.trace.insert_component(comp).map_err(|e| (ln, e))?
            }
            TraceLine::ExhaustivenessDef { index, component } => {
                if let Some(bdy) = self
                    .proof_bodies
                    .insert(index, ProofBody::new(index, component))
                {
                    return Err((ln, IntegrityError::DuplicateProofId(bdy.index)));
                }
            }
            TraceLine::ExhaustivenessStep { proof, lits } => {
                if let Some(bdy) = self.proof_bodies.get_mut(&proof) {
                    bdy.add_step(lits)
                } else {
                    return Err((ln, IntegrityError::MissingExhaustivenessProof(proof)));
                }
            }
            TraceLine::ExhaustivenessStatement {
                proof,
                assm: _,
                vars,
            } => {
                if let Some(bdy) = self.proof_bodies.remove(&proof) {
                    //let assm = checked_litset(&self.trace, assm).map_err(|e| (ln, e))?;
                    let vars = checked_varset(&self.trace, vars).map_err(|e| (ln, e))?;
                    let proof = bdy.finalize(&vars, &self.trace).map_err(|e| (ln, e))?;
                    self.trace
                        .add_exhaustiveness_proof(proof)
                        .map_err(|e| (ln, e))?
                } else {
                    return Err((ln, IntegrityError::MissingExhaustivenessProof(proof)));
                }
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
                if !self.trace.get_component(&child).is_some() {
                    return Err((ln, IntegrityError::MissingComponentDef(child)));
                };
                if !self.trace.get_component(&component).is_some() {
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
                    child_components: {
                        match self.join_children.get(&component) {
                            Some(l) => l.clone(),
                            None => {
                                return Err((ln, IntegrityError::ClaimBeforeJoinChild(component)))
                            }
                        }
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

pub struct HeaderParser<R> {
    lp: LineParser<R>,
}

impl<R: BufRead> HeaderParser<R> {
    pub fn from(reader: R) -> io::Result<Self> {
        Ok(HeaderParser {
            lp: LineParser::from(reader)?,
        })
    }

    pub fn read_to_body(mut self) -> Result<BodyParser<R>, (usize, ParseError)> {
        let mut problem = match self.lp.next() {
            Some((_ln, Ok(TraceLine::Problem { nvars, nclauses }))) => Trace::new(nvars, nclauses),
            Some((ln, Ok(_))) => return Err((ln, ParseError::InvalidFirstLine())),
            Some((ln, Err(e))) => return Err((ln, e)),
            None => return Err((0, ParseError::IncompleteTraceHeader())),
        };

        // fill with dummy clause 0
        problem.clauses.resize(
            (problem.n_orig_clauses + 1).try_into().unwrap(),
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
                        || problem.clauses[index as usize].index != 0
                    {
                        return Err((ln, IntegrityError::InvalidClauseIndex(index).into()));
                    }
                    lits = match checked_litset(&problem, lits) {
                        Ok(l) => l,
                        Err(e) => return Err((ln, ParseError::IntegrityError(e))),
                    };
                    problem.clauses[index as usize] = Clause { index, lits };
                    clauses_read += 1;
                }
                Some((ln, Ok(l))) => {
                    eprintln! {"too early: {:?}", l};
                    return Err((ln, ParseError::ClausesNotFinished()));
                }
                Some((ln, Err(e))) => return Err((ln, e)),
                None => return Err((0, ParseError::IncompleteTraceHeader())),
            }
        }

        Ok(BodyParser {
            trace: problem,
            lp: self.lp,
            join_children: HashMap::new(),
            proof_bodies: HashMap::new(),
        })
    }
}
