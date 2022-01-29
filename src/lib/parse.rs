use crate::proofs::ProofBody;
use crate::*;
use nom::{
    branch::alt,
    bytes::streaming::{tag, take_till, take_while, take_while1},
    character::streaming::{space0, space1},
    combinator::{complete, eof, map, map_res, opt, recognize},
    error::{ParseError, VerboseError},
    sequence::{pair, preceded, terminated, tuple},
    IResult,
};
use num_bigint::BigUint;
use std::collections::HashMap;
use std::io;
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
    End {},
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
    #[error("a join claim was given for component {0}, but it has no join children!")]
    NoJoinChildren(ComponentIndex),
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
pub enum TraceReadError<'l> {
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
    #[error("nom error: {0}")]
    NomErr(nom::Err<nom::error::VerboseError<&'l str>>),
}

fn is_nonzero_digit(c: char) -> bool {
    c != '0' && c.is_ascii_digit()
}

fn parse_idx(input: &str) -> IResult<&str, Index, VerboseError<&str>> {
    map_res(
        recognize(pair(
            take_while1(|c: char| is_nonzero_digit(c)),
            take_while(|c: char| c.is_ascii_digit()),
        )),
        |out: &str| out.parse::<Index>(),
    )(input)
}

fn parse_count(input: &str) -> IResult<&str, BigUint, VerboseError<&str>> {
    map_res(
        recognize(take_while(|c: char| c.is_ascii_digit())),
        |out: &str| out.parse::<BigUint>(),
    )(input)
}

fn parse_lit(input: &str) -> IResult<&str, Lit, VerboseError<&str>> {
    map_res(
        recognize(tuple((
            opt(tag("-")),
            take_while1(|c: char| is_nonzero_digit(c)),
            take_while(|c: char| c.is_ascii_digit()),
        ))),
        |out: &str| out.parse::<Lit>(),
    )(input)
}

fn idxlist(input: &str) -> IResult<&str, Vec<Index>, VerboseError<&str>> {
    map(nom::multi::separated_list0(tag(" "), parse_idx), |mut l| {
        l.sort_unstable();
        l.dedup();
        l
    })(input)
}

fn lits(input: &str) -> IResult<&str, Vec<Lit>, VerboseError<&str>> {
    map(nom::multi::separated_list0(tag(" "), parse_lit), |mut l| {
        l.sort_unstable_by(|a, b| a.var().partial_cmp(&b.var()).unwrap());
        l
    })(input)
}

fn lineend(input: &str) -> IResult<&str, (), VerboseError<&str>> {
    map(
        tuple((space0, tag("0"), nom::character::streaming::line_ending)),
        |_| (),
    )(input)
}

fn nullsep(input: &str) -> IResult<&str, (), VerboseError<&str>> {
    map(tuple((space0, tag("0"), space1)), |_| ())(input)
}

fn linetag(prefix: &'static str) -> impl FnMut(&str) -> IResult<&str, (), VerboseError<&str>> {
    move |i| map(pair(tag(prefix), space1), |_| ())(i)
}

// alt(multispace0,
fn parse_line(input: &str) -> IResult<&str, Option<TraceLine>, VerboseError<&str>> {
    let mut problem = map(
        tuple((linetag("st"), parse_idx, space1, parse_idx, lineend)),
        |(_, nvars, _, nclauses, _)| Some(TraceLine::Problem { nvars, nclauses }),
    );

    let mut clause = map(
        tuple((parse_idx, space1, lits, lineend)),
        |(index, _, lits, _)| Some(TraceLine::Clause { index, lits }),
    );

    let mut proof_def = map(
        tuple((parse_idx, space1, parse_idx, lineend)),
        |(index, _, component, _)| Some(TraceLine::ExhaustivenessDef { index, component }),
    );

    let mut proof_step = map(
        tuple((parse_idx, space1, lits, lineend)),
        |(proof, _, lits, _)| Some(TraceLine::ExhaustivenessStep { proof, lits }),
    );

    let mut proof_fin = map(
        tuple((parse_idx, space1, idxlist, nullsep, lits, lineend)),
        |(proof, _, vars, _, assm, _)| {
            Some(TraceLine::ExhaustivenessStatement { proof, vars, assm })
        },
    );

    let mut component = map(
        tuple((parse_idx, space1, idxlist, nullsep, idxlist, lineend)),
        |(index, _, vars, _, clauses, _)| {
            Some(TraceLine::ComponentDef {
                index,
                vars,
                clauses,
            })
        },
    );

    let mut model = map(
        tuple((parse_idx, space1, tag("1"), space1, lits, lineend)),
        |(component, _, _, _, model, _)| Some(TraceLine::ModelClaim { component, model }),
    );

    let mut composition = map(
        tuple((parse_idx, space1, parse_count, space1, lits, lineend)),
        |(proof, _, count, _, assm, _)| Some(TraceLine::CompositionClaim { proof, count, assm }),
    );

    let mut join = map(
        tuple((parse_idx, space1, parse_count, space1, lits, lineend)),
        |(component, _, count, _, assm, _)| {
            Some(TraceLine::JoinClaim {
                component,
                count,
                assm,
            })
        },
    );

    let mut extension = map(
        tuple((
            parse_idx,
            space1,
            parse_idx,
            space1,
            parse_count,
            space1,
            lits,
            lineend,
        )),
        |(component, _, subcomponent, _, count, _, assm, _)| {
            Some(TraceLine::ExtensionClaim {
                component,
                subcomponent,
                count,
                assm,
            })
        },
    );

    let mut join_child = map(
        tuple((parse_idx, space1, parse_idx, lineend)),
        |(child, _, component, _)| Some(TraceLine::JoinChild { child, component }),
    );

    let empty = map(
        tuple((space0, nom::character::streaming::line_ending)),
        |_: (&str, &str)| None,
    );

    let end = map(alt((eof, preceded(space0, eof))), |_| {
        Some(TraceLine::End {})
    });

    let mut comment = map(
        tuple((
            take_till(|c| c == '\n'),
            nom::character::streaming::line_ending,
        )),
        |_: (&str, &str)| None,
    );

    let (rest, tag) = match terminated::<&str, &str, &str, VerboseError<&str>, _, _>(
        nom::character::streaming::alpha1,
        space1,
    )(input)
    {
        Ok(r) => r,
        Err(_e) => {
            let r = alt((end, empty))(input);
            if !r.is_ok() {
                eprintln! {"{:?}", input.len()};
            }
            return r;
        }
    };

    match tag {
        "c" => comment(rest),
        "xs" => proof_step(rest),
        "xp" => proof_def(rest),
        "xf" => proof_fin(rest),
        "d" => component(rest),
        "m" => model(rest),
        "a" => composition(rest),
        "jc" => join_child(rest),
        "j" => join(rest),
        "e" => extension(rest),
        "f" => clause(rest),
        "p" => problem(rest),
        _ => {
            return Err(nom::Err::Error(nom::error::VerboseError::from_error_kind(
                input,
                nom::error::ErrorKind::Tag,
            )))
        }
    }
}

pub struct LineParser<'l> {
    input: &'l str,
}

impl<'l> LineParser<'l> {
    pub fn from(input: &'l str) -> Self {
        LineParser { input }
    }
}

impl<'l> Iterator for LineParser<'l> {
    type Item = Result<TraceLine, TraceReadError<'l>>;

    fn next(&mut self) -> Option<Self::Item> {
        let (rest, result) = match complete(parse_line)(self.input) {
            Ok(r) => r,
            Err(e) => return Some(Err(TraceReadError::NomErr(e))),
        };
        self.input = rest;
        match result {
            Some(TraceLine::End {}) => None,
            Some(l) => Some(Ok(l)),
            None => self.next(),
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

pub struct BodyParser<'l> {
    trace: Trace,
    lp: LineParser<'l>,
    join_children: HashMap<ComponentIndex, Vec<ComponentIndex>>,
    proof_bodies: HashMap<ProofIndex, ProofBody>,
}

// FIXME: eventually, this should work in a streaming fashion
impl<'l> BodyParser<'l> {
    fn parse_line(&mut self, line: TraceLine) -> Result<(), IntegrityError> {
        match line {
            TraceLine::ComponentDef {
                index,
                vars,
                clauses,
            } => {
                let comp = Component {
                    index,
                    vars: checked_varset(&self.trace, vars)?,
                    clauses: checked_clauseset(&self.trace, clauses)?,
                };
                self.trace.insert_component(comp)?;
            }
            TraceLine::ExhaustivenessDef { index, component } => {
                if let Some(bdy) = self
                    .proof_bodies
                    .insert(index, ProofBody::new(index, component))
                {
                    return Err(IntegrityError::DuplicateProofId(bdy.index));
                }
            }
            TraceLine::ExhaustivenessStep { proof, lits } => {
                if let Some(bdy) = self.proof_bodies.get_mut(&proof) {
                    bdy.add_step(lits)
                } else {
                    return Err(IntegrityError::MissingExhaustivenessProof(proof));
                }
            }
            TraceLine::ExhaustivenessStatement {
                proof,
                assm: _,
                vars,
            } => {
                if let Some(bdy) = self.proof_bodies.remove(&proof) {
                    //let assm = checked_litset(&self.trace, assm).map_err(|e| (ln, e))?;
                    let vars = checked_varset(&self.trace, vars)?;
                    let proof = bdy.finalize(&vars, &self.trace)?;
                    self.trace.add_exhaustiveness_proof(proof)?
                } else {
                    return Err(IntegrityError::MissingExhaustivenessProof(proof));
                }
            }
            TraceLine::ModelClaim { component, model } => {
                self.trace.insert_model_claim(ModelClaim {
                    component,
                    assm: checked_litset(&self.trace, model)?,
                })?
            }
            TraceLine::CompositionClaim { proof, count, assm } => {
                self.trace.insert_composition_claim(CompositionClaim {
                    proof,
                    count,
                    assm: checked_litset(&self.trace, assm)?,
                })?
            }
            TraceLine::JoinChild { child, component } => {
                if !self.trace.get_component(&child).is_some() {
                    return Err(IntegrityError::MissingComponentDef(child));
                };
                if !self.trace.get_component(&component).is_some() {
                    return Err(IntegrityError::MissingComponentDef(component));
                };
                if self.trace.has_join_claims(component) {
                    return Err(IntegrityError::ClaimBeforeJoinChild(component));
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
            } => self.trace.insert_join_claim(JoinClaim {
                component,
                count,
                assm: checked_litset(&self.trace, assm)?,
                child_components: {
                    match self.join_children.get(&component) {
                        Some(l) => l.clone(),
                        None => return Err(IntegrityError::NoJoinChildren(component)),
                    }
                },
            })?,
            TraceLine::ExtensionClaim {
                component,
                subcomponent,
                count,
                assm,
            } => self.trace.insert_extension_claim(ExtensionClaim {
                component,
                subcomponent,
                count,
                assm: checked_litset(&self.trace, assm)?,
            })?,
            TraceLine::Problem { .. } => return Err(IntegrityError::UnexpectedProblemLine()),
            TraceLine::Clause { .. } => return Err(IntegrityError::UnexpectedClause()),
            TraceLine::End {} => unreachable!(),
        }
        Ok(())
    }

    pub fn parse_complete(mut self) -> Result<Trace, TraceReadError<'l>> {
        while let Some(line) = self.lp.next() {
            self.parse_line(line?)
                .map_err(|e| TraceReadError::IntegrityError(e))?;
        }
        Ok(self.trace)
    }
}

pub struct HeaderParser<'l> {
    lp: LineParser<'l>,
}

impl<'l> HeaderParser<'l> {
    pub fn from(input: &'l str) -> Self {
        HeaderParser {
            lp: LineParser::from(input),
        }
    }

    pub fn read_to_body(mut self) -> Result<BodyParser<'l>, TraceReadError<'l>> {
        let mut problem = match self.lp.next() {
            Some(Ok(TraceLine::Problem { nvars, nclauses })) => Trace::new(nvars, nclauses),
            Some(Ok(_)) => return Err(TraceReadError::InvalidFirstLine()),
            Some(Err(e)) => return Err(e),
            None => return Err(TraceReadError::IncompleteTraceHeader()),
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
                Some(Ok(TraceLine::Clause { index, mut lits })) => {
                    if index < 1
                        || index > problem.n_orig_clauses
                        || problem.clauses[index as usize].index != 0
                    {
                        return Err(IntegrityError::InvalidClauseIndex(index).into());
                    }
                    lits = checked_litset(&problem, lits)?;
                    problem.clauses[index as usize] = Clause { index, lits };
                    clauses_read += 1;
                }
                Some(Ok(_)) => {
                    return Err(TraceReadError::ClausesNotFinished());
                }
                Some(Err(e)) => return Err(e),
                None => return Err(TraceReadError::IncompleteTraceHeader()),
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
