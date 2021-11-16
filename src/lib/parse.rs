use crate::*;
use num_bigint::BigUint;
use radix_trie::Trie;
use std::collections::BTreeMap;
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
    ModelList {
        index: ListIndex,
        component: ComponentIndex,
        vars: Vec<Var>,
        clauses: Vec<ClauseIndex>,
        assm: Vec<Lit>,
    },
    Model {
        list: ListIndex,
        lits: Vec<Lit>,
    },
    CompositionClaim {
        list: ListIndex,
        count: BigUint,
        assm: Vec<Lit>,
    },
    JoinList {
        child: ComponentIndex,
        component: ComponentIndex,
    },
    JoinClaim {
        component: ComponentIndex,
        count: BigUint,
        assm: Vec<Lit>,
    },
    ExtensionClaim {
        list: ListIndex,
        subcomponent: ComponentIndex,
        count: BigUint,
        assm: Vec<Lit>,
    },
}

#[derive(Error, Debug)]
pub enum IntegrityError {
    #[error("an invalid clause index was given")]
    InvalidClauseIndex(),
    #[error("the variable is invalid")]
    InvalidVariable(),
    #[error("the literal is invalid, because its variable is invalid")]
    InvalidLiteral(),
    #[error("variable / literal list contains duplicate elements (or is not sorted, which is an implementation error)")]
    ListInconsistent(),
    #[error("the component id {0} is not unique")]
    DuplicateComponentId(ComponentIndex),
    #[error("the model list id {0} is not unique")]
    DuplicateListId(ListIndex),
    #[error("a claim with the same assumption already exists for component {0}")]
    DuplicateClaim(ComponentIndex),
    #[error("component {0} this claim references is not (yet) defined")]
    MissingComponentDef(ComponentIndex),
    #[error("model list {0} this claim references is not (yet) defined")]
    MissingModelList(ListIndex),
    #[error("a claim for component {0} was given before all join lists where specified")]
    ClaimBeforeJoinList(ComponentIndex),
    #[error("the join list component {0} is redundant for component {1}")]
    RedundantJoinList(ComponentIndex, ComponentIndex),
    #[error("a misplaced problem line within the trace")]
    UnexpectedProblemLine(),
    #[error("a misplaced clause line within the trace")]
    UnexpectedClause(),
    #[error("model is not an assignment over the list variables of model list {0}")]
    InvalidModel(ListIndex),
    #[error("the model was already given for model list {0}")]
    DuplicateModel(ListIndex),
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
            .collect::<Result<Vec<_>, _>>()
            .map(|mut v| {
                v.sort_unstable_by(litcmp);
                v
            })
    }

    fn parse_line(t: &str, data: &[&str]) -> Result<TraceLine, ParseError> {
        match t {
            "p" => match data {
                [nv, nc, "0"] => Ok(TraceLine::Problem {
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
            "ml" => match &data.split(|v| v == &"0").collect::<Vec<_>>()[..] {
                [[idx, comp, v @ ..], [c @ ..], [a @ ..], []] => Ok(TraceLine::ModelList {
                    index: LineParser::parsenum(idx)?,
                    component: LineParser::parsenum(comp)?,
                    vars: LineParser::parsevec(v)?,
                    clauses: LineParser::parsevec(c)?,
                    assm: LineParser::parselits(a)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "m" => match data {
                [idx, l @ .., "0"] => Ok(TraceLine::Model {
                    list: LineParser::parsenum(idx)?,
                    lits: LineParser::parselits(l)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "a" => match data {
                [list, count, a @ .., "0"] => Ok(TraceLine::CompositionClaim {
                    list: LineParser::parsenum(list)?,
                    count: LineParser::parsenum(count)?,
                    assm: LineParser::parselits(a)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "jl" => match data {
                [list, comp, "0"] => Ok(TraceLine::JoinList {
                    child: LineParser::parsenum(list)?,
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
                [list, subcomp, count, a @ .., "0"] => Ok(TraceLine::ExtensionClaim {
                    list: LineParser::parsenum(list)?,
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

#[derive(Debug)]
pub struct BodyParser {
    trace: Trace,
    lp: LineParser,
    join_lists: BTreeMap<ComponentIndex, Vec<ComponentIndex>>,
}

// FIXME: eventually, this should work in a streaming fashion
impl BodyParser {
    fn checked_litvec(&self, vec: Vec<Lit>) -> Result<Vec<Lit>, IntegrityError> {
        if vec.iter().any(|v| !self.trace.check_lit(*v)) {
            Err(IntegrityError::InvalidVariable())
        } else {
            if !vec.windows(2).all(|w| w[0].abs() < w[1].abs()) {
                return Err(IntegrityError::ListInconsistent());
            };
            Ok(vec)
        }
    }

    fn checked_varset(&self, mut vec: Vec<Lit>) -> Result<BTreeSet<Var>, IntegrityError> {
        if vec.iter().any(|v| !self.trace.check_var(*v)) {
            Err(IntegrityError::InvalidVariable())
        } else {
            if !vec.windows(2).all(|w| w[0] < w[1]) {
                return Err(IntegrityError::ListInconsistent());
            };
            Ok(BTreeSet::from_iter(vec.drain(..)))
        }
    }

    fn checked_clauseset(
        &self,
        mut vec: Vec<ClauseIndex>,
    ) -> Result<BTreeSet<ClauseIndex>, IntegrityError> {
        if vec.iter().any(|v| !(*v > 0 && *v <= self.trace.n_clauses)) {
            eprintln! {"{:?}", vec};
            Err(IntegrityError::InvalidClauseIndex())
        } else {
            if !vec.windows(2).all(|w| w[0] < w[1]) {
                return Err(IntegrityError::ListInconsistent());
            };
            Ok(BTreeSet::from_iter(vec.drain(..)))
        }
    }

    fn parse_line(&mut self, line: TraceLine, ln: usize) -> Result<(), (usize, IntegrityError)> {
        match line {
            TraceLine::ComponentDef {
                index,
                vars,
                clauses,
            } => {
                let comp = Component {
                    index,
                    vars: self.checked_varset(vars).map_err(|e| (ln, e))?,
                    clauses: self.checked_clauseset(clauses).map_err(|e| (ln, e))?,
                };
                if self.trace.components.insert(comp.index, comp).is_some() {
                    return Err((ln, IntegrityError::DuplicateComponentId(index)));
                }
            }
            TraceLine::ModelList {
                index,
                component,
                vars,
                clauses,
                assm,
            } => self
                .trace
                .insert_list(ModelList {
                    index,
                    component,
                    vars: self.checked_varset(vars).map_err(|e| (ln, e))?,
                    clauses: self.checked_clauseset(clauses).map_err(|e| (ln, e))?,
                    assm: self.checked_litvec(assm).map_err(|e| (ln, e))?,
                    models: Trie::new(),
                })
                .map_err(|e| (ln, e))?,
            TraceLine::Model { list, lits } => {
                self.trace.insert_model(list, lits).map_err(|e| (ln, e))?
            }
            TraceLine::CompositionClaim { list, count, assm } => self
                .trace
                .insert_composition_claim(CompositionClaim {
                    list,
                    count,
                    assm: self.checked_litvec(assm).map_err(|e| (ln, e))?,
                })
                .map_err(|e| (ln, e))?,
            TraceLine::JoinList { child, component } => {
                if !self.trace.components.contains_key(&child) {
                    return Err((ln, IntegrityError::MissingComponentDef(child)));
                };
                if self.trace.get_component_claims(component).is_some() {
                    return Err((ln, IntegrityError::ClaimBeforeJoinList(component)));
                }
                let lists = match self.join_lists.get_mut(&component) {
                    Some(l) => l,
                    None => {
                        self.join_lists.insert(component, Vec::new());
                        self.join_lists.get_mut(&component).unwrap()
                    }
                };
                if lists
                    .iter()
                    .any(|l| self.trace.get_list(*l).unwrap().component == component)
                {
                    return Err((ln, IntegrityError::RedundantJoinList(child, component)));
                }
                lists.push(child);
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
                    assm: self.checked_litvec(assm).map_err(|e| (ln, e))?,
                    child_components: match self.join_lists.get(&component) {
                        Some(l) => l.clone(),
                        None => return Err((ln, IntegrityError::ClaimBeforeJoinList(component))),
                    },
                })
                .map_err(|e| (ln, e))?,
            TraceLine::ExtensionClaim {
                list,
                subcomponent,
                count,
                assm,
            } => self
                .trace
                .insert_extension_claim(ExtensionClaim {
                    list,
                    subcomponent,
                    count,
                    assm: self.checked_litvec(assm).map_err(|e| (ln, e))?,
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
            problem.n_clauses + 1,
            Clause {
                index: 0,
                lits: vec![],
            },
        );

        let mut clauses_read = 0;

        // read clauses
        while clauses_read < problem.n_clauses {
            match self.lp.next() {
                Some((ln, Ok(TraceLine::Clause { index, lits }))) => {
                    if index < 1 || index > problem.n_clauses || problem.clauses[index].index != 0 {
                        return Err((ln, IntegrityError::InvalidClauseIndex().into()));
                    }
                    if lits.iter().any(|l| !problem.check_lit(*l)) {
                        return Err((ln, IntegrityError::InvalidLiteral().into()));
                    }
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
            join_lists: BTreeMap::new(),
        })
    }
}
