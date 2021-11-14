use num_bigint::BigUint;
use sharptrace_checker::*;
use std::fs::File;
use std::io;
use std::io::{BufRead, BufReader, Lines};
use std::iter::{Enumerate, Iterator};
use std::path::PathBuf;
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
        component: ComponentIndex,
        list: ListIndex,
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
}

pub struct LineParser {
    reader: Enumerate<Lines<BufReader<File>>>,
}

impl LineParser {
    pub fn from_file(path: &PathBuf) -> io::Result<Self> {
        Ok(LineParser {
            reader: BufReader::new(File::open(path)?).lines().enumerate(),
        })
    }

    fn parsenum<T: FromStr>(val: &str) -> Result<T, ParseError> {
        val.parse::<T>().map_err(|_e| ParseError::ConversionError())
    }

    fn parsevec<T: FromStr>(val: &[&str]) -> Result<Vec<T>, ParseError> {
        val.iter()
            .map(|i| LineParser::parsenum(*i))
            .collect::<Result<Vec<_>, _>>()
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
                    lits: LineParser::parsevec(l)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "d" => match &data.split(|v| v == &"0").map(|s| s).collect::<Vec<_>>()[..] {
                [[idx, v @ ..], [c @ ..], []] => Ok(TraceLine::ComponentDef {
                    index: LineParser::parsenum(idx)?,
                    vars: LineParser::parsevec(v)?,
                    clauses: LineParser::parsevec(c)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "ml" => match &data.split(|v| v == &"0").map(|s| s).collect::<Vec<_>>()[..] {
                [[idx, comp, v @ ..], [c @ ..], [a @ ..], []] => Ok(TraceLine::ModelList {
                    index: LineParser::parsenum(idx)?,
                    component: LineParser::parsenum(comp)?,
                    vars: LineParser::parsevec(v)?,
                    clauses: LineParser::parsevec(c)?,
                    assm: LineParser::parsevec(a)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "m" => match data {
                [idx, l @ .., "0"] => Ok(TraceLine::Model {
                    list: LineParser::parsenum(idx)?,
                    lits: LineParser::parsevec(l)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "a" => match data {
                [list, count, a @ .., "0"] => Ok(TraceLine::CompositionClaim {
                    list: LineParser::parsenum(list)?,
                    count: LineParser::parsenum(count)?,
                    assm: LineParser::parsevec(a)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "jl" => match data {
                [list, comp, "0"] => Ok(TraceLine::JoinList {
                    component: LineParser::parsenum(comp)?,
                    list: LineParser::parsenum(list)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "j" => match data {
                [comp, count, a @ .., "0"] => Ok(TraceLine::JoinClaim {
                    component: LineParser::parsenum(comp)?,
                    count: LineParser::parsenum(count)?,
                    assm: LineParser::parsevec(a)?,
                }),
                _ => Err(ParseError::MalformedLine()),
            },
            "e" => match data {
                [list, subcomp, count, a @ .., "0"] => Ok(TraceLine::ExtensionClaim {
                    list: LineParser::parsenum(list)?,
                    subcomponent: LineParser::parsenum(subcomp)?,
                    count: LineParser::parsenum(count)?,
                    assm: LineParser::parsevec(a)?,
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
            Some((ln, Err(e))) => return Some((ln + 1, Err(ParseError::IOError(e)))),
            None => return None,
        }
    }
}
