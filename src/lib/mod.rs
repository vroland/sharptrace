use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::fmt;
use std::str::FromStr;

mod list;
mod parse;
mod trace;
mod utils;
mod verify;

pub use parse::{BodyParser, HeaderParser, IntegrityError, ParseError};
pub use trace::*;
pub use verify::{VerificationError, Verifier};

pub type Var = isize;

#[derive(Clone, Copy, Eq)]
pub struct Lit(isize);

impl Lit {
    pub fn from_dimacs(l: isize) -> Self {
        Lit(l)
    }

    pub fn signum(self) -> isize {
        self.0.signum()
    }

    pub fn var(self) -> Var {
        self.0.abs()
    }
}

impl std::ops::Neg for Lit {
    type Output = Lit;
    fn neg(self) -> Self::Output {
        Lit(-self.0)
    }
}

impl PartialEq for Lit {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl PartialOrd for Lit {
    fn partial_cmp(&self, other: &Lit) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl Ord for Lit {
    fn cmp(&self, other: &Lit) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl FromStr for Lit {
    type Err = <usize as FromStr>::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        isize::from_str(s).map(Self::from_dimacs)
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A clause index.
pub type ClauseIndex = usize;
/// A component index.
pub type ComponentIndex = usize;
/// A model list index.
pub type ListIndex = usize;
pub type Model = BTreeSet<Lit>;
pub type Assumption = BTreeSet<Lit>;
