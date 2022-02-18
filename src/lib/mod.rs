use std::cmp::Ordering;
use std::fmt;
use std::str::FromStr;

mod parse;
mod proofs;
mod trace;
mod utils;
mod verify;

pub use parse::{BodyParser, HeaderParser, Index, IntegrityError, TraceReadError};
pub use trace::*;
pub use verify::{VerificationError, Verifier};

// use smaller types to save some space
pub type Var = u32;
pub type LitInt = i32;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Lit(LitInt);

impl Lit {
    pub const fn from_dimacs(l: LitInt) -> Self {
        Lit(l)
    }

    pub fn signum(self) -> LitInt {
        self.0.signum()
    }

    pub fn var(self) -> Var {
        self.0.abs() as Var
    }

    pub fn as_int(self) -> LitInt {
        self.0
    }
}

impl std::ops::Neg for Lit {
    type Output = Lit;
    fn neg(self) -> Self::Output {
        Lit(-self.0)
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
        LitInt::from_str(s).map(Self::from_dimacs)
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
pub type ClauseIndex = Index;
/// A component index.
pub type ComponentIndex = Index;
pub type ProofIndex = Index;
pub type Assumption = Vec<Lit>;
