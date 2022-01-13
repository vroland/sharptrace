use sharptrace_check::{HeaderParser, ParseError, VerificationError, Verifier};
use std::path::PathBuf;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ProofError {
    #[error("could not open the proof file")]
    IOError(#[from] std::io::Error),
    #[error("an error occured when parsing the proof")]
    ParseError(#[from] ParseError),
    #[error("an error occured while verifying the proof")]
    VerificationError(#[from] VerificationError),
}

fn main() -> Result<(), ProofError> {
    let parser = HeaderParser::from_file(&PathBuf::from("proof"))?;

    eprint!("parsing...");
    let bp = match parser.read_to_body() {
        Ok(bp) => bp,
        Err((l, e)) => {
            eprintln! {"error in proof line {}:", l};
            return Err(e.into());
        }
    };
    let trace = match bp.parse_complete() {
        Ok(t) => t,
        Err((l, e)) => {
            eprintln! {"error in proof line {}:", l};
            return Err(e.into());
        }
    };
    eprintln!("done.");
    trace.print_stats();

    let mut verifier = Verifier::new(&trace);

    // verify claims
    let claim_count = trace.get_claims().count();
    for (i, claim) in trace.get_claims().enumerate() {
        if i % 100 == 0 {
            eprint! {"\rverifying claims... {}%", (i * 100) / claim_count};
        }
        if let Err(e) = verifier.verify_claim(claim) {
            eprintln! {};
            eprintln! {"verification error for {} of component {}: {}", claim, trace.comp_id_of(claim), e}
            std::process::exit(3);
        }
    }
    eprintln! {"\rclaims verified.          "};

    let root = trace.find_root_claim().map_err(ParseError::from)?;
    eprintln! {"root model count: {}", root.count()};
    Ok(())
}
