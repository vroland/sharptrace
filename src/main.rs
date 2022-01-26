use clap::Parser;
use rayon::prelude::*;
use sharptrace_check::{HeaderParser, ParseError, VerificationError, Verifier};
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use thiserror::Error;

#[derive(Parser, Debug)]
#[clap(author, version, about)]
struct Args {
    /// Name of the input proof trace, - for stdin
    #[clap(default_value = "-")]
    trace: PathBuf,

    /// Number of threads for claim verification, 0 = auto
    #[clap(short, long, default_value_t = 0)]
    threads: usize,
}

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
    let args = Args::parse();

    // set number of threads
    rayon::ThreadPoolBuilder::new()
        .num_threads(args.threads)
        .build_global()
        .expect("could not initialize thread pool!");

    // choose input
    let stdin = std::io::stdin();
    let parser = if args.trace == PathBuf::from("-") {
        eprint!("reading from stdin...");
        let reader = Box::new(stdin.lock().lines());
        HeaderParser::from(reader)
    } else {
        eprint!("reading from {:?}...", args.trace);
        let reader = Box::new(BufReader::new(File::open(args.trace)?).lines());
        HeaderParser::from(reader)
    }?;

    let bp = match parser.read_to_body() {
        Ok(bp) => bp,
        Err((l, e)) => {
            eprintln! {};
            eprintln! {"error in proof line {}: {}", l, e};
            std::process::exit(1);
        }
    };
    let trace = match bp.parse_complete() {
        Ok(t) => t,
        Err((l, e)) => {
            eprintln! {};
            eprintln! {"error in proof line {}: {}", l, e};
            std::process::exit(2);
        }
    };
    eprintln!("done.");
    trace.print_stats();

    let verifier = Verifier::new(&trace);

    // verify claims
    let claim_count = trace.get_claims().count();
    let counts_verified = AtomicUsize::new(0);
    trace.get_claims().par_bridge().for_each(|claim| {
        let old_count = counts_verified.fetch_add(1, Ordering::SeqCst);

        if old_count % 100 == 0 {
            eprint! {"\rverifying claims... {}%", (old_count * 100) / claim_count};
        }
        if let Err(e) = verifier.verify_claim(claim) {
            eprintln! {};
            eprintln! {"verification error for {} of component {}: {}", claim, trace.comp_id_of(claim), e}
            std::process::exit(3);
        }
    });
    eprintln! {"\rclaims verified.          "};

    let root = trace.find_root_claim().map_err(ParseError::from)?;
    eprintln! {"root model count: {}", root.count()};
    Ok(())
}
