use clap::Parser;
use nom::error::convert_error;
use rayon::prelude::*;
use sharptrace_check::{HeaderParser, TraceReadError, Verifier};
use std::fs::File;
use std::io::{BufReader, Read};
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

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

fn main() -> std::io::Result<()> {
    let args = Args::parse();

    // set number of threads
    rayon::ThreadPoolBuilder::new()
        .num_threads(args.threads)
        .build_global()
        .expect("could not initialize thread pool!");

    // choose input
    let mut input = String::new();
    if args.trace == PathBuf::from("-") {
        eprint!("reading from stdin...");
        std::io::stdin().lock().read_to_string(&mut input)?;
    } else {
        eprint!("reading from {:?}...", args.trace);
        BufReader::new(File::open(args.trace)?).read_to_string(&mut input)?;
    };
    eprint!("done.\nparsing...");

    let parser = HeaderParser::from(&input);

    let bp = match parser.read_to_body() {
        Ok(t) => t,
        Err(TraceReadError::NomErr(nom::Err::Error(e)))
        | Err(TraceReadError::NomErr(nom::Err::Failure(e))) => {
            eprintln! {"error: {}", &convert_error(input.as_str(), e)};
            std::process::exit(2);
        }
        Err(e) => {
            eprintln! {"error: {}", e};
            std::process::exit(1);
        }
    };
    let trace = match bp.parse_complete() {
        Ok(t) => t,
        Err(TraceReadError::NomErr(nom::Err::Error(e)))
        | Err(TraceReadError::NomErr(nom::Err::Failure(e))) => {
            eprintln! {"error: {}", &convert_error(input.as_str(), e)};
            std::process::exit(2);
        }
        Err(e) => {
            eprintln! {"error: {}", e};
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

    let root = trace
        .find_root_claim()
        .map_err(TraceReadError::from)
        .expect("coult not find root claim!");
    eprintln! {"root model count: {}", root.count()};
    Ok(())
}
