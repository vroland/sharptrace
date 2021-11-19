use sharptrace_check::{HeaderParser, Verifier};
use std::path::PathBuf;

use std::io;

fn main() -> io::Result<()> {
    let parser = HeaderParser::from_file(&PathBuf::from("proof"))?;

    eprint!("parsing...");
    let bp = parser.read_to_body().expect("parse error:");
    let trace = bp.parse_complete().expect("parse error:");
    eprintln!("done.");
    trace.print_stats();

    let mut verifier = Verifier::new(&trace);

    for list in trace.get_lists() {
        verifier.verify_list(*list).expect("verification error:")
    }

    for (i, claim) in trace.get_claims().enumerate() {
        verifier.verify_claim(claim).expect("verification error:");
        if i % 1000 == 0 && i > 0 {
            eprintln! {"{} claims verified.", i};
        }
    }
    Ok(())
}
