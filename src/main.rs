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

    let list_count = trace.get_lists().count();
    for (i, list) in trace.get_lists().enumerate() {
        if i % (list_count / 100) == 0 {
            eprint! {"\rverifying lists... {}%", (i * 100) / list_count};
        }
        verifier.verify_list(*list).expect("verification error:")
    }
    eprintln! {"\rlists verified.           "};

    let claim_count = trace.get_claims().count();
    for (i, claim) in trace.get_claims().enumerate() {
        if i % (claim_count / 100) == 0 {
            eprint! {"\rverifying claims... {}%", (i * 100) / claim_count};
        }
        verifier.verify_claim(claim).expect("verification error:");
    }
    eprintln! {"\rclaims verified.          "};

    let root = trace.find_root_claim().expect("no root claim!");
    eprintln! {"root model count: {}", root.count()};
    Ok(())
}
