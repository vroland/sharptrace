mod parse;

use crate::parse::LineParser;
use std::path::PathBuf;

use std::io;

fn main() -> io::Result<()> {
    let parser = LineParser::from_file(&PathBuf::from("proof"))?;

    for (ln, l) in parser {
        println!("line {}: {:?}", ln, l.expect("parse error:"));
    }
    Ok(())
}
