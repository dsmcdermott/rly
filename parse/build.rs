use std::io::Result;

use rly_common::doc_build;

fn main() -> Result<()> {
	let h: &[&str] = &[];
	doc_build::build("src/parser_doc.md", "src/lib_content.rs", "src/lib.rs", h)
}
