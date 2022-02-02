use std::io::Result;

use rly_common::doc_build;

fn main() -> Result<()> {
	let additional_headers = ["#![allow(rustdoc::invalid_rust_codeblocks)]\n"];
	doc_build::build(
		"src/lexer_doc.md",
		"src/lib_content.rs",
		"src/lib.rs",
		&additional_headers,
	)
}
