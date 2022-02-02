use std::fs::File;
use std::io::{Read, Write};

mod common;

use common::write_test_lexer;

use diff::{lines, Result as DR};


//const MOD_HEADER: &'static str = r#"
//#[allow(nonstandard_style, dead_code)]
//mod lexer {
//"#;


fn build_test_lexer() {
	let mut fout = File::create("tests/test_lexer/test_lexer.rs").unwrap();
	fout.write_all(write_test_lexer().unwrap().unwrap().as_bytes()).unwrap();
}

#[test]
fn test_lexer_is_configured() {
//	let mut fout = File::create(fout_name).unwrap();
//	fout.write_all("mod lexer {\n".as_bytes()).unwrap();
//	fout.write_all(write_test_lexer_output().unwrap().unwrap().as_bytes()).unwrap();
//	fout.write_all("}\n".as_bytes()).unwrap();
	let mut buff = String::new();
	buff.push_str(&write_test_lexer().unwrap().unwrap());
	if &buff != include_str!("test_lexer/test_lexer.rs") {
		build_test_lexer();
		eprintln!("Error: test_lexer tests couldn't be run since the lexer file was not properly configured: re-run the tests");
		panic!();
	};
}

#[test]
fn test_template_changes() {
	let lexer = write_test_lexer().unwrap().unwrap();
	let diff: Vec<_> = lines(include_str!("test_lexer_copy"), &lexer)
		.into_iter()
		.filter(|res| match res {
			DR::Left(_) => true,
			DR::Right(_) => true,
			_ => false,
		})
		.collect();
	if !diff.is_empty() {
		for res in diff {
			match res {
				DR::Left(s) => eprintln!("-{}", s),
				DR::Right(s) => eprintln!("+{}", s),
				_ => unreachable!(),
			};
		};
		panic!();
	};
}


include!{"test_lexer/test_lexer.rs"}

use lexer::Lexer;
use lex::Error;

#[test]
fn test_new_lexer() {
	Lexer::new();
}

#[test]
fn test_lexing() -> Result<(), Error> {
	let rules = Lexer::new();
	let mut input = String::new();
	File::open("tests/test_lexer/test_lexer_input").unwrap().read_to_string(&mut input).unwrap();
	let lexer = rules.lex(&input);
	let mut tokens = Vec::new();
	for tok in lexer {
		tokens.push(tok?);
	};
	println!("{:?}", tokens);
	Ok(())
}
