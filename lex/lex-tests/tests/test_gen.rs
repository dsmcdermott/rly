use diff::Result as DR;

use std::{
	error::Error,
	fs::{self, File},
	path::Path,
};

fn gen_lexer<S: AsRef<Path>>(s: S) -> Result<String, Box<dyn Error>> {
	let fin = File::open(s)?;
	let mut buff = Vec::<u8>::new();
	lex::write_from_reader(fin, &mut buff)?;
	Ok(String::from_utf8(buff)?)
}

fn test_changes<S: AsRef<Path>, T: AsRef<Path>>(src: S, reference: T) {
	let src = src.as_ref();
	let reference = reference.as_ref();
	let lexer = gen_lexer(src).unwrap();
	let copy = fs::read_to_string(reference).unwrap();
	let diff: Vec<_> = diff::lines(&copy, &lexer)
		.into_iter()
		.filter(|res| match res {
			DR::Left(_) => true,
			DR::Right(_) => true,
			_ => false,
		})
		.collect();
	if !diff.is_empty() {
		eprintln!(
			"{}\t{}",
			&reference.to_string_lossy(),
			&src.to_string_lossy()
		);
		for res in diff {
			match res {
				DR::Left(s) => eprintln!("-{}", s),
				DR::Right(s) => eprintln!("+{}", s),
				_ => unreachable!(),
			};
		}
		panic!();
	};
}

fn test_write<S: AsRef<Path>, T: AsRef<Path>>(s: S, t: T) -> Result<(), Box<dyn Error>> {
	let fin = File::open(s)?;
	let fout = File::create(t)?;
	Ok(lex::write_from_reader(fin, fout)?)
}

#[test]
fn test_write_main() {
	test_write("lex-tests_lex.lex", "tests/out/lex-tests_lex.rs").unwrap();
}

#[test]
fn test_write_alt() {
	test_write("lex-tests-alt.lex", "tests/out/lex-alt.rs").unwrap();
}

#[test]
fn test_changes_main() {
	test_changes("lex-tests_lex.lex", "tests/copies/test_lexer_copy");
}

#[test]
fn test_changes_alt() {
	test_changes("lex-tests-alt.lex", "tests/copies/alt_lexer_copy");
}

#[test]
fn main() {
	println!("tests/test.rs: TESTING");
}
