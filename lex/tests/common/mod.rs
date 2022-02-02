use lex::LexerBuilderError;
use std::{fs::File, io::Write};

fn write_lex<W: Write>(fout: &mut W) -> Result<(), LexerBuilderError> {
	let fin = File::open("tests/test.lex")?;
	lex::write_from_reader(fin, fout)
}

pub fn write_test_lexer() -> Result<Result<String, std::string::FromUtf8Error>, LexerBuilderError> {
	//	let mut fout = File::create("tests/test_lexer_output.txt").unwrap();
	let mut buff = Vec::new();
	write_lex(&mut buff)?;
	Ok(String::from_utf8(buff))
}
