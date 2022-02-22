lex::lexer!("alt-lex");
parse::parser!("alt-parse");

use lexer::Lexer;
use parser::Ast;

use parse::{Error, SyntaxError, SyntaxErrorKind};

fn parse(s: &str) -> Result<Ast<'_>, Error> {
	let lexer = Lexer::new();
	let tokens = lexer.lex(s);
	parser::parse(tokens)
}

fn display_err<T, E>(result: Result<T, E>) -> Result<T, E>
where
	E: std::fmt::Display,
{
	if let Err(e) = &result {
		eprintln!("{}", e);
	};
	result
}

macro_rules! test_proper {
	($name: ident, $sent: literal) => {
		#[test]
		fn $name() {
			display_err(parse($sent)).unwrap();
		}
	}
}

test_proper!(test_sent, "the cat sees the mouse");

test_proper!(test_intr, "the small mouse sleeps");

test_proper!(test_adj, "the black cat chases the quick mouse");


fn unwrap_syntax_err<'a>(result: Result<Ast<'a>, Error>) -> SyntaxError {
	match result {
		Err(e) => match e {
			Error::SyntaxError(e) => e,
			Error::LexerError(e) => {
				eprintln!("{}", e);
				panic!("{:?}", e);
			}
		}
		Ok(a) => {
			eprintln!("{}", a.display());
			panic!("error not generated");
		}
	}
}

macro_rules! test_eof {
	($name: ident, $sent: literal) => {
		#[test]
		fn $name() {
			let err = unwrap_syntax_err(parse($sent));
			assert_eq!(err.kind(), &SyntaxErrorKind::UnexpectedEof);
		}
	}
}

macro_rules! test_ut {
	($name: ident, $sent: literal, $tok: literal) => {
		#[test]
		fn $name() {
			let err = unwrap_syntax_err(parse($sent));
			assert_eq!(err.kind(), &SyntaxErrorKind::UnexpectedToken($tok.to_string()));
		}
	}
}

test_eof!(test_trans_eof, "the big cat catches");

test_eof!(test_missing_noun_eof, "the gray cat sees the");

test_ut!(test_missing_noun, "the white sees the cat", "sees");

test_ut!(test_missing_det, "yellow mouse sees the cat", "yellow");
