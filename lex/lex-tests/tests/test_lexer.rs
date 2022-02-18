
lex::lexer!();

mod lex_alt {
	lex::lexer!("lex-alt");
	pub use lexer::*;
}

const LEX_INP: &'static str = " A * 2	+  1";
const LEX_INVALID: &'static str = "A - B";
const LEX_ERR_RULE: &'static str = r"A \ B";

fn test_lexing<T, L>(inp: &str, res: &[(T, &str)])
where
	T: Copy + std::fmt::Debug + Eq,
	L: lex::Lexer<T>,
	for<'r, 's> &'r L: lex::IntoTokens<'s, T>,
{
	use lex::IntoTokens;
	let rules = L::new();
	let lexer = rules.lex(inp);
	let mut tokens = Vec::new();
	for token in lexer {
		let tok = token.unwrap();
		tokens.push((*tok.kind(), tok.val()));
	};
	assert_eq!(&tokens, res);
}

#[test]
fn test_lexing_main() {
	use lexer::{Lexer, TokenKind::{self, *}};
	let kind_val = [
		(id, "A"),
		(mul, "*"),
		(int, "2"),
		(sum, "+"),
		(int, "1"),
	];
	test_lexing::<TokenKind, Lexer>(LEX_INP, &kind_val);
}

fn test_err<T, L>(inp: &str, first_kind: T, first_val: &str, err_kind: lex::ErrorKind, err_val: &str)
where
	T: Eq + std::fmt::Debug,
	L: lex::Lexer<T>,
	for <'r, 's> &'r L: lex::IntoTokens<'s, T>,
{
	use lex::IntoTokens;
	let rules = L::new();
	let mut lexer = rules.lex(inp);
	let tok = lexer.next().unwrap().unwrap();
	assert_eq!(tok.kind(), &first_kind);
	assert_eq!(tok.val(), first_val);
	let err = lexer.next().unwrap().unwrap_err();
	assert_eq!(err.kind(), err_kind);
	assert_eq!(err.val(), err_val);
}

#[test]
fn test_lexing_invalid() {
	use lex::ErrorKind;
	use lexer::{TokenKind, Lexer};
	test_err::<TokenKind, Lexer>(LEX_INVALID, TokenKind::id, "A", ErrorKind::UnrecognisedInput, "-");
}

#[test]
fn test_lexing_err() {
	use lex::ErrorKind;
	use lexer::{TokenKind, Lexer};
	test_err::<TokenKind, Lexer>(LEX_ERR_RULE, TokenKind::id, "A", ErrorKind::ErrorRule, "\\");
}

const LEX_ALT_INP: &'static str = " 0xa + 0o6 + 	test - 9";
const LEX_ALT_INVALID: &'static str = "A * B";
const LEX_ALT_ERR: &'static str = "5 five 5";

#[test]
fn test_lexing_alt() {
	use lex_alt::{Lexer, TokenKind::{self, *}};
	let kind_val = [
		(HEX, "0xa"),
		(PLUS, "+"),
		(OCT, "0o6"),
		(PLUS, "+"),
		(IDENT, "test"),
		(MINUS, "-"),
		(DEC, "9"),
	];
	test_lexing::<TokenKind, Lexer>(LEX_ALT_INP, &kind_val);
}

#[test]
fn test_lexing_alt_invalid() {
	use lex::ErrorKind;
	use lex_alt::{TokenKind, Lexer};
	test_err::<TokenKind, Lexer>(LEX_ALT_INVALID, TokenKind::IDENT, "A", ErrorKind::UnrecognisedInput, "*");
}

#[test]
fn test_lexing_alt_err() {
	use lex::ErrorKind;
	use lex_alt::{TokenKind, Lexer};
	test_err::<TokenKind, Lexer>(LEX_ALT_ERR, TokenKind::DEC, "5", ErrorKind::ErrorRule, "five");
}
