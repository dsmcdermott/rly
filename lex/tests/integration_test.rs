use lex::LexerBuilderError;

mod common;

use common::write_test_lexer;

#[test]
fn test_lexer_building() -> Result<(), LexerBuilderError> {
	write_test_lexer()?.unwrap();
	Ok(())
}
