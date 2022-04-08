use lex::LexerBuilder;
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
	let mut builder = LexerBuilder::new().unwrap();
	builder.build()?;
	assert_eq!(builder.name(), Some("lex-tests_lex".as_ref()));
	assert_eq!(builder.location(), Some("lex-tests_lex.lex".as_ref()));
	builder
		.with_name("lex-alt")?
		.at_location("lex-tests-alt.lex")?
		.build()?;
	assert_eq!(builder.name(), Some("lex-alt".as_ref()));
	assert_eq!(builder.location(), Some("lex-tests-alt.lex".as_ref()));
	Ok(())
}
