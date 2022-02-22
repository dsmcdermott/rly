use lex::LexerBuilder;
use parse::ParserBuilder;

fn main() {
	LexerBuilder::new()
		.unwrap()
		.build()
		.expect("error generating 'parse-tests_lex.lex'")
		.at_location("alt-lex.lex").unwrap()
		.with_name("alt-lex").unwrap()
		.build()
		.expect("error generating 'alt-lex.lex'");

	let mut builder = ParserBuilder::new().unwrap();
	builder
		.build::<u32, u32>()
		.expect("error generating 'parse-tests_parse.y");
	builder
		.at_location("alt-parse.y").unwrap()
		.with_name("alt-parse").unwrap()
		.force_load_file().unwrap();
	builder
		.build::<u32, u32>()
		.expect("error generating 'parse-alt.y'");
}
