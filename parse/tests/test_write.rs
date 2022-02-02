use lex::write_from_str;
use parse::{ParserSpec, Rules};
use std::fs::File;

//const TEST_DOC: &'static str = r#"
//
//start -> Expr;
//Expr -> Fact ;
//
//Expr -> lparen Expr rparen
//; Fact -> n;
//	Fact
//-> plus Fact;
//
//Fact ->
//	Fact
//	plus
//	n
//;"#;

const ALT_TEST_DOC: &'static str = r"
start -> Sum;
Sum -> Sum plus Fact;
Sum -> Fact;
Fact -> Fact mult Term;
Fact -> Term;
Term -> int;
Term -> id;
Term -> lparen Sum rparen;
";

type NTYPE = u8;

type TTYPE = u8;

//fn rules() -> Rules<'static, N_TYPE, T_TYPE>
//{
//	Rules::new(TEST_DOC).unwrap()
//}

fn alt_rules() -> Rules<'static, NTYPE, TTYPE> {
	Rules::new(ALT_TEST_DOC).unwrap()
}

fn spec<'b>(rules: &'b Rules<'static, NTYPE, TTYPE>) -> ParserSpec<'static, 'b, NTYPE, TTYPE> {
	ParserSpec::new(rules)
}

//const TEST_LEXER_SPEC: &'static str = r#"
//lparen : "\("
//rparen : "\)"
//n : "[0-9]+"
//plus : "\+"
//ignore : "[[:space:]]+"
//"#;

const ALT_LEXER_SPEC: &'static str = r#"
plus : "\+"
mult : "\*"
int : "[0-9]+"
id : "[_a-zA-Z][_a-zA-Z0-9]*"
lparen : "\("
rparen : "\)"
ignore : "[[:space:]]"
"#;

#[test]
fn write_parser() {
	let fout = File::create("tests/test_parser").unwrap();
	let rules = alt_rules();
	let spec = spec(&rules);
	spec.write(fout).unwrap();
}

#[test]
fn write_lexer() {
	let mut fout = File::create("tests/test_lexer").unwrap();
	write_from_str(ALT_LEXER_SPEC, &mut fout).unwrap();
}

include!("test_parser");
include!("test_lexer");

const INP: &'static str = "A*2 + 4";

#[test]
fn test_parse() {
	let rules = lexer::Lexer::new();
	let lexer = rules.lex(INP);
	let mut parser = parser::Parser::new(lexer).unwrap();
	match parser.parse() {
		Ok(ast) => println!("{}", ast.display()),
		Err(e) => panic!("{}\n", e),
	};
}
