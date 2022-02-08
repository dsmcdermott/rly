// This module contains code for writing a parser from a grammar rule specification.
// 'Rules' represents a set of grammar or production rules, and ParserSpec represents a
// set of generated tables for a LR(1) parser. Rules' contain references to the source
// str, and ParserSpec's contain references to a Rules.
//
// ParserSpec's write parser modules by implementing Display (via the wrapper struct
// ParserDisplay), where the Displayed text is the source code for a parser module. This
// is done using src/parser_template.rs as a format string, where components are writen by
// creating wrapper structs around the data to be formatted, and having those structs also
// implement Display by writing out their data as the correctly formatted components.

use crate::{
	START,
	EOF,
	error::ParserError,
	grammar_rule_structures::Prim,
	grammar_rules::GrammarRules,
	scanning::{Scanner, SrcError},
	sym_map::{FromUsize, IntoUsize, InvalidDiscriminant, SymMap},
	table_construction::Table,
};
use std::{
	collections::HashMap,
	fmt::{Display, Formatter, Result as FmtResult},
	io::{self, Write},
};

/// A struct representing a parsed collection of grammar or production rules.
///
/// `'a` is the lifetime of the source text from which the rules were parsed, and `N` and
/// `T` are the discriminant types for non-terminal and terminal symbols respectively.
///
/// # Creating Rules
///
/// Instances of [`Rules`] can be created with [`Rules::new`], which parses a source
/// [`str`] and returns its [`Rules`].
///
/// ```
/// use parse::Rules;
///
/// let src = r"
/// 	Start -> Expr;
/// 	Expr -> Fact;
/// 	Fact -> lparen Expr rparen;
/// 	Fact -> n;
/// 	Fact -> plus Fact;
/// 	Fact -> Fact plus n;
/// ";
///
/// let rules = Rules::<u32, u32>::new(src).unwrap();
/// ```
///
/// Alternatively, one can use [`Rules::from_rule_map`] to create a [`Rules`] from a
/// mapping of strings for non-terminals to the bodies of their rules. For example:
///
/// ```
/// use std::collections::HashMap;
/// use parse::Rules;
///
/// let mut map: HashMap<&str, Vec<Box<[&str]>>> = HashMap::new();
///
/// map.insert("Start", vec![["Expr"].into()]);
/// map.insert("Expr", vec![["Fact"].into()]);
/// map.insert("Fact", vec![
/// 	["lparen", "Expr", "rparen"].into(),
/// 	["n"].into(),
/// 	["plus", "Fact"].into(),
/// 	["Fact", "plus", "n"].into()
/// ]);
///
/// let rules = Rules::<u32, u32>::from_rule_map(&map).unwrap();
/// ```
///
/// # Using Rules
///
/// [`Rules`] contains all the information necessary for generating a parser for the
/// language defined by the given production rules. The process of generating and writing
/// a parser module to a [writer](Write) can be streamlined with [`Rules::write`].
/// However, the process of generating a parser is computationally expensive. So if you
/// intend to use the generated parser tables multiple times, it is recomended to use a
/// [`ParserSpec`], which stores the result of generating a parser.
///
/// ```
/// use parse::Rules;
///
/// let src = r"
/// 	Start -> Expr;
/// 	Expr -> Fact;
/// 	Fact -> lparen Expr rparen;
/// 	Fact -> n;
/// 	Fact -> plus Fact;
/// 	Fact -> Fact plus n;
/// ";
///
/// let rules = Rules::<u32, u32>::new(src).unwrap();
///
/// let mut fout_1: Vec<u8> = Vec::new();
/// let mut fout_2: Vec<u8> = Vec::new();
/// let mut fout_3: Vec<u8> = Vec::new();
///
/// rules.write(&mut fout_1).unwrap();	// Generates, then consumes a ParserSpec
///
/// let spec = rules.gen_spec();
///
/// spec.write(&mut fout_2).unwrap();
/// spec.write(&mut fout_3).unwrap();	// Avoids re-generating a ParserSpec
/// ```

#[derive(Debug)]
pub struct Rules<'a, N: Prim, T: Prim> {
	map: SymMap<'a>,
	rules: GrammarRules<N, T>,
}

impl<'a, N: Prim, T: Prim> Rules<'a, N, T> {
	fn map(&self) -> &SymMap<'a> {
		&self.map
	}

	fn rules(&self) -> &GrammarRules<N, T> {
		&self.rules
	}
}

impl<'a, N, T> Rules<'a, N, T>
where
	N: Prim + FromUsize,
	T: Prim + FromUsize,
{
	fn from_sym_map(
		map: SymMap<'a>,
		rules: &HashMap<&'a str, Vec<Box<[&'a str]>>>,
	) -> Result<Self, InvalidDiscriminant> {
		let start = map.non_term_val(START).unwrap();
		let eof = map.term_val(EOF).unwrap();
		let rules = GrammarRules::new(map.grammar_rules(rules)?, start, eof);
		Ok(Self { map, rules })
	}

	// TODO: Figure out what kind of return type this method should have.

	/// Creates a [`Rules`] from a representation of a set of grammar rules in the form of
	/// a mapping from the non-terminal symbols (as [`str`]'s) to [`Vec`]'s of their right
	/// hand sides (as [boxed slices](Box) of [`str`]'s.)
	///
	/// Returns [`Some(result)`](Some) if `map` is a valid grammar specification, otherwise
	/// it returns [`None`].
	///
	/// # Example
	///
	/// ```
	/// use std::collections::HashMap;
	/// use parse::Rules;
	///
	/// let mut map: HashMap<&str, Vec<Box<[&str]>>> = HashMap::new();
	///
	/// map.insert("Start", vec![["Expr"].into()]);
	/// map.insert("Expr", vec![["Fact"].into()]);
	/// map.insert("Fact", vec![
	/// 	["lparen", "Expr", "rparen"].into(),
	/// 	["n"].into(),
	/// 	["plus", "Fact"].into(),
	/// 	["Fact", "plus", "n"].into()
	/// ]);
	///
	/// let rules = Rules::<u32, u32>::from_rule_map(&map).unwrap();
	/// ```
	pub fn from_rule_map(
		map: &HashMap<&'a str, Vec<Box<[&'a str]>>>,
	) -> Option<Result<Self, InvalidDiscriminant>> {
		SrcError::check_rules(map).map(|m| Self::from_rule_map_unchecked(m))
	}

	fn from_rule_map_unchecked(
		map: &HashMap<&'a str, Vec<Box<[&'a str]>>>,
	) -> Result<Self, InvalidDiscriminant> {
		Self::from_sym_map(SymMap::new(map), map)
	}

	/// Parses a grammar specification `src` into a [`Rules`]
	///
	/// # Example
	///
	/// ```
	/// use parse::Rules;
	///
	/// let src = r"
	/// 	Start -> Expr;
	/// 	Expr -> Fact;
	/// 	Fact -> lparen Expr rparen;
	/// 	Fact -> n;
	/// 	Fact -> plus Fact;
	/// 	Fact -> Fact plus n;
	/// ";
	///
	/// let rules = Rules::<u32, u32>::new(src).unwrap();
	/// ```
	pub fn new<S: AsRef<str> + ?Sized>(src: &'a S) -> Result<Self, ParserError> {
		let map = scan_text(src)?;
		let rules = Self::from_rule_map_unchecked(&map)?;
		Ok(rules)
	}
}

impl<'a, N, T> Rules<'a, N, T>
where
	N: Prim + IntoUsize,
	T: Prim + IntoUsize,
{
	/// Generates a [`ParserSpec`] and uses it to write a parser module to `fout`.
	///
	/// # Example
	///
	/// ```no_run
	/// use std::fs::File;
	/// use parse::Rules;
	///
	/// let src = r"
	/// 	Start -> Expr;
	/// 	Expr -> Fact;
	/// 	Fact -> lparen Expr rparen;
	/// 	Fact -> n;
	/// 	Fact -> plus Fact;
	/// 	Fact -> Fact plus n;
	/// ";
	///
	/// let rules = Rules::<u32, u32>::new(src).unwrap();
	///
	/// let fout = File::create("parser.rs")
	/// 	.expect("unable to create file 'parser.rs'");
	///
	/// rules.write(fout)
	/// 	.expect("unable to write to 'parser.rs'");
	/// ```
	pub fn write<W: Write>(&self, fout: W) -> io::Result<()> {
		self.gen_spec().write(fout)
	}
}

pub fn scan_text<'a, S: AsRef<str> + ?Sized>(
	src: &'a S,
) -> Result<HashMap<&'a str, Vec<Box<[&'a str]>>>, SrcError> {
	Scanner::scan_text(src.as_ref())
}

impl<'a, N: Prim, T: Prim> Rules<'a, N, T> {
	/// Generates and returns a [`ParserSpec`] based on the rules provided by `self`.
	///
	/// # Example
	///
	/// ```no_run
	/// use std::fs::File;
	/// use parse::{Rules, ParserSpec};
	///
	/// let src = r"
	/// 	Start -> Expr;
	/// 	Expr -> Fact;
	/// 	Fact -> lparen Expr rparen;
	/// 	Fact -> n;
	/// 	Fact -> plus Fact;
	/// 	Fact -> Fact plus n;
	/// ";
	///
	/// let rules = Rules::new(src).unwrap();
	///
	/// let spec: ParserSpec<'_, '_, u32, u32> = rules.gen_spec();
	/// ```
	pub fn gen_spec(&self) -> ParserSpec<'a, '_, N, T> {
		ParserSpec::new(self)
	}
}

/// A struct representing a compiled collection of LR(1) parser tables.
///
/// [`ParserSpec`] contains the results of generating a parser from a [`Rules`] and is
/// capable of writing out a parser module to a [writer](std::io::Write).
///
/// # Example
///
/// ```no_run
/// # fn main() -> std::io::Result<()> {
/// use std::fs::File;
/// use parse::{Rules, ParserSpec};
///
/// let src = r"
/// 	Start -> Expr;
/// 	Expr -> Fact;
/// 	Fact -> lparen Expr rparen;
/// 	Fact -> n;
/// 	Fact -> plus Fact;
/// 	Fact -> Fact plus n;
/// ";
///
/// let rules = Rules::new(src).unwrap();
///
/// let spec: ParserSpec<'_, '_, u32, u32> = rules.gen_spec();
///
/// let mut fout = File::create("my_parser.rs")?;
///
/// spec.write(&mut fout)?;
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
pub struct ParserSpec<'a, 'b, N: Prim, T: Prim> {
	rules: &'b Rules<'a, N, T>,
	tables: Vec<Table<'b, N, T>>,
}

impl<'a, 'b, N: Prim, T: Prim> ParserSpec<'a, 'b, N, T> {
	/// Creates a new [`ParserSpec`] from a [`Rules`].
	///
	/// # Example
	///
	/// ```no_run
	/// use std::fs::File;
	/// use parse::{Rules, ParserSpec};
	///
	/// let src = r"
	/// 	Start -> Expr;
	/// 	Expr -> Fact;
	/// 	Fact -> lparen Expr rparen;
	/// 	Fact -> n;
	/// 	Fact -> plus Fact;
	/// 	Fact -> Fact plus n;
	/// ";
	///
	/// let rules = Rules::<u32, u32>::new(src).unwrap();
	///
	/// let spec = ParserSpec::new(&rules);
	/// ```
	pub fn new(rules: &'b Rules<'a, N, T>) -> Self {
		let tables = rules.rules().build_tables();
		Self { rules, tables }
	}

	fn map(&self) -> &'b SymMap<'a> {
		self.rules.map()
	}

	fn gr(&self) -> &'b GrammarRules<N, T> {
		self.rules.rules()
	}

	/// Returns the [`Rules`] used by `self`.
	///
	/// # Example
	///
	/// ```
	/// use std::ptr;
	/// use parse::{Rules, ParserSpec};
	///
	/// let src = r"
	/// 	Start -> Expr;
	/// 	Expr -> Fact;
	/// 	Fact -> lparen Expr rparen;
	/// 	Fact -> n;
	/// 	Fact -> plus Fact;
	/// 	Fact -> Fact plus n;
	/// ";
	///
	/// let rules = Rules::<u32, u32>::new(src).unwrap();
	/// let rules_ref = &rules;
	///
	/// let spec = ParserSpec::new(rules_ref);
	/// assert!(ptr::eq(spec.rules(), rules_ref));
	/// ```
	pub fn rules(&self) -> &'b Rules<'a, N, T> {
		self.rules
	}
}

impl<'a, 'b, N: Prim + IntoUsize, T: Prim + IntoUsize> ParserSpec<'a, 'b, N, T> {
	fn display(&self) -> ParserDisplay<'a, 'b, '_, N, T> {
		ParserDisplay(self)
	}

	/// Returns a string containing a parser module for `self`.
	///
	/// # Example
	///
	/// ```
	/// # fn main() -> std::io::Result<()> {
	/// use std::fs::File;
	/// use parse::{Rules, ParserSpec};
	///
	/// let src = r"
	/// 	Start -> Expr;
	/// 	Expr -> Fact;
	/// 	Fact -> lparen Expr rparen;
	/// 	Fact -> n;
	/// 	Fact -> plus Fact;
	/// 	Fact -> Fact plus n;
	/// ";
	///
	/// let rules = Rules::new(src).unwrap();
	///
	/// let spec: ParserSpec<'_, '_, u32, u32> = rules.gen_spec();
	///
	/// let mut fout = Vec::<u8>::new();
	///
	/// spec.write(&mut fout).unwrap();
	///
	/// let src = String::from_utf8(fout).unwrap();
	///
	/// assert_eq!(src, spec.as_string());
	/// # Ok(())
	/// # }
	/// ```
	pub fn as_string(&self) -> String {
		format!("{}", self.display())
	}

	/// Writes a parser module to `fout`.
	///
	/// # Example
	///
	/// ```no_run
	/// # fn main() -> std::io::Result<()> {
	/// use std::fs::File;
	/// use parse::{Rules, ParserSpec};
	///
	/// let src = r"
	/// 	Start -> Expr;
	/// 	Expr -> Fact;
	/// 	Fact -> lparen Expr rparen;
	/// 	Fact -> n;
	/// 	Fact -> plus Fact;
	/// 	Fact -> Fact plus n;
	/// ";
	///
	/// let rules = Rules::new(src).unwrap();
	///
	/// let spec: ParserSpec<'_, '_, u32, u32> = rules.gen_spec();
	///
	/// let mut fout = File::create("my_parser.rs")?;
	///
	/// spec.write(&mut fout)?;
	/// # Ok(())
	/// # }
	/// ```
	pub fn write<W: Write>(&self, mut fout: W) -> io::Result<()> {
		write!(fout, "{}", self.display())
	}
}

//pub fn write_from_rules<'a, 'b, N, T, W>(rules: &'b Rules<'a, N, T>, fout: W) -> io::Result<()>
//where
//	N: Prim + IntoUsize,
//	T: Prim + IntoUsize,
//	W: Write,
//{
//	ParserSpec::new(rules).write(fout)
//}

//pub fn write_from_rule_map<'a, N, T, W>(map: &HashMap<&'a str, Vec<Box<[&'a str]>>>, fout: W) -> io::Result<()>
//where
//	N: Prim + IntoUsize + FromUsize,
//	T: Prim + IntoUsize + FromUsize,
//	W: Write,
//{
//	Rules::<'a, N, T>::from_rule_map(map).gen_spec().write(fout)
//}

/// Parses the grammar specification in `src` and writes a parser module to `fout`.
///
/// This is equivalent to [`Rules::new(src)`](Rules::new) followed by
/// [`rules.write(fout)`](Rules::write).
///
/// # Example
///
/// ```
/// let src = r"
/// 	Start -> Expr;
/// 	Expr -> Fact;
/// 	Fact -> lparen Expr rparen;
/// 	Fact -> n;
/// 	Fact -> plus Fact;
/// 	Fact -> Fact plus n;
/// ";
///
/// let mut fout = Vec::<u8>::new();
///
/// parse::write_from_src::<u32, u32, _, _>(src, &mut fout).unwrap();
/// ```
pub fn write_from_src<'a, N, T, W, S>(src: &'a S, fout: W) -> Result<(), Box<dyn std::error::Error>>
where
	N: Prim + IntoUsize + FromUsize,
	T: Prim + IntoUsize + FromUsize,
	W: Write,
	S: AsRef<str> + ?Sized,
{
	Ok(Rules::<'a, N, T>::new(src)?.gen_spec().write(fout)?)
}

struct NonTermVariants<'a, 'b>(&'b SymMap<'a>);

impl<'a, 'b> Display for NonTermVariants<'a, 'b> {
	fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
		Ok(for sym in self.0.non_terms() {
			write!(f, "\tN_{},\n\t", sym)?;
		})
	}
}

struct Names<'a, 'b>(&'b SymMap<'a>);

impl<'a, 'b> Display for Names<'a, 'b> {
	fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
		Ok(for sym in self.0.non_terms() {
			write!(f, "\tNonTerm::N_{sym} => \"{sym}\",\n\t\t\t\t", sym = sym)?;
		})
	}
}

struct Shifts<'a, 'b, T>(&'b SymMap<'a>, Vec<(T, usize)>)
where
	T: Prim + IntoUsize;

impl<'a, 'b, T> Display for Shifts<'a, 'b, T>
where
	T: Prim + IntoUsize,
{
	fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
		Ok(for (term, goto) in self.1.iter().copied() {
			write!(
				f,
				"Some(TokenKind::T_{term}) => {{ let la = self.shift()?.unwrap(); self.s{goto}(AstNode::Leaf(la)) }}\n\t\t\t\t",
				term = self.0.term(term),
				goto = goto
			)?;
		})
	}
}

struct Reductions<'a, 'b, N, T>(&'b Rules<'a, N, T>, Vec<(T, (N, usize))>)
where
	N: Prim + IntoUsize,
	T: Prim + IntoUsize;

impl<'a, 'b, N, T> Display for Reductions<'a, 'b, N, T>
where
	N: Prim + IntoUsize,
	T: Prim + IntoUsize,
{
	fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
		let mut write = |la: std::fmt::Arguments<'_>, lhs: &N, n: &usize| {
			write!(
				f,
				"{la} => return ret(NonTerm::N_{lhs}, val, {n}),\n\t\t\t\t",
				la = la,
				lhs = self.0.map().non_term(*lhs),
				n = n
			)
		};
		Ok(for (la, (lhs, n)) in self.1.iter() {
			if la == self.0.rules().eof() {
				write(format_args!("None"), lhs, n)?;
			} else {
				write(
					format_args!("Some(TokenKind::T_{})", self.0.map().term(*la)),
					lhs,
					n,
				)?;
			};
		})
	}
}

struct Gotos<'a, 'b, N>(&'b SymMap<'a>, Vec<(N, usize)>)
where
	N: Prim + IntoUsize;

impl<'a, 'b, N> Display for Gotos<'a, 'b, N>
where
	N: Prim + IntoUsize,
{
	fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
		Ok(for (sym, goto) in self.1.iter().copied() {
			write!(
				f,
				"\n\t\t\t\t\t\tNonTerm::N_{sym} => self.s{goto}(AstNode::Branch(s)),",
				sym = self.0.non_term(sym),
				goto = goto
			)?;
		})
	}
}

#[rustfmt::skip]
macro_rules! state {
	() => {
r#"

		fn s{num}(&mut self{arg}) -> {return_type} {{{table_details}
			let mut res: (Ast<'a>, usize) = match self.kind() {{
				{shifts}{reductions}_ => Err(Error::from(self.err())),
			}}?;
			loop {{
				let ({mut_stack}s, n) = res;
				if n == 0 {{
					res = match *s.label() {{{gotos}{return_on_start}
						_ => goto_err(),
					}}?;
				}} else {{
					{handle_return}
				}};
			}};
		}}"#
	};
}

struct TableDetails<'a, 'b, 'c, N, T>(&'b SymMap<'a>, &'c Table<'b, N, T>)
where
	N: Prim + IntoUsize,
	T: Prim + IntoUsize;

impl<'a, 'b, 'c, N, T> Display for TableDetails<'a, 'b, 'c, N, T>
where
	N: Prim + IntoUsize,
	T: Prim + IntoUsize,
{
	fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
		self.1.display_items(
			|arg| write!(f, "\n\t\t\t//{}", arg),
			|n| self.0.non_term(*n),
			|t| self.0.term(*t),
		)
	}
}

struct State<'a, 'b, 'c, N, T>(&'b Rules<'a, N, T>, &'c Table<'b, N, T>)
where
	N: Prim + IntoUsize,
	T: Prim + IntoUsize;

impl<'a, 'b, 'c, N, T> Display for State<'a, 'b, 'c, N, T>
where
	N: Prim + IntoUsize,
	T: Prim + IntoUsize,
{
	fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
		let (shifts, reductions, gotos) = self.1.actions();
		let num = self.1.number();
		let (arg, return_type, mut_stack, return_on_start, handle_return) = if num == 0 {
			(
				"",
				"Result<Ast<'a>>",
				"",
				"\n\t\t\t\t\t\tSTART => return Ok(s),",
				"panic!(\"Unexpected error in parsing\")",
			)
		} else {
			(
				", val: AstNode<NonTerm, Token<'a>>",
				"Res<'a>",
				"mut ",
				"",
				"s.push(val);\n\t\t\t\t\treturn Ok((s, n-1));",
			)
		};
		write!(
			f,
			state!(),
			num = num,
			arg = arg,
			return_type = return_type,
			table_details = TableDetails(self.0.map(), self.1),
			shifts = Shifts(self.0.map(), shifts),
			reductions = Reductions(self.0, reductions),
			mut_stack = mut_stack,
			gotos = Gotos(self.0.map(), gotos),
			return_on_start = return_on_start,
			handle_return = handle_return,
		)
	}
}

struct States<'a, 'b, 'c, N, T>(&'c ParserSpec<'a, 'b, N, T>)
where
	N: Prim + IntoUsize,
	T: Prim + IntoUsize;

impl<'a, 'b, 'c, N, T> Display for States<'a, 'b, 'c, N, T>
where
	N: Prim + IntoUsize,
	T: Prim + IntoUsize,
{
	fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
		Ok(for table in &self.0.tables {
			write!(f, "{}", State(self.0.rules, table))?;
		})
	}
}

impl<'a, 'b, N, T> ParserSpec<'a, 'b, N, T>
where
	N: Prim + IntoUsize,
	T: Prim + IntoUsize,
{
	fn token_kind(&self) -> &str {
		"use super::lexer::TokenKind;"
	}

	fn non_terms(&self) -> NonTermVariants<'a, 'b> {
		NonTermVariants(self.map())
	}

	fn names(&self) -> Names<'a, 'b> {
		Names(self.map())
	}

	fn start(&self) -> String {
		format!("N_{}", self.map().non_term(*self.gr().start()))
	}

	fn states(&self) -> States<'a, 'b, '_, N, T> {
		States(self)
	}
}

pub struct ParserDisplay<'a, 'b, 'c, N: Prim, T: Prim>(&'c ParserSpec<'a, 'b, N, T>);

impl<'a, 'b, 'c, N, T> Display for ParserDisplay<'a, 'b, 'c, N, T>
where
	N: Prim + IntoUsize,
	T: Prim + IntoUsize,
{
	fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
		write!(
			f,
			concat!("//", include_str!("parser_template.rs")),
			non_term_vals = format_args!("{:?}", self.0.map().non_terms()),
			term_vals = format_args!("{:?}", self.0.map().terms()),
			token_kind = self.0.token_kind(),
			non_terms = self.0.non_terms(),
			names = self.0.names(),
			start = self.0.start(),
			states = self.0.states(),
		)
	}
}

#[cfg(test)]
mod tests {
	use super::{ParserSpec, Rules};

	const TEST_DOC: &'static str = r#"

Start -> Expr;
Expr -> Fact ; 

Fact -> lparen Expr rparen
; Fact -> n;
	Fact 
-> plus Fact;

Fact -> 
	Fact
	plus
	n
;"#;

	mod gen {
		use super::*;

		pub type NType = u8;

		pub type TType = u8;

		pub fn rules() -> Rules<'static, NType, TType> {
			Rules::new(TEST_DOC).unwrap()
		}

		pub fn spec<'b>(
			rules: &'b Rules<'static, NType, TType>,
		) -> ParserSpec<'static, 'b, NType, TType> {
			ParserSpec::new(rules)
		}
	}

	use gen::{rules, spec};

	#[test]
	fn test_spec_gen() {
		let rules = rules();
		let _spec = spec(&rules);
	}
}
