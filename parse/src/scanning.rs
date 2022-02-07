// This module contains the Scanner struct, which is responsable for scanning strings and
// generating a RuleMap (HashMap<&str, Vec<Box<[&str]>>>,) which is the first step in
// generating a parser. The RuleMap is a mapping from left hand side non-terminal symbols
// to their right hand sides. This is then processed by other components in this crate to
// extract the data necessary for building a parser.
//
// Parser source files contain a sequence of rules of the form:
// RULE ::= IDENT '->' IDENT+ ';'
// Whitespace (including newlines) is ignored.
//
// START and "eof" are special identifiers. There must be exactly one rule with START as
// the left-hand-side and START cannot appear on the right-hand-side of any rules. "eof"
// is reserved and cannot be used.
use crate::START;

use std::{boxed::Box, collections::HashMap};

use regex::{Match, Regex};

use rly_common::errors::ErrorData;

// An aggregation of production rules in the form of a mapping from left hand side
// (non-terminal) symbols to their right hand sides, where both terminal and non-terminal
// symbols are represented by str references derived from the source.
//
// No real reason for having it be Vec<Box<[_]>> other than that I thought Vec<Vec<_>>
// might be more confusing at a glance
pub type RuleMap<'a> = HashMap<&'a str, Vec<Box<[&'a str]>>>;

const NAME: &'static str = "^[[:alpha:]][0-9_[:alpha:]]*";
const DIV: &'static str = "^->";
const TERM: &'static str = "^;";
const IGNORE: &'static str = "^[[:space:]]+";

// Scans its input 'inp' to generate a RuleMap. name, div, term, and ignore are all
// generated according to the constants above. The input is parsed using a kind of
// recursive descent parser.
pub struct Scanner<'a> {
	inp: &'a str,
	pos: usize,
	rules: RuleMap<'a>,
	name: Regex,
	div: Regex,
	term: Regex,
	ignore: Regex,
}

mod error {
	use crate::START;
	use rly_common::errors::ErrorData;

	use std::{
		error,
		fmt::{Display, Formatter, Result},
	};

	/// A syntax error in a parser source.
	///
	/// For errors that have a logial location[^no_loc], the corresponding variant
	/// contains an [`ErrorData`] that describes the location of the error.
	///
	/// [^no_loc]: which is all of them except [`NoStart`](Self::NoStart), for sources that
	/// lack a "`Start`" rule, and [`EmptyInput`](Self::EmptyInput), for sources that are
	/// empty.
	///
	/// # Example
	///
	/// ```
	/// use parse::{Rules, SrcError, ParserError};
	///
	/// let src = "\
	///     foo -> bar;
	///     90 -> foo;
	/// ";
	///
	/// let err = Rules::<u32, u32>::new(src).err().unwrap();
	///
	/// let src_err = match err {
	/// 	ParserError::SrcError(e) => e,
	/// 	_ => unreachable!(),
	/// };
	///
	/// match src_err {
	/// 	SrcError::InvalidIdent(data) => assert_eq!(data.lineno(), 1),
	/// 	_ => unreachable!(),
	/// };
	/// ```
	#[derive(Debug, PartialEq, Eq, Clone)]
	pub enum SrcError {
		/// For invalid identifiers.
		InvalidIdent(ErrorData),
		/// A missing divider "`->`".
		MissingDiv(ErrorData),
		/// A missing rule terminator "`;`".
		MissingTerm(ErrorData),
		/// No rule for "`Start`".
		NoStart,
		/// Multiple rules for "`Start`".
		DuplicateStart(ErrorData),
		/// Reserved identifier "`eof`" used.
		EofUsed(ErrorData),
		/// Source is empty.
		EmptyInput,
	}

	impl SrcError {
		pub(crate) fn check_rules<'a, 'b>(
			rules: &'a super::RuleMap<'b>,
		) -> Option<&'a super::RuleMap<'b>> {
			use regex::Regex;
			let ident = Regex::new(super::NAME).unwrap();
			macro_rules! check {
				($cond: expr) => {
					if !$cond {
						return None;
					};
				};
			}
			let check_ident = |name: &str| {
				if let Some(mtch) = ident.find(name) {
					(mtch.end() == name.len()) && (name != "eof")
				} else {
					false
				}
			};
			check!(rules.get(START)?.len() == 1);
			for key in rules.keys() {
				check!(check_ident(key));
				let rhss = rules.get(key).unwrap();
				check!(rhss.len() != 0);
				for rhs in rhss {
					check!(rhs.len() != 0);
					for name in rhs.iter() {
						check!(check_ident(name));
						check!(*name != START);
					}
				}
			}
			Some(rules)
		}
	}

	impl Display for SrcError {
		fn fmt(&self, f: &mut Formatter<'_>) -> Result {
			use SrcError::*;
			fn write<T: Display>(f: &mut Formatter<'_>, mssg: T, data: &ErrorData) -> Result {
				write!(
					f,
					"Syntax error on line {}: {}\n{}",
					data.lineno(),
					mssg,
					data.line_offset()
				)
			}
			fn wnd<T: Display>(mssg: T, f: &mut Formatter<'_>) -> Result {
				write!(f, "Syntax error: {}", mssg)
			}
			match self {
				InvalidIdent(data) => write(f, "Not a valid identifier.", data),
				MissingDiv(data) => write(f, "Missing '->'", data),
				MissingTerm(data) => write(f, "Missing closing ';'", data),
				DuplicateStart(data) => write(f, format_args!("Only one rule for '{}' allowed", START), data),
				EofUsed(data) => write(f, "'eof' is a reserved value", data),
				NoStart => wnd(format_args!("Must have a rule for '{}'", START), f),
				EmptyInput => wnd("Input is empty", f),
			}
		}
	}

	impl error::Error for SrcError {}
}

pub use error::SrcError;

pub type Result<T> = std::result::Result<T, SrcError>;

impl<'a> Scanner<'a> {
	pub fn new(inp: &'a str) -> Self {
		Self {
			inp,
			pos: 0,
			rules: HashMap::new(),
			name: Regex::new(NAME).unwrap(),
			div: Regex::new(DIV).unwrap(),
			term: Regex::new(TERM).unwrap(),
			ignore: Regex::new(IGNORE).unwrap(),
		}
	}

	fn name(&self) -> &Regex {
		&self.name
	}

	fn div(&self) -> &Regex {
		&self.div
	}

	fn term(&self) -> &Regex {
		&self.term
	}

	fn ignore(&self) -> &Regex {
		&self.ignore
	}

	fn find(&self, reg: &Regex) -> Option<Match<'a>> {
		reg.find(&self.inp[self.pos..])
	}

	fn find_ignore(&self) -> Option<Match<'a>> {
		self.find(self.ignore())
	}

	fn find_name(&self) -> Result<Match<'a>> {
		match self.find(self.name()) {
			Some(rmatch) if rmatch.as_str() != "eof" => Ok(rmatch),
			None => Err(self.err(SrcError::InvalidIdent)),
			_ => Err(self.err(SrcError::EofUsed)),
		}
	}

	fn find_div(&self) -> Result<Match<'a>> {
		self.find(self.div())
			.ok_or_else(|| self.err(SrcError::MissingDiv))
	}

	fn find_term(&self) -> Result<Match<'a>> {
		self.find(self.term())
			.ok_or_else(|| self.err(SrcError::MissingTerm))
	}

	fn expect_none(&mut self) {
		if let Some(rmatch) = self.find_ignore() {
			self.update(rmatch);
		};
	}

	fn expect_lhs(&mut self) -> Result<&'a str> {
		let rmatch = self.find_name()?;
		let name = rmatch.as_str();
		if name == START && self.rules.contains_key(&name) {
			return Err(self.err(SrcError::DuplicateStart));
		};
		self.update(rmatch);
		Ok(name)
	}

	fn expect_div(&mut self) -> Result<()> {
		self.expect_none();
		let rmatch = self.find_div()?;
		self.update(rmatch);
		Ok(())
	}

	// Parses a single symbol on the right-hand-side of a production rule. If no symbols
	// are left, parses the rule terminator ';' and returns Ok(None).
	fn expect_rhs(&mut self) -> Result<Option<&'a str>> {
		self.expect_none();
		Ok(if let Some(rmatch) = self.find(self.name()) {
			self.update(rmatch);
			Some(rmatch.as_str())
		} else {
			self.expect_term()?;
			None
		})
	}

	fn expect_term(&mut self) -> Result<()> {
		let rmatch = self.find_term()?;
		self.update(rmatch);
		Ok(())
	}

	// Parses a rule and adds it to self.rules. If the imput is fully parsed, returns
	// Ok(false).
	fn expect_rule(&mut self) -> Result<bool> {
		self.expect_none();
		if self.pos == self.inp.len() {
			return Ok(false);
		};
		let lhs = self.expect_lhs()?;
		self.expect_div()?;
		let mut rhs = Vec::new();
		loop {
			match self.expect_rhs()? {
				Some(sym) => rhs.push(sym),
				None => break,
			};
		}
		self.rules
			.entry(lhs)
			.or_insert_with(|| Vec::new())
			.push(rhs.into_boxed_slice());
		Ok(true)
	}

	fn check_has_start(&self) -> Result<()> {
		if !self.rules.contains_key(START) {
			Err(SrcError::NoStart)
		} else {
			Ok(())
		}
	}

	pub fn scan(&mut self) -> Result<()> {
		while self.expect_rule()? {}
		self.check_has_start()
	}

	pub fn make_rules(mut self) -> Result<RuleMap<'a>> {
		self.scan()?;
		Ok(self.rules)
	}

	fn find_err(&self) -> ErrorData {
		println!("{} {}", self.inp.len(), self.pos);
		ErrorData::find(&self.inp, self.pos).unwrap()
	}

	fn err<F: FnOnce(ErrorData) -> SrcError>(&self, var: F) -> SrcError {
		var(self.find_err())
	}

	fn update(&mut self, rmatch: Match<'_>) {
		self.pos += rmatch.end();
	}

	pub fn scan_text(inp: &'a str) -> Result<RuleMap<'a>> {
		Self::new(inp).make_rules()
	}
}

//fn find_line(inp: &str, pos: usize) -> usize {
//	assert!(pos <= inp.len());
//	let mut count = 0;
//	for (num, line) in inp.split('\n').enumerate() {
//		count += line.len() + 1;
//		if pos <= count {
//			return num;
//		};
//	};
//	unreachable!();
//}

#[cfg(test)]
mod tests {

	#[test]
	fn test_regex_construction() {
		use super::Scanner;
		Scanner::new("");
	}

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

	fn assert<T, E: std::fmt::Display + std::fmt::Debug>(res: std::result::Result<T, E>) -> T {
		match res {
			Ok(t) => t,
			Err(e) => panic!("\n{}", e),
		}
	}

	#[test]
	fn test_scan() {
		use super::Scanner;
		println!("{:?}", assert(Scanner::scan_text(TEST_DOC)));
	}

	const TEST_DOC_ERR: &'static str = r#"

Start -> Expr;
Expr -> Fact ; 

lparen Expr rparen
; Fact -> n;
	Fact 
-> plus Fact;

Fact -> 
	Fact
	plus
	n
;"#;

	#[test]
	fn test_scan_err() {
		use super::Scanner;
		println!("{}", Scanner::scan_text(TEST_DOC_ERR).unwrap_err());
	}
}
