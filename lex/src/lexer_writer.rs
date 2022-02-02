// This module contains code for writing lexer modules using rusts native string formatting api.
//
// It does this by wrapping the relevant data in custom structs that implement the `Display`
// trait, using formatting strings as templates to write out the correctly composed code.

use super::{scan, LexerBuilderError, LexerError, TokenRule};
use std::{
	fmt::{Arguments, Display, Formatter, Result as FmtResult},
	io::{Read, Write},
};

/// A struct that contains a specification of lexing rules and can write out a lexer module.
pub struct LexerWriter<'a> {
	rules: Vec<TokenRule<'a>>,
	ignore_index: Option<usize>,
	error_index: Option<usize>,
}

// These are templates used as format strings in writing out sections of the lexer. They're
// instantiated by macros, rather than constants, because the rust formatting macros only
// work with string literals, but if we define the strings as macros they'll be inserted by
// the preprocessor before expanding the enclosing macro call.

macro_rules! token_rule {
	() => {
		r#"		pub const T_{name}: &'static str = r{edge}"{value}"{edge};
		pub const T_ANCHOR_{name}: &'static str = r{edge}"^{value}"{edge};
"#
	};
}

macro_rules! special_index {
	() => {
		"\t\tpub const {name}_INDEX: usize = {index};\n"
	};
}

macro_rules! ignore_case {
	() => {
		"\t\t\t\trules::IGNORE_INDEX => self.get_next(),\n"
	};
}

macro_rules! error_case {
	() => {
		r#"				rules::ERROR_INDEX => {{ let val = reg_match.as_str(); Err(Error::error_rule(val)) }}
"#
	};
}

struct TokenRules<'w, 'a>(&'w LexerWriter<'a>);

impl<'w, 'a> Display for TokenRules<'w, 'a> {
	fn fmt(&self, f: &mut Formatter) -> FmtResult {
		for TokenRule(name, value) in self.0.rules.iter().copied() {
			let edge = "#".repeat(sanitize(value));
			write!(f, token_rule!(), name = name, edge = edge, value = value)?;
		}
		Ok(())
	}
}

struct SpecialIndex(Option<usize>, &'static str);

impl Display for SpecialIndex {
	fn fmt(&self, f: &mut Formatter) -> FmtResult {
		match self.0 {
			Some(n) => write!(f, special_index!(), name = self.1, index = n),
			None => Ok(()),
		}
	}
}

struct TokenVariants<'w, 'a>(&'w LexerWriter<'a>);

impl<'w, 'a> Display for TokenVariants<'w, 'a> {
	fn fmt(&self, f: &mut Formatter) -> FmtResult {
		for pair in self.0.rules.iter().enumerate() {
			if let Some(rule) = self.0.is_user_rule(pair) {
				write!(f, "\tT_{name},\n\t", name = rule.name())?;
			};
		}
		Ok(())
	}
}

struct TokenDisplay<'w, 'a>(&'w LexerWriter<'a>);

impl<'w, 'a> Display for TokenDisplay<'w, 'a> {
	fn fmt(&self, f: &mut Formatter) -> FmtResult {
		for pair in self.0.rules.iter().enumerate() {
			if let Some(rule) = self.0.is_user_rule(pair) {
				write!(
					f,
					"\tTokenKind::T_{name} => write!(f, {name:?}),\n\t\t\t\t",
					name = rule.name()
				)?;
			};
		}
		Ok(())
	}
}

struct KindArrayElements<'w, 'a>(&'w LexerWriter<'a>);

impl<'w, 'a> Display for KindArrayElements<'w, 'a> {
	fn fmt(&self, f: &mut Formatter) -> FmtResult {
		for pair in self.0.rules.iter().enumerate() {
			match self.0.is_user_rule(pair) {
				Some(rule) => write!(f, " Some(TokenKind::T_{}),", rule.name()),
				None => write!(f, " None,"),
			}?;
		}
		Ok(())
	}
}

struct LexerRules<'w, 'a>(&'w LexerWriter<'a>);

impl<'w, 'a> Display for LexerRules<'w, 'a> {
	fn fmt(&self, f: &mut Formatter) -> FmtResult {
		for rule in self.0.rules.iter() {
			write!(f, " rules::T_ANCHOR_{},", rule.name())?;
		}
		Ok(())
	}
}

struct LexerRegs<'w, 'a>(&'w LexerWriter<'a>);

impl<'w, 'a> Display for LexerRegs<'w, 'a> {
	fn fmt(&self, f: &mut Formatter) -> FmtResult {
		for rule in self.0.rules.iter() {
			write!(f, " Regex::new(rules::T_{}).unwrap(),", rule.name())?;
		}
		Ok(())
	}
}

impl<'a> LexerWriter<'a> {
	fn new<I>(iter: I) -> Self
	where
		I: IntoIterator<Item = TokenRule<'a>>,
	{
		let mut ignore_index = None;
		let mut error_index = None;
		let find_index = |(index, rule): &(usize, TokenRule<'a>)| {
			let name = rule.name();
			if ignore_index.is_none() && name == "ignore" {
				ignore_index = Some(*index);
			} else if error_index.is_none() && name == "error" {
				error_index = Some(*index);
			}
		};
		let rules = iter
			.into_iter()
			.enumerate()
			.inspect(find_index)
			.map(|(_index, rule)| rule)
			.collect();
		Self {
			rules,
			ignore_index,
			error_index,
		}
	}

	fn token_rules(&self) -> TokenRules<'_, 'a> {
		TokenRules(self)
	}

	fn ignore_index(&self) -> SpecialIndex {
		SpecialIndex(self.ignore_index, "IGNORE")
	}

	fn error_index(&self) -> SpecialIndex {
		SpecialIndex(self.error_index, "ERROR")
	}

	fn token_variants(&self) -> TokenVariants<'_, 'a> {
		TokenVariants(self)
	}

	fn token_display(&self) -> TokenDisplay<'_, 'a> {
		TokenDisplay(self)
	}

	fn rules_len(&self) -> usize {
		self.rules.len()
	}

	fn kind_array_elements(&self) -> KindArrayElements<'_, 'a> {
		KindArrayElements(self)
	}

	fn lexer_rules(&self) -> LexerRules<'_, 'a> {
		LexerRules(self)
	}

	fn lexer_regs(&self) -> LexerRegs<'_, 'a> {
		LexerRegs(self)
	}

	fn ignore_case(&self) -> Arguments<'_> {
		match self.ignore_index {
			Some(_) => format_args!(ignore_case!()),
			None => format_args!(""),
		}
	}

	fn error_case(&self) -> Arguments<'_> {
		match self.error_index {
			Some(_) => format_args!(error_case!()),
			None => format_args!(""),
		}
	}

	/// Writes a module containing a [`Lexer`](crate#lexer-structure) to the writer
	/// `fout`.
	///
	/// # Example
	///``` no_run
	/// use std::fs::File;
	/// use std::env;
	/// use std::path::PathBuf;
	/// use lex::LexerWriter;
	///
	/// let rules = r#"
	/// 	id : "[a-zA-Z_][0-9a-zA-Z_]*"
	/// 	ignore : "[[:space:]]+"
	/// 	int : "[0-9]+"
	/// 	error : "/""#;
	///
	/// let writer = LexerWriter::from_str(rules).unwrap();
	///
	/// let out_dir = env::var_os("OUT_DIR").unwrap();
	/// let mut loc = PathBuf::from(out_dir);
	/// loc.push("lexer.rs");
	/// let fout = File::create(loc).unwrap();
	///
	/// writer.write(fout).unwrap();
	///```
	pub fn write<W: Write>(&self, mut fout: W) -> Result<(), LexerBuilderError> {
		macro_rules! write_fields {
			($($name: ident),*) => {
				write!(fout,
					concat!("//", include_str!("lexer_template.rs")),
					$($name = self.$name()),*
				)
			};
		}
		write_fields!(
			token_rules,
			ignore_index,
			error_index,
			token_variants,
			token_display,
			rules_len,
			kind_array_elements,
			lexer_rules,
			lexer_regs,
			ignore_case,
			error_case
		)
		.map_err(|e| e.into())
	}

	fn is_user_rule(&self, inp: (usize, &TokenRule<'a>)) -> Option<TokenRule<'a>> {
		let (n, rule) = inp;
		let n = Some(n);
		if n != self.ignore_index && n != self.error_index {
			Some(*rule)
		} else {
			None
		}
	}

	/// Parses the input `text` and returns a [`LexerWriter`] if the text is a valid description
	/// of a lexer, otherwise it returns an [`LexerError`],
	///
	/// # Example
	///```
	/// use lex::LexerWriter;
	///
	/// let rules = r#"
	/// 	id : "[a-zA-Z_][0-9a-zA-Z_]*"
	/// 	ignore : "[[:space:]]+"
	/// 	int : "[0-9]+"
	/// 	error : "/""#;
	///
	/// let writer = LexerWriter::from_str(rules).unwrap();
	///```
	pub fn from_str(text: &'a str) -> Result<Self, LexerError> {
		let rules = scan(text)?;
		let writer = Self::new(rules);
		Ok(writer)
	}
}

// Scans a string and returns the number of `#`'s that must be used to use the string with
// rusts raw string syntax
fn sanitize(s: &str) -> usize {
	use std::cmp::max;
	let mut count = 0;
	let mut temp_count = 0;
	let mut flag = false;
	for char in s.chars() {
		if flag {
			if char == '#' {
				temp_count += 1;
			} else {
				count = max(count, temp_count);
				temp_count = 0;
				flag = char.eq(&'"');
			}
		} else {
			flag = char.eq(&'"');
		}
	}
	max(count, temp_count)
}

/// Parses the string `text` for a [`LexerWriter`] and then writes the
/// [`Lexer`](crate#lexer-structure) to the output `fout`. See [`LexerWriter::write`] and
/// [`LexerWriter::from_str`] for more detailes
///
/// # Example
///```no_run
/// use std::fs::File;
/// use std::env;
/// use std::path::PathBuf;
/// use lex::LexerWriter;
/// use lex::write_from_str;
///
/// let rules = r#"
/// 	id : "[a-zA-Z_][0-9a-zA-Z_]*"
/// 	ignore : "[[:space:]]+"
/// 	int : "[0-9]+"
/// 	error : "/""#;
///
/// let out_dir = env::var_os("OUT_DIR").unwrap();
/// let mut loc = PathBuf::from(out_dir);
/// loc.push("lexer.rs");
/// let fout = File::create(loc).unwrap();
///
/// write_from_str(rules, fout).unwrap()
///```
pub fn write_from_str<W>(text: &str, fout: W) -> Result<(), LexerBuilderError>
where
	W: Write,
{
	LexerWriter::from_str(text)?.write(fout)
}

/// Like [`write_from_str`] but reads the text from the specified input `fin`. See the
/// [documentation for `write_from_str`](write_from_str) for more details.
///
/// # Example
///```no_run
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use std::fs::File;
/// use std::env;
/// use std::path::PathBuf;
/// use lex::LexerWriter;
/// use lex::write_from_reader;
///
/// let fin = File::open("my_lexer.lex")?;
/// let out_dir = env::var_os("OUT_DIR").unwrap();
/// let mut loc = PathBuf::from(out_dir);
/// loc.push("my_lexer.lex");
/// let fout = File::create(loc)?;
///
/// write_from_reader(fin, fout)?;
/// # Ok(())
/// # }
///```
pub fn write_from_reader<R, W>(mut fin: R, fout: W) -> Result<(), LexerBuilderError>
where
	R: Read,
	W: Write,
{
	let mut text = String::new();
	fin.read_to_string(&mut text)?;
	write_from_str(&text, fout)
}

#[cfg(test)]
mod tests {
	use super::{LexerWriter, TokenRule};

	const RULES: [TokenRule<'static>; 4] = [
		TokenRule("id", "[a-zA-Z_][0-9a-zA-Z_]*"),
		TokenRule("ignore", "[[:space:]]+"),
		TokenRule("int", "[0-9]+"),
		TokenRule("error", r"/\"),
	];

	#[test]
	fn test_write() {
		let writer = LexerWriter::new(RULES);
		let mut buff = Vec::<u8>::new();
		writer.write(&mut buff).unwrap();
	}
}
