
use std::collections::HashSet;

pub mod regex {
	//! Re-exports from the [`regex`] crate used by the generated lexers. See the documentation there for more info.
	pub use ::regex::{Match, Regex, RegexSet};
}
use crate::regex::{Regex, RegexSet};

mod lexer_writer;
pub use lexer_writer::{write_from_reader, write_from_str, LexerWriter};

pub mod rly_common {
	//! Re-exports from the [`rly_common`] crate used by the generated lexers. See the documentation there for more info.
	pub use rly_common::errors::ErrorData;
}

mod error;
pub use error::{FmtError, LexerBuilderError, LexerError, LexerErrorKind};

mod lexers;
pub use lexers::{Error, ErrorKind, IntoTokens, Lexer, Tokens};

mod token;
pub use token::Token;

#[derive(Debug, Clone, Copy)]
// Represents a rule for lexing tokens.
// The first element is the name and the second is the regex-string for the rule.
struct TokenRule<'a>(&'a str, &'a str);

impl<'a> TokenRule<'a> {
	fn name(&self) -> &'a str {
		self.0
	}
}

// Scans src and returns a vector of TokenRules if syntactically correct.
fn scan(src: &str) -> Result<Vec<TokenRule>, LexerError> {
	let mut rules: Vec<(&str, (&str, usize))> = Vec::new();
	let mut names = HashSet::new();
	let ignore = RegexSet::new(["^[[:space:]]*#.*", "^[[:space:]]*$"]).unwrap();
	let name = Regex::new("^[[:space:]]*([[:alpha:]][0-9_[:alpha:]]*)").unwrap();
	let div = Regex::new("^[[:space:]]+:[[:space:]]+").unwrap();
	let regx = Regex::new("^\"(.*)\"[[:space:]]*$").unwrap();
	let mut lines = Vec::new();
	for (n, s) in src.lines().enumerate() {
		if ignore.is_match(s) {
			continue;
		};
		// TODO: make better error messages
		let err = |val| LexerError::fmt::<&str, &str>(val, n, s);
		let name_match = name
			.captures(s)
			.ok_or_else(|| err("missing or improperly formatted name for token rule"))?;
		let rule_name = name_match.get(1).unwrap().as_str();
		let mut rest_of_line = &s[name_match.get(0).unwrap().end()..];
		rest_of_line = &rest_of_line[div
			.find(rest_of_line)
			.ok_or_else(|| err("missing divider \":\" between name and regex"))?
			.end()..];
		let regx_val = regx
			.captures(rest_of_line)
			.ok_or_else(|| err("missing or improperly delimited regex"))?
			.get(1)
			.unwrap()
			.as_str();
		match Regex::new(regx_val) {
			Ok(comp_regx) => {
				if comp_regx.is_match("") {
					return Err(LexerError::empty(rule_name, regx_val, n, s));
				}
			}
			Err(e) => {
				return Err(LexerError::regex(e, n, s));
			}
		};
		if !names.insert(rule_name) {
			let prev = rules.iter().find(|x| x.0 == rule_name).unwrap().1 .1;
			return Err(LexerError::duplicate_name(
				rule_name,
				prev,
				lines[prev],
				n,
				s,
			));
		};
		rules.push((rule_name, (regx_val, n)));
		lines.push(s);
	}
	Ok(rules
		.iter()
		.map(|(name, (val, _n))| TokenRule(name, val))
		.collect())
}

#[cfg(test)]
mod tests {
	use super::*;

	fn print_err<T, E: std::fmt::Display>(r: Result<T, E>) -> Result<T, E> {
		r.map_err(|e| {
			eprintln!("{}", &e);
			e
		})
	}

	const TEST_DOC: &str = r##"
name : "[a-zA-Z_][0-9a-zA-Z_]*"
	# test comment : ""  
 	 str : ""[^"]*""	


comment : "#.*"
"##;

	#[test]
	fn test_scan() -> Result<(), LexerBuilderError> {
		let rules = scan(TEST_DOC)?;
		println!("{:?}", &rules);
		assert!(rules.iter().map(|x| (x.0, x.1)).eq([
			("name", "[a-zA-Z_][0-9a-zA-Z_]*"),
			("str", "\"[^\"]*\""),
			("comment", "#.*")
		]));
		Ok(())
	}

	const TEST_DOC_FAIL_REGFMT: &str = r##"
name : "[a-zA-Z_][0-9a-zA-Z_]*"
	# test comment : ""
 	 str : ""[^"]*"" .a


comment : "#.*""##;

	#[test]
	#[should_panic]
	fn test_scan_non_space_past_regex() {
		print_err(scan(TEST_DOC_FAIL_REGFMT)).unwrap();
	}

	const TEST_DOC_INVALID_REGX: &str = r##"
name : "[a-zA-Z_][0-9a-zA-Z_]*"
	# test comment : ""
 	 str : ""[^"]*""


comment : "*#.*\]""##;

	#[test]
	#[should_panic]
	fn test_scan_invalid_regex() {
		print_err(scan(TEST_DOC_INVALID_REGX)).unwrap();
	}

	const TEST_DOC_DUPLICATE_NAME: &str = r##"
name : "[a-zA-Z_][0-9a-zA-Z_]*"
	# test comment : ""
 	 str : ""[^"]*""


name : "#.*""##;

	#[test]
	#[should_panic]
	fn test_scan_duplicate_names() {
		print_err(scan(TEST_DOC_DUPLICATE_NAME)).unwrap();
	}

	const TEST_DOC_EMPTY_REGEX_MATCH: &str = r##"
name : "a?|[a-zA-Z_][0-9a-zA-Z_]*"
	# test comment : ""  
 	 str : ""[^"]*""	


comment : "#.*"
"##;

	#[test]
	#[should_panic]
	fn test_scan_empty_regex_match() {
		print_err(scan(TEST_DOC_EMPTY_REGEX_MATCH)).unwrap();
	}
}

mod build_script;
pub use build_script::{build_lexer, LexerBuilder};
// also contains 'lexer!'
