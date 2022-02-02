// This module defines the `LexerBuilderError`type which is a generic type for errors encountered when creating lexers.
use regex::Error as RError;
use rly_common::builders;
use std::error;
use std::fmt::{Display, Formatter, Result};
use std::io::Error as IOError;

#[derive(Debug)]
/// A type for syntax errors in Lexer definitions.
//
// `val` is an errormessage indicating the nature of the error, and `line` indicates which line of the source the error occured on.
pub struct FmtError {
	val: String,
}

impl FmtError {
	pub(crate) fn new<S: Into<String>>(val: S) -> Self {
		Self { val: val.into() }
	}
}

impl Display for FmtError {
	fn fmt(&self, f: &mut Formatter<'_>) -> Result {
		self.val.fmt(f)
	}
}

//impl Display for FmtError {
//	fn fmt(&self, f: &mut Formatter<'_>) -> Result {
//		write!(f, "Invalid lexer syntax on line {}: {}", self.line, &self.val)
//	}
//}
//
//impl error::Error for FmtError {}

/// The different kinds of [`LexerError`]'s.
#[derive(Debug)]
pub enum LexerErrorKind {
	/// For invalid regex's.
	Regex(RError),
	/// For syntax errors in the lexer source.
	Fmt(FmtError),
	/// For token rules that match and empty string.
	EmptyRegexMatch {
		/// The name of the rule.
		name: String,
		/// The source string for the regex.
		regex: String,
	},
	/// For duplicate token names.
	DuplicateName {
		name: String,
		previous_lineno: usize,
		previous_line: String,
	},
}

#[derive(Debug)]
/// A type for errors encountered when creating lexers.
///
/// Its methods can be used to determine the [kind](LexerErrorKind) of error, which line
/// number it occured on, and what the contents of that line were.

//pub struct Error(ErrorKind);
pub struct LexerError {
	kind: LexerErrorKind,
	lineno: usize,
	line: String,
}

use LexerErrorKind::*;

impl LexerError {
	/// Returns a reference to the [`LexerErrorKind`] for `self`.
	pub fn kind(&self) -> &LexerErrorKind {
		&self.kind
	}

	/// Returns the line number (starting from 0) on which the error occured.
	pub fn lineno(&self) -> usize {
		self.lineno
	}

	/// Returns the line in which the error occured as a [`str`].
	pub fn line(&self) -> &str {
		&self.line
	}

	fn new(kind: LexerErrorKind, lineno: usize, line: String) -> Self {
		Self { kind, lineno, line }
	}

	pub(crate) fn regex<S: Into<String>>(e: RError, lineno: usize, line: S) -> Self {
		Self::new(Regex(e), lineno, line.into())
	}

	pub(crate) fn fmt<S: Into<String>, T: Into<String>>(val: S, lineno: usize, line: S) -> Self {
		Self::new(Fmt(FmtError::new(val)), lineno, line.into())
	}

	pub(crate) fn empty<S: Into<String>, T: Into<String>, U: Into<String>>(
		name: T,
		regex: U,
		lineno: usize,
		line: S,
	) -> Self {
		Self::new(
			EmptyRegexMatch {
				name: name.into(),
				regex: regex.into(),
			},
			lineno,
			line.into(),
		)
	}

	pub(crate) fn duplicate_name<S: Into<String>, T: Into<String>, U: Into<String>>(
		name: T,
		previous_lineno: usize,
		previous_line: U,
		lineno: usize,
		line: S,
	) -> Self {
		Self::new(
			DuplicateName {
				name: name.into(),
				previous_lineno,
				previous_line: previous_line.into(),
			},
			lineno,
			line.into(),
		)
	}
}

impl Display for LexerError {
	fn fmt(&self, f: &mut Formatter<'_>) -> Result {
		match self.kind() {
			Regex(e) => write!(f, "Invalid regex on line {}: {}\n{}", self.lineno(), e, self.line()),
			Fmt(e) => write!(f, "Invalid lexer syntax on line {}: {}\n{}", self.lineno(), e, self.line()),
			EmptyRegexMatch { name, regex } => write!(f, "The regex '{}' for '{}' on line {} matches an empty string. Rules for tokens cannot match empty strings\n{}", regex, name, self.lineno(), self.line()),
			DuplicateName { name, previous_lineno, previous_line } => write!(f, "The token '{}' is defined on line {}:\n{}\nAnd defined again on line {}:\n{}\nTokens cannot have multiple definitions.", name, previous_lineno, previous_line, self.lineno(), self.line()),
		}
	}
}

impl error::Error for LexerError {}

/// An umbrella type for errors encountered when generating and writing [lexer
/// modules](crate#lexer-structure)
#[derive(Debug)]
pub enum LexerBuilderError {
	Lexer(LexerError),
	IO(IOError),
	Builder(builders::Error),
}

impl From<LexerError> for LexerBuilderError {
	fn from(e: LexerError) -> Self {
		Self::Lexer(e)
	}
}

impl From<IOError> for LexerBuilderError {
	fn from(e: IOError) -> Self {
		Self::IO(e)
	}
}

impl From<builders::Error> for LexerBuilderError {
	fn from(e: builders::Error) -> Self {
		Self::Builder(e)
	}
}

impl Display for LexerBuilderError {
	fn fmt(&self, f: &mut Formatter<'_>) -> Result {
		use LexerBuilderError::*;
		match self {
			Lexer(e) => <LexerError as Display>::fmt(e, f),
			IO(e) => e.fmt(f),
			Builder(e) => e.fmt(f),
		}
	}
}

impl error::Error for LexerBuilderError {}
