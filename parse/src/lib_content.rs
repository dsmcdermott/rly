mod grammar_rule_structures;

pub use grammar_rule_structures::Prim;

mod grammar_rules;

//pub use grammar_rules::GrammarRules;

mod table_construction;

//pub use table_construction::{TableBuilder, Table};

mod scanning;

pub use scanning::SrcError;

mod sym_map;

pub use sym_map::{FromUsize, IntoUsize, InvalidDiscriminant};

mod grammar_spec;

pub use grammar_spec::{write_from_src, ParserSpec, Rules};

pub mod rly_common {
	//! Re-exports from the crate [`rly_common`]. Used by [generated
	//! parsers](crate#parser-structure).
	pub use rly_common::errors;
}

pub mod lex {
	//! Re-exports from the crate [`lex`]. Used by [generated
	//! parsers](crate#parser-structure).
	pub use lex::{Error, Token, Tokens};
}

mod build_script;
pub use build_script::ParserBuilder;

mod parser;
pub use parser::{Error, Parser, SyntaxError, SyntaxErrorKind};

pub mod ast;

mod error {
	use super::{InvalidDiscriminant, SrcError};
	pub use rly_common::builders::Error as BuilderError;
	use std::{
		error::Error,
		fmt::{Display, Formatter, Result},
		io,
	};

	/// An umbrella type for the different errors that can occur when generating and
	/// writing parsers.
	#[non_exhaustive]
	#[derive(Debug)]
	pub enum ParserError {
		SrcError(SrcError),
		IOError(io::Error),
		BuilderError(BuilderError),
		InvalidDiscriminant(InvalidDiscriminant),
	}

	impl Display for ParserError {
		fn fmt(&self, f: &mut Formatter<'_>) -> Result {
			match self {
				Self::SrcError(e) => e.fmt(f),
				Self::IOError(e) => e.fmt(f),
				Self::BuilderError(e) => e.fmt(f),
				Self::InvalidDiscriminant(e) => e.fmt(f),
			}
		}
	}

	impl Error for ParserError {
		fn source(&self) -> Option<&(dyn Error + 'static)> {
			match self {
				Self::SrcError(e) => Some(e),
				Self::IOError(e) => Some(e),
				Self::BuilderError(e) => Some(e),
				Self::InvalidDiscriminant(e) => Some(e),
			}
		}
	}

	macro_rules! impl_from {
		($variant: ident, $origin: ty) => {
			impl From<$origin> for ParserError {
				fn from(t: $origin) -> Self {
					Self::$variant(t)
				}
			}
		};
	}

	macro_rules! impl_from_s {
		($($variant: ident),*) => { $(impl_from!($variant, $variant);)* }
	}

	impl_from_s!(SrcError, BuilderError, InvalidDiscriminant);
	impl_from!(IOError, io::Error);
}

pub use error::ParserError;

/// A re-export of [`rly_common::builders::Error`](::rly_common::builders::Error).
pub use error::BuilderError;
