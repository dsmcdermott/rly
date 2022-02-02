// This module contains the Parser trait and errors used by Parser's, namely Error,
// SyntaxError, and SyntaxErrorKind.

use super::{ast::Ast, lex::Tokens};

mod errors {
	use crate::lex;
	use rly_common::errors::ErrorData;
	use std::{
		error,
		fmt::{self, Display, Formatter},
	};

	/// An enum for the kinds of [`SyntaxError`]'s.
	#[derive(Debug, PartialEq, Eq, Clone)]
	pub enum SyntaxErrorKind {
		/// For a token that was not expected by any grammar rules.
		UnexpectedToken(String),

		/// For an unexpected end-of-file when parsing.
		UnexpectedEof,
	}

	/// A type for syntax errors returned by [`Parser`](super::Parser)'s.
	///
	/// [`SyntaxError`]'s have two causes: An unexpected token and an unexpected
	/// end-of-file. The cause of a [`SyntaxError`] can be inspected with
	/// [`kind`](SyntaxError::kind).
	///
	/// ```
	/// # use parse::rly_common::errors::ErrorData;
	/// # fn gen_err_data() -> ErrorData {
	/// 	ErrorData::new("", 0, 0, 0)
	/// }
	/// use parse::{SyntaxError, SyntaxErrorKind};
	///
	/// let wrong_token = "foo";
	///
	/// let error = SyntaxError::unexpected_token(wrong_token, gen_err_data());
	///
	/// let error_kind = SyntaxErrorKind::UnexpectedToken(wrong_token.into());
	///
	/// assert_eq!(error.kind(), &error_kind);
	/// ```
	#[derive(Debug, PartialEq, Eq, Clone)]
	pub struct SyntaxError {
		kind: SyntaxErrorKind,
		data: ErrorData,
	}

	impl SyntaxError {
		/// Creates a new [`SyntaxError`] with kind
		/// [`UnexpectedToken`](SyntaxErrorKind::UnexpectedToken).
		///
		/// # Example
		///
		/// ```
		/// # use parse::rly_common::errors::ErrorData;
		/// # fn gen_err_data() -> ErrorData {
		/// 	ErrorData::new("", 0, 0, 0)
		/// }
		/// use parse::SyntaxError;
		///
		/// let wrong_token = "foo";
		///
		/// let error = SyntaxError::unexpected_token(wrong_token, gen_err_data());
		/// ```
		pub fn unexpected_token<S: Into<String>>(tok: S, data: ErrorData) -> Self {
			Self {
				kind: SyntaxErrorKind::UnexpectedToken(tok.into()),
				data,
			}
		}

		/// Creates a new [`SyntaxError`] with kind
		/// [`UnexpectedEof`](SyntaxErrorKind::UnexpectedEof).
		///
		/// # Example
		///
		/// ```
		/// # use parse::rly_common::errors::ErrorData;
		/// # fn gen_err_data() -> ErrorData {
		/// 	ErrorData::new("", 0, 0, 0)
		/// }
		/// use parse::SyntaxError;
		///
		/// let error = SyntaxError::unexpected_eof(gen_err_data());
		/// ```
		pub fn unexpected_eof(data: ErrorData) -> Self {
			Self {
				kind: SyntaxErrorKind::UnexpectedEof,
				data,
			}
		}

		/// Returns the [kind](SyntaxErrorKind) of error for `self`.
		///
		/// # Example
		///
		/// ```
		/// # use parse::rly_common::errors::ErrorData;
		/// # fn gen_err_data() -> ErrorData {
		/// 	ErrorData::new("", 0, 0, 0)
		/// }
		/// use parse::{SyntaxError, SyntaxErrorKind};
		///
		/// let wrong_token = "foo";
		///
		/// let error = SyntaxError::unexpected_token(wrong_token, gen_err_data());
		///
		/// let error_kind = SyntaxErrorKind::UnexpectedToken(wrong_token.into());
		///
		/// assert_eq!(error.kind(), &error_kind);
		/// ```
		pub fn kind(&self) -> &SyntaxErrorKind {
			&self.kind
		}

		/// Returns a reference to the [`ErrorData`] contained in `self`.
		///
		/// # Example
		/// ```
		/// use parse::rly_common::errors::ErrorData;
		/// use parse::SyntaxError;
		///
		/// fn gen_err_data() -> ErrorData {
		/// 	// ...
		/// 	ErrorData::new("", 0, 0, 0)
		/// }
		///
		/// let wrong_token = "foo";
		///
		/// let err_data = gen_err_data();
		///
		/// let error = SyntaxError::unexpected_token(wrong_token, err_data.clone());
		///
		/// assert_eq!(error.data(), &err_data);
		/// ```
		pub fn data(&self) -> &ErrorData {
			&self.data
		}
	}

	impl Display for SyntaxError {
		fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
			let mut write = |arg| {
				write!(
					f,
					"Unexpected {} on line {}:\n{}",
					arg,
					self.data.lineno(),
					self.data.line_offset(),
				)
			};
			match &self.kind {
				SyntaxErrorKind::UnexpectedToken(s) => {
					write(format_args!("token '{}'", s.as_str()))
				}
				SyntaxErrorKind::UnexpectedEof => write(format_args!("EOF")),
			}
		}
	}

	impl error::Error for SyntaxError {}

	/// An umbrella type for errors returned by a [`Parser`].
	///
	/// Can be either a [`SyntaxError`], or a [lexer error](lex::Error).
	///
	/// [`Parser`]: super::Parser
	#[derive(Debug)]
	pub enum Error {
		SyntaxError(SyntaxError),
		LexerError(lex::Error),
	}

	impl Display for Error {
		fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
			match self {
				Self::SyntaxError(e) => e.fmt(f),
				Self::LexerError(e) => e.fmt(f),
			}
		}
	}

	impl From<SyntaxError> for Error {
		fn from(e: SyntaxError) -> Self {
			Self::SyntaxError(e)
		}
	}

	impl From<lex::Error> for Error {
		fn from(e: lex::Error) -> Self {
			Self::LexerError(e)
		}
	}

	impl error::Error for Error {
		fn source(&self) -> Option<&(dyn error::Error + 'static)> {
			Some(match self {
				Self::SyntaxError(e) => e,
				Self::LexerError(e) => e,
			})
		}
	}
}

pub use errors::{Error, SyntaxError, SyntaxErrorKind};

pub trait Parser<'a, L, T, B, U>: Sized
where
	L: Tokens<'a, T>,
{
	fn new<I>(inp: I) -> Result<Self, Error>
	where
		I: IntoIterator<IntoIter = L>;

	fn parse(&mut self) -> Result<Ast<B, U>, Error>;
}
