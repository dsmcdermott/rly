// This module contains the Token struct.

use rly_common::errors::ErrorData;

/// The type of tokens returned by [`Lexer`](super::Lexer)'s.
///
/// In `Token<'a, T>`, `'a` is the lifetime of the source `str` from which the token was
/// lexed, and `T` is the type of the discriminant used to differentiate different types
/// of tokens (e.g. "identifier" or "integer" or "open parenthesis" etc.)
///
/// The type of a token can be accessed with [`Token::kind`] and the value of a token, in
/// the form of the sub-`str` of the source from which it was parsed, can be accessed with
/// [`Token::val`].
///
/// # Example
///
/// ```
/// use lex::Token;
///
/// enum TokenKind {
/// 	Ident,
/// 	Int,
/// 	Sum,
/// }
/// use TokenKind::*;
///
/// let src = "A + 2 + 5";
///
/// let tok = |kind, start| Token::new(kind, src, start, start + 1).unwrap();
///
/// let tokens = [
/// 	tok(Ident, 0),
/// 	tok(Sum, 2),
/// 	tok(Int, 4),
/// 	tok(Sum, 6),
/// 	tok(Int, 8),
/// ];
///
/// for token in &tokens {
/// 	assert_eq!(token.src(), src);
/// };
///
/// assert_eq!(
/// 	tokens
/// 		.into_iter()
/// 		.map(|t| t.val())
/// 		.collect::<Vec<_>>(),
/// 	["A", "+", "2", "+", "5"]
/// );
/// ```
///
/// # Errors
///
/// `Token`'s can also generate [`ErrorData`]'s for themselves, for use with error
/// reporting. For example:
///
/// ```
/// use lex::Token;
///
/// enum TokenKind {
/// 	Ident,
/// 	Int,
/// 	Sum,
/// }
/// use TokenKind::*;
///
/// let src = "5 + 4 +";
///
/// let trailing_sum = Token::new(Sum, src, 6, 7).unwrap();
///
/// let err_mssg = format!(
/// 	"'+' operator without a right operand:\n{}",
/// 	trailing_sum.get_error_data().line_offset()
/// );
///
/// assert_eq!(err_mssg, "\
/// '+' operator without a right operand:
/// 5 + 4 +
///       ^");
/// ```

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Token<'a, T> {
	kind: T,
	val: &'a str,
	src: &'a str,
}

impl<'a, T> Token<'a, T> {
	/// Creates a new instance of [`Token`] of kind `kind` and with a value consisting of
	/// `src[start..end]`[^max_size].
	///
	/// If `start..end` is a valid substring of `src`, this function returns
	/// [`Some(token)`], otherwise it returns [`None`].
	///
	/// # Safety
	///
	/// Unlikely as it is, it can lead to undefined behaviour if `start` is greater than
	/// [`isize::MAX`]. This is only checked by [`Token::new`] if compiled with
	/// debug-assertions.
	///
	/// ```no_run
	/// use lex::Token;
	///
	/// let start = usize::try_from(isize::MAX).unwrap() + 1;
	/// let end = usize::try_from(isize::MAX).unwrap() + 2;
	///
	/// let bytes = [b' '; isize::MAX as usize + 1];      // roughly 9,223 petabytes(!) on a 64bit system
	///
	/// let src = std::str::from_utf8(&bytes).unwrap();
	///
	/// let token = Token::new((), src, start, end).unwrap();
	///
	/// let pos = token.pos();          // undefined behaviour
	/// ```
	///
	/// # Example
	///
	/// ```
	/// use std::ptr;
	/// use lex::Token;
	///
	/// #[derive(Debug, PartialEq, Eq)]
	/// enum TokenKind {
	/// 	Ident,
	/// 	Int,
	/// 	Sum,
	/// }
	/// use TokenKind::*;
	///
	/// let src = "A + 5 + 3";
	///
	/// let token = Token::new(Int, src, 4, 5).unwrap();
	///
	/// assert_eq!(token.kind(), &Int);
	/// assert_eq!(token.val(), "5");
	/// assert!(ptr::eq(token.src(), src));
	/// assert_eq!(token.pos(), 4);
	///
	/// let invalid_token = Token::new(Ident, src, 10, 6);
	///
	/// assert!(invalid_token.is_none());
	/// ```
	pub fn new(kind: T, src: &'a str, start: usize, end: usize) -> Option<Self> {
		debug_assert!(start <= usize::try_from(isize::MAX).unwrap());
		let val = src.get(start..end)?;
		Some(Self { kind, val, src })
	}

	/// Returns a reference to the discriminant for the type of toke of `self`.
	///
	/// # Example
	///
	/// ```
	/// use lex::Token;
	///
	/// #[derive(Debug, PartialEq, Eq)]
	/// enum TokenKind {
	/// 	Ident,
	/// 	Int,
	/// 	Sum,
	/// }
	/// use TokenKind::*;
	///
	/// let src = "A + 5 + 3";
	///
	/// let token = Token::new(Int, src, 4, 5).unwrap();
	///
	/// assert_eq!(token.kind(), &Int);
	/// ```
	pub fn kind(&self) -> &T {
		&self.kind
	}

	/// Returns the original [`str`] for `self`.
	///
	/// # Example
	///
	/// ```
	/// use lex::Token;
	///
	/// enum TokenKind {
	/// 	Ident,
	/// 	Int,
	/// 	Sum,
	/// }
	/// use TokenKind::*;
	///
	/// let src = "A + 5 + 3";
	///
	/// let token = Token::new(Int, src, 4, 5).unwrap();
	///
	/// assert_eq!(token.val(), "5");
	/// ```
	pub fn val(&self) -> &'a str {
		self.val
	}

	/// Returns the source from which `self` was lexed.
	///
	/// # Example
	///
	/// ```
	/// use std::ptr;
	/// use lex::Token;
	///
	/// enum TokenKind {
	/// 	Ident,
	/// 	Int,
	/// 	Sum,
	/// }
	/// use TokenKind::*;
	///
	/// let src = "A + 5 + 3";
	///
	/// let token = Token::new(Int, src, 4, 5).unwrap();
	///
	/// assert!(ptr::eq(token.src(), src));
	/// ```
	pub fn src(&self) -> &'a str {
		self.src
	}

	/// Returns the index or position of [`self.val`](Self::val) within
	/// [`self.src()`](Self::src). Or in other words the position of the token within the
	/// source.
	///
	/// # Example
	///
	/// ```
	/// use lex::Token;
	///
	/// enum TokenKind {
	/// 	Ident,
	/// 	Int,
	/// 	Sum,
	/// }
	/// use TokenKind::*;
	///
	/// let src = "A + 5 + 3";
	///
	/// let token = Token::new(Int, src, 4, 5).unwrap();
	///
	/// assert_eq!(token.pos(), 4);
	pub fn pos(&self) -> usize {
		// Safety: self.val is guarenteed to be a substring of, and derived from,
		// self.src. Therefore, pointers are derived from a pointer to the same object and
		// are within bounds of the same allocated object. Offsets larger than isize::MAX
		// are exceedingly unlikely, but are still are still guarenteed to be caught when
		// run in debug mode.

		unsafe { usize::try_from(self.val.as_ptr().offset_from(self.src.as_ptr())).unwrap() }
	}

	/// Generates an [`ErrorData`] corresponding to the location of `self` within
	/// [`self.src()`](Self::src).
	///
	/// # Example
	///
	/// ```
	/// use lex::Token;
	///
	/// enum TokenKind {
	/// 	Ident,
	/// 	Int,
	/// 	Sum,
	/// }
	/// use TokenKind::*;
	///
	/// let src = "5 + 4 +";
	///
	/// let trailing_sum = Token::new(Sum, src, 6, 7).unwrap();
	///
	/// let err_mssg = format!(
	/// 	"'+' operator without a right operand:\n{}",
	/// 	trailing_sum.get_error_data().line_offset()
	/// );
	///
	/// assert_eq!(err_mssg, "\
	/// '+' operator without a right operand:
	/// 5 + 4 +
	///       ^");
	/// ```
	pub fn get_error_data(&self) -> ErrorData {
		ErrorData::find(self.src(), self.pos()).unwrap()
	}

	/// Finds the line, line number, and column number on whitch the token starts. Similar
	/// to calling [`ErrorData::gen_data`] on [`self.src()`](Self::src) and
	/// [`self.pos()`](Self::pos).
	///
	/// # Example
	///
	/// ```
	/// use lex::Token;
	///
	/// enum TokenKind {
	/// 	Ident,
	/// 	Int,
	/// 	Sum,
	/// }
	/// use TokenKind::*;
	///
	/// let src = "5 + 4 +";
	///
	/// let trailing_sum = Token::new(Sum, src, 6, 7).unwrap();
	///
	/// let (line, lineno, colno) = trailing_sum.get_context();
	///
	/// assert_eq!(line, "5 + 4 +");
	/// assert_eq!(lineno, 0);
	/// assert_eq!(colno, 6);
	/// ```
	pub fn get_context(&self) -> (&str, usize, usize) {
		ErrorData::gen_data(self.src(), self.pos()).unwrap()
	}
}

mod display {
	use super::Token;
	use std::fmt::{Display, Formatter, Result};

	/// Displays `self` according to the format: `{self.kind()}("{self.val()}")`.
	///
	/// # Example
	/// ```
	/// use std::fmt::{Display, Formatter, Result};
	/// use lex::Token;
	///
	/// enum TokenKind {
	/// 	Ident,
	/// 	Int,
	/// 	Sum,
	/// }
	/// use TokenKind::*;
	///
	/// impl Display for TokenKind {
	/// 	fn fmt(&self, f: &mut Formatter<'_>) -> Result {
	/// 		write!(f, "{}", match self {
	/// 			Ident => "Ident",
	/// 			Int => "Int",
	/// 			Sum => "Sum",
	/// 		})
	/// 	}
	/// }
	///
	/// let src = "5 + val + 4";
	///
	/// let token = Token::new(Ident, src, 4, 7).unwrap();
	/// let display = format!("{}", token);
	///
	/// assert_eq!(display, r#"Ident("val")"#);
	/// ```
	impl<'a, T: Display> Display for Token<'a, T> {
		fn fmt(&self, f: &mut Formatter<'_>) -> Result {
			write!(f, "{}({:?})", self.kind(), self.val())
		}
	}
}
