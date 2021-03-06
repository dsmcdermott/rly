//compile_error!("This is just a template file and shouldn't be compiled");

#[allow(nonstandard_style, dead_code)]
#[allow(clippy::all)]
mod lexer {
	use lex::{
		regex::{
			RegexSet,
			Regex,
			Match,
		},
		Error,
	};

	mod rules {
		pub const T_id: &'static str = r"[a-zA-Z_][0-9a-zA-Z_]*";
		pub const T_ANCHOR_id: &'static str = r"^([a-zA-Z_][0-9a-zA-Z_]*)";
		pub const T_mul: &'static str = r"\*";
		pub const T_ANCHOR_mul: &'static str = r"^(\*)";
		pub const T_sum: &'static str = r"\+";
		pub const T_ANCHOR_sum: &'static str = r"^(\+)";
		pub const T_ignore: &'static str = r"[[:space:]]+";
		pub const T_ANCHOR_ignore: &'static str = r"^([[:space:]]+)";
		pub const T_int: &'static str = r"[0-9]+";
		pub const T_ANCHOR_int: &'static str = r"^([0-9]+)";
		pub const T_error: &'static str = r"\\";
		pub const T_ANCHOR_error: &'static str = r"^(\\)";
		pub const IGNORE_INDEX: usize = 3;
		pub const ERROR_INDEX: usize = 5;
	}

	#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
	pub enum TokenKind {
		r#id,
		r#mul,
		r#sum,
		r#int,
	}

	mod display {
		use std::fmt::{Display, Formatter, Result};
		use super::TokenKind;

		impl Display for TokenKind {
			fn fmt(&self, f: &mut Formatter<'_>) -> Result {
				match self {
					TokenKind::r#id => write!(f, "id"),
					TokenKind::r#mul => write!(f, "mul"),
					TokenKind::r#sum => write!(f, "sum"),
					TokenKind::r#int => write!(f, "int"),
				}
			}
		}
	}

	const KIND_ARRAY: [Option<TokenKind>; 6] = [ Some(TokenKind::r#id), Some(TokenKind::r#mul), Some(TokenKind::r#sum), None, Some(TokenKind::r#int), None, ];

	pub type Token<'a> = lex::Token<'a, TokenKind>;

	pub struct Lexer {
		set: RegexSet,
		regs: [Regex; 6],
	}

	pub struct Tokens<'r, 's> {
		rules: &'r Lexer,
		inp: &'s str,
		line: &'s str,
		lines: std::str::Split<'s, char>,
		lineno: usize,
		pos: usize,
		linepos: usize,
		src: &'s str,
	}

	impl Lexer {
		pub fn new() -> Self {
			let set = RegexSet::new([ rules::T_ANCHOR_id, rules::T_ANCHOR_mul, rules::T_ANCHOR_sum, rules::T_ANCHOR_ignore, rules::T_ANCHOR_int, rules::T_ANCHOR_error, ]).unwrap();
			let regs = [ Regex::new(rules::T_id).unwrap(), Regex::new(rules::T_mul).unwrap(), Regex::new(rules::T_sum).unwrap(), Regex::new(rules::T_ignore).unwrap(), Regex::new(rules::T_int).unwrap(), Regex::new(rules::T_error).unwrap(), ];
			Self { set, regs }
		}

		pub fn lex<'r, 's>(&'r self, inp: &'s str) -> Tokens<'r, 's> {
			Tokens::new(self, inp)
		}
	}

	impl<'r, 's> Tokens<'r, 's> {

		fn new(rules: &'r Lexer, inp: &'s str) -> Self {
			let mut lines = inp.split('\n');
			let line = lines.next().unwrap();
			Self {
				rules,
				inp,
				line,
				lines,
				lineno: 1,
				pos: 0,
				linepos: 0,
				src: inp,
			}
		}

		fn get_next(&mut self) -> Result<Option<Token<'s>>, Error> {
			if self.inp == "" {
				return Ok(None);
			};
			let (match_num, reg_match) = self
				.get_match()
				.ok_or_else(|| self.unrecognized_input())?;
			let src = self.src;
			let pos = self.pos;
			self.update_pos(reg_match.end());
			let end = self.pos;
			match match_num {
				rules::IGNORE_INDEX => self.get_next(),
				rules::ERROR_INDEX => { let val = reg_match.as_str(); Err(Error::error_rule(val)) }
				n => {
					let next = Token::new(KIND_ARRAY[n].unwrap(), src, pos, end);
					debug_assert!(next.is_some());
					Ok(next)
				}
			}
		}

		fn get_match(&self) -> Option<(usize, Match<'s>)> {
			self.rules.set
				.matches(self.inp)
				.iter()
				.next()
				.map(|n|
					(n, self.rules.regs[n].find(self.inp).unwrap())
				)
		}

		fn find_closest_match(&self) -> Option<usize> {
			self.rules.regs
				.iter()
				.filter_map(|r| r.find(self.inp))
				.map(|m| m.start())
				.min()
		}

		fn unrecognized_input(&self) -> Error {
			let end = self.find_closest_match().unwrap_or(self.inp.len());
			Error::unrecognised_input(&self.inp[0..end])
		}

		fn line_len(&self) -> usize {
			self.line.len() + 1
		}

		fn update_linepos(&mut self) {
			self.linepos += self.line_len();
		}

		pub fn colno(&self) -> usize {
			self.pos - self.linepos
		}

		fn next_line(&mut self) {
			self.line = self.lines.next().unwrap();
			self.lineno += 1;
		}

		fn update_line(&mut self) {
			if self.colno() > self.line_len() {
				self.update_linepos();
				self.next_line();
				self.update_line();
			}
		}

		fn update_pos(&mut self, new_pos: usize) {
			self.pos += new_pos;
			self.update_line();
			self.inp = &self.inp[new_pos..];
		}

		pub fn line(&self) -> &str {
			self.line
		}

		pub fn lineno(&self) -> usize {
			self.lineno
		}

		pub fn pos(&self) -> usize {
			self.pos
		}

		pub fn current_err_data(&self) -> lex::rly_common::ErrorData {
			<Self as lex::Tokens<'s, TokenKind>>::current_err_data(self)
		}
	}

	impl<'r, 's> Iterator for Tokens<'r, 's> {
		type Item = Result<Token<'s>, Error>;

		fn next(&mut self) -> Option<Self::Item> {
			self.get_next().transpose()
		}
	}

	impl<'r, 's> lex::Tokens<'s, TokenKind> for Tokens<'r, 's> {
		fn line(&self) -> &str {
			Tokens::line(self)
		}

		fn lineno(&self) -> usize {
			Tokens::lineno(self)
		}

		fn colno(&self) -> usize {
			Tokens::colno(self)
		}

		fn pos(&self) -> usize {
			Tokens::pos(self)
		}
	}

	impl<'r, 's> lex::IntoTokens<'s, TokenKind> for &'r Lexer {
		type Tokens = Tokens<'r, 's>;

		fn lex(self, inp: &'s str) -> Self::Tokens {
			Lexer::lex(self, inp)
		}
	}

	impl lex::Lexer<TokenKind> for Lexer {
		fn new() -> Self {
			Lexer::new()
		}
	}
}
