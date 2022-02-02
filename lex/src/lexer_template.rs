compile_error!("This is just a template file and shouldn't be compiled");

#[allow(nonstandard_style, dead_code)]
mod lexer {{
	use lex::{{
		regex::{{
			RegexSet,
			Regex,
			Match,
		}},
		Error,
	}};

	mod rules {{
{token_rules}{ignore_index}{error_index}	}}

	#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
	pub enum TokenKind {{
	{token_variants}}}

	mod display {{
		use std::fmt::{{Display, Formatter, Result}};
		use super::TokenKind;

		impl Display for TokenKind {{
			fn fmt(&self, f: &mut Formatter<'_>) -> Result {{
				match self {{
				{token_display}}}
			}}
		}}
	}}

	const KIND_ARRAY: [Option<TokenKind>; {rules_len}] = [{kind_array_elements} ];

	pub type Token<'a> = lex::Token<'a, TokenKind>;

	pub struct Lexer {{
		set: RegexSet,
		regs: [Regex; {rules_len}],
	}}

	pub struct Tokens<'r, 's> {{
		rules: &'r Lexer,
		inp: &'s str,
		line: &'s str,
		lines: std::str::Split<'s, char>,
		lineno: usize,
		pos: usize,
		linepos: usize,
		src: &'s str,
	}}

	impl Lexer {{
		pub fn new() -> Self {{
			let set = RegexSet::new([{lexer_rules} ]).unwrap();
			let regs = [{lexer_regs} ];
			Self {{ set, regs }}
		}}

		pub fn lex<'r, 's>(&'r self, inp: &'s str) -> Tokens<'r, 's> {{
			Tokens::new(self, inp)
		}}
	}}

	impl<'r, 's> Tokens<'r, 's> {{

		fn new(rules: &'r Lexer, inp: &'s str) -> Self {{
			let mut lines = inp.split('\n');
			let line = lines.next().unwrap();
			Self {{
				rules,
				inp,
				line,
				lines,
				lineno: 1,
				pos: 0,
				linepos: 0,
				src: inp,
			}}
		}}

		fn get_next(&mut self) -> Result<Option<Token<'s>>, Error> {{
			if self.inp == "" {{
				return Ok(None);
			}};
			let (match_num, reg_match) = self
				.get_match()
				.ok_or_else(|| self.unrecognized_input())?;
			let src = self.src;
			let pos = self.pos;
			self.update_pos(reg_match.end());
			let end = self.pos;
			match match_num {{
{ignore_case}{error_case}				n => {{
					let next = Token::new(KIND_ARRAY[n].unwrap(), src, pos, end);
					debug_assert!(next.is_some());
					Ok(next)
				}}
			}}
		}}

		fn get_match(&self) -> Option<(usize, Match<'s>)> {{
			self.rules.set
				.matches(self.inp)
				.iter()
				.next()
				.map(|n|
					(n, self.rules.regs[n].find(self.inp).unwrap())
				)
		}}

		fn find_closest_match(&self) -> Option<usize> {{
			self.rules.regs
				.iter()
				.filter_map(|r| r.find(self.inp))
				.map(|m| m.start())
				.min()
		}}

		fn unrecognized_input(&self) -> Error {{
			let end = self.find_closest_match().unwrap_or(self.inp.len());
			Error::unrecognised_input(&self.inp[0..end])
		}}

		fn line_len(&self) -> usize {{
			self.line.len() + 1
		}}

		fn update_linepos(&mut self) {{
			self.linepos += self.line_len();
		}}

		pub fn colno(&self) -> usize {{
			self.pos - self.linepos
		}}

		fn next_line(&mut self) {{
			self.line = self.lines.next().unwrap();
			self.lineno += 1;
		}}

		fn update_line(&mut self) {{
			if self.colno() > self.line_len() {{
				self.update_linepos();
				self.next_line();
				self.update_line();
			}}
		}}

		fn update_pos(&mut self, new_pos: usize) {{
			self.pos += new_pos;
			self.update_line();
			self.inp = &self.inp[new_pos..];
		}}

		pub fn line(&self) -> &str {{
			self.line
		}}

		pub fn lineno(&self) -> usize {{
			self.lineno
		}}

		pub fn pos(&self) -> usize {{
			self.pos
		}}

		pub fn current_err_data(&self) -> lex::rly_common::ErrorData {{
			<Self as lex::Tokens<'s, TokenKind>>::current_err_data(self)
		}}
	}}

	impl<'r, 's> Iterator for Tokens<'r, 's> {{
		type Item = Result<Token<'s>, Error>;

		fn next(&mut self) -> Option<Self::Item> {{
			self.get_next().transpose()
		}}
	}}

	impl<'r, 's> lex::Tokens<'s, TokenKind> for Tokens<'r, 's> {{
		fn line(&self) -> &str {{
			Tokens::line(self)
		}}

		fn lineno(&self) -> usize {{
			Tokens::lineno(self)
		}}

		fn colno(&self) -> usize {{
			Tokens::colno(self)
		}}

		fn pos(&self) -> usize {{
			Tokens::pos(self)
		}}
	}}

	impl<'r, 's> lex::IntoTokens<'s, TokenKind> for &'r Lexer {{
		type Tokens = Tokens<'r, 's>;

		fn lex(self, inp: &'s str) -> Self::Tokens {{
			Lexer::lex(self, inp)
		}}
	}}

	impl lex::Lexer<TokenKind> for Lexer {{
		fn new() -> Self {{
			Lexer::new()
		}}
	}}
}}
