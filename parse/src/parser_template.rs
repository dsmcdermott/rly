compile_error!("This is just a template page and should not be compiled");


#[allow(nonstandard_style, dead_code, unreachable_patterns)]
#[allow(clippy::all)]
mod parser {{
	//{non_term_vals}
	//{term_vals}

	use parse::lex::{{self, Tokens}};
	use parse::{{
		SyntaxError,
		Error,
		Parser as ParserTrait,
		ast::{{self, AstNode, reverse}},
	}};

	{token_kind}

	pub type Token<'a> = lex::Token<'a, TokenKind>;

	#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
	pub enum NonTerm {{
	{non_terms}}}

	mod display {{
		use std::fmt::{{Display, Formatter, Result}};
		use super::NonTerm;

		impl Display for NonTerm {{
			fn fmt(&self, f: &mut Formatter) -> Result {{
				let name = match self {{
				{names}}};
				write!(f, "{{}}", name)
			}}
		}}
	}}

	const START: NonTerm = NonTerm::{start};

	pub type Ast<'a> = ast::Ast<NonTerm, Token<'a>>;

	type Result<T> = std::result::Result<T, Error>;

	type Res<'a> = Result<(Ast<'a>, usize)>;

	fn ret<'a>(label: NonTerm, children: AstNode<NonTerm, Token<'a>>, n: usize) -> Res<'a> {{
		Ok((Ast::new(label, vec![children]), n))
	}}

	fn goto_err<'a>() -> Res<'a> {{
		panic!("Unexpected error in parsing")
	}}

	pub struct Parser<'a, L> {{
		inp: L,
		la: Option<Token<'a>>,
	}}

	impl<'a, L> Parser<'a, L> {{
		fn la(&self) -> &Option<Token<'a>> {{
			&self.la
		}}

		fn kind(&self) -> Option<TokenKind> {{
			match self.la() {{
				Some(tok) => Some(*tok.kind()),
				None => None,
			}}
		}}
	}}

	impl<'a, L> Parser<'a, L>
	where
		L: Tokens<'a, TokenKind>,
	{{

		fn err_token(&self, tok: &Token<'a>) -> SyntaxError {{
			let data = tok.get_error_data();
			SyntaxError::unexpected_token(tok.val(), data)
		}}

		fn err_eof(&self) -> SyntaxError {{
			let data = self.inp.current_err_data();
			SyntaxError::unexpected_eof(data)
		}}

		fn err(&self) -> SyntaxError {{
			match self.la() {{
				Some(tok) => self.err_token(tok),
				None => self.err_eof(),
			}}
		}}

		fn shift(&mut self) -> Result<Option<Token<'a>>> {{
			let la = self.la;
			self.la = self.inp.next().transpose()?;
			Ok(la)
		}}{states}
	}}

	impl<'a, L> Parser<'a, L>
	where
		L: Tokens<'a, TokenKind>,
	{{
		pub fn new<I>(inp: I) -> Result<Self>
		where
			I: IntoIterator<IntoIter = L>,
		{{
			let mut inp = inp.into_iter();
			let la = inp.next().transpose()?;
			Ok(Self {{
				inp,
				la,
			}})
		}}

		pub fn parse(&mut self) -> Result<Ast<'a>> {{
			let mut tree = self.s0()?;
			reverse(&mut tree);
			Ok(tree)
		}}
	}}

	impl<'a, L> ParserTrait<'a, L, TokenKind, NonTerm, Token<'a>> for Parser<'a, L>
	where
		L: Tokens<'a, TokenKind>,
	{{
		fn new<I>(inp: I) -> Result<Self>
		where
			I: IntoIterator<IntoIter = L>,
		{{
			Parser::new(inp)
		}}

		fn parse(&mut self) -> Result<Ast<'a>> {{
			Parser::parse(self)
		}}
	}}

	pub fn parse<'a, L, I>(iter: I) -> Result<Ast<'a>>
	where
		L: Tokens<'a, TokenKind>,
		I: IntoIterator<IntoIter = L>,
	{{
		Parser::new(iter)?.parse()
	}}

}}
