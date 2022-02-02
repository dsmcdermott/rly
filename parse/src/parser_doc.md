This crate contains items for generating [LR(1) parsers][wp] which can recognise and
parse languages into [concrete syntax trees][wc] (also called "parse trees"), which
can then be transformed into [abstract syntax trees][wa] for processing, such as with
a compiler or interpreter.

This is done by parsing a source [`str`] containing a specification of a grammar and
and then generating a table of states for an LR(1) parser (as a finite state
automaton) for that grammar. That table is then used to write out a module, in rust
source code, for a parser struct capable of parsing the desired language.

# Generating Parsers

## How Parsers are Created

If you just want to use a parser in your project, and don't care about the internals
of how it's generated, you can probably skip this section and just read the section on
[build scripts](crate#build-scripts).

The general process for creating parsers starts with a [`str`] containing a list of
grammar rules and parsing it into a [`Rules`] struct, which contains the abstract
representation of those rules as well other data needed to understand them.

A [`Rules`] struct is then used to create a [`ParserSpec`] which contains a
specification of a parser in the form of a set of states for a finite state automaton.
A [`ParserSpec`] can then be used to write out a module, in rust source code,
containing a type which can be used to parse the language in question.

The process for generating a [`ParserSpec`] from a [`Rules`] is somewhat involved, and
I won't go over it here except to say that, for the most part, it follows the standard
process for generating LR(1) states, which you can read more about [here][wt] and
[here][tp]. It deviates slightly from this process in using a "merge as you go"
strategy, where the program attempts to merge equivalent item sets as soon as
possible, based on the algorithm outlined [here][honalee] with minor changes.

The traditional implementation of an LR(K) parser involves modelling a finite state
automaton using a stack to store the states of the machine and the parsed fragments of
the source text, a data table describing the states of the machine, and an
interpretation loop which consults the table and the current input to decide what
action to take.

This crate, however, implements parsers using a ["recursive ascent"][wr] strategy,
where the states are implemented as actual functions, and the call stack itself is
used as the stack of states and parsed fragments.

The benefit of this is an improvement in performance similar to that going from
interpreted to compiled languages: By implementing the states as actual functions
which get compiled to machine code it eliminates the overhead of having an interpreter
loop and a seperate stack from the built-in call stack.[^performance]

[^performance]: A note of warning: An actual performance improvement is still
speculative. I haven't done any profiling to measure the performance impact, and there
are potential downsides to implementing it this way: Implementing each state as a
seperate function could cause excessive paging in and out of the instruction cache.

The downside to this is that it's more complicated to implement: More rust code has to
be generated and included for a parser, which makes it more difficult to document and
abstract over different parsers. This is somewhat mitigated by the trait [`Parser`],
which provides a common abstraction over the interfaces of the generated types.

## Discriminants

A note on discriminants: a "discriminant" type is the type used for the internal
representations of symbols by a [`Rules`] and [`ParserSpec`] when generating a parser.
Generally speaking, there are two different discriminant types to specify when
building a parser: the discriminant for non-terminal symbols (that is, the symbols
that can appear on the left-hand side a [production rule][pr]) and the discriminant
for terminal symbols. A discriminant type must implement [`Prim`], [`FromUsize`], and
[`IntoUsize`], and should be capable of avoiding collisions for the number of symbols
that it's required to differentiate.

If you're unsure what to use for a discriminant, [`u32`] is a good default, and is
also used by the [`build_parser!`] macro as the default type for both terminal and
non-terminal symbols.

## Build Scripts

The process of generating a parser for a crate can be automated using cargo's build-in
[build script functionality][bs]. This crate provides the [`ParserBuilder`] struct and
[`build_parser!`] macro to simplify this process. For example:

With [`ParserBuilder`].

```no_run
// in build.rs

use parse::{ParserError, ParserBuilder};

fn main() -> Result<(), ParserError> {
	let mut builder = ParserBuilder::new().unwrap();

	builder
		.with_name("my_parser")?
		.at_location("parser.y")?
		.build::<u32, u32>()?
		.set_rerun().unwrap();

	Ok(())
}
```

With [`build_parser!`].

```no_run
// in build.rs

use parse::ParserError;

fn main() -> Result<(), ParserError> {
	parse::build_parser!(name = "my_parser", location = "parser.y")?;

	Ok(())
}
```

Either way, this generates a [`ParserSpec`] and uses it to write a parser to the
current builds [`OUT_DIR`][od], and from there it can be included in your code. This
crate also contains a convenience macro called [`parser!`] to help with this:

```ignore
// in src/main.rs

parse::parser!("my_parser");

use parser::Parser;
```

# Parser Grammars

## Format

A grammar for a parser consists of a list of (non-empty) [production rules][pr] for a
[context-free grammar][cf], represented by a utf-8 encoded string. A production rule
takes the form:

```text
	Rule ::= Symbol '->' Symbol+ ';'
```

Where there is a single non-terminal symbol on the left-hand side, followed by `->`
(`U+002D` followed by `U+003E`) and a non-empty sequence of symbols, seperated by
whitespace, on the right-hand side, with a semi-colon `;` (`U+003B`) terminating the
rule. Whitespace is ignored except to seperate symbols.

Some examples:

```text
Expr -> Expr sum Fact;

Fact ->
	Fact
	mult
	Term
;

Fact->Term;
```

A symbol can be describied by the following regex:

```text
	[[:alpha:]]([0-9_[:alpha:]])*
```

Which matches at least one ASCII alphabetical character, followed by any combination
of digits `0` through `9`, underscores `_`, or ASCII alphabetical characters.

### "start" and "eof"

The symbols `start` and `eof` are special: `eof` is reserved and cannot be used as a
symbol, and the symbol `start` must occur exactly once, on the left-hand side of a
production rule.

## Semantics

The grammar rules define the structure of the syntax trees used by the parser and how
the parser attempts to parse the input.

The grammar, or production rules can be seen as a kind of [rewrite rule][wr], where
the symbol on the left-hand side can be replaced with the sequence of symbols on the
right-hand side.

Given an input sequence of terminal symbols (paired with their original values,) the
parser attempts to generate a _derivation history_ for the sequence which describes
how to generate that sequence by starting with the [`start`](crate#start-and-eof)
symbol, and recurively applying production rules untill the appropriate sequence of
non-terminals is produced.

The parser does this by essentially working backwards from the terminals, recursively
using the production rule to reduce sequences of symbols into non-terminal symbols. As
it does this, it builds trees out of the reduced symbols, label each non-leaf node by
the left-hand side of the production rule that was used to make it.

### Grammar Example

Suppose you have the following grammar:

```text
start -> Sum;
Sum -> Fact;
Sum -> Sum plus Fact;
Fact -> int;
Fact -> Fact mult int;
```

With non-terminals `start`, `Sum`, and `Fact`, and terminals `plus` `mult` and `int`.

And suppose you have the following input:

```text
5 + 4 * 3 + 2
```

This would first be lexed by a [lexer](::lex::Lexer), producing the following sequence
of tokens:

```text
int("5") plus("+") int("4") mult("*") int("3") plus("+") int("2")
```

The parser would parse this sequence by repeatedly applying production rules to group
symbols into syntax trees. Like so[^brevity]

[^brevity]: Source strings are removed for brevity, so `int` instead of `int("5")`,
for example. However, in an actual syntax tree generated by a parser that information
is still there and can be inspected.

```text
int plus int mult int plus int
Fact(int) plus int mult int plus int
Sum(Fact(int)) plus int mult int plus int
Sum(Fact(int)) plus Fact(int) mult int plus int
Sum(Fact(int)) plus Fact(Fact(int) mult int) plus int
Sum(Sum(Fact(int)) plus Fact(Fact(int) mult int)) plus int
Sum(Sum(Fact(int)) plus Fact(Fact(int) mult int)) plus Fact(int)
Sum(Sum(Sum(Fact(int)) plus Fact(Fact(int) mult int)) plus Fact(int))
start(Sum(Sum(Sum(Fact(int)) plus Fact(Fact(int) mult int)) plus Fact(int)))
```

This results in a tree which groups nodes according to the grammar rules given above.
For illustration:

```text
                       start
                         │
                        Sum
         ┌───────────────┴───────────────┬───────┐
        Sum                              │      Fact
 ┌───────┼───────────────┐               │       │
Sum      │              Fact             │       │
 │       │       ┌───────┼───────┐       │       │
Fact     │      Fact     │       │       │       │
 │       │       │       │       │       │       │
int     plus    int     mult    int     plus    int

 5       +       4       *       3       +       2
```

### Terminal and NonTerminal Symbols

Throughout this documentation, you may see refrences to "terminal" and "non-terminal"
symbols. A terminal symbol is a symbol in a [grammar specification](crate#format) that
does not appear on the left-hand side of a production rule, and is therefore
"terminal" in the sense that it cannot be rewritten any further by the production
rules. A non-terminal symbol is a symbol that _does_ appear on the left-hand side of a
production rule, and can therefore be replaced with another sequence of symbols
according to the rules of the grammar.

When parsing, the terminal symbols represent the types of concrete tokens to parse. In
the above example, these are `int`, for integer literals, `plus`, for `+`, and `mult`,
for `*`. When parsing, each instance of one of these symbols corresponds to a concrete
section of the text, such as bytes 0-1 ("`5`") for the first `int` or bytes 10-11
("`+`") for the second `plus`.

Non-terminal symbols, on the other hand, correspond to higher-order phrases,
represented as branch nodes in the syntax tree grouping together their constituent
elements. In the above example, the non-terminals are `Fact`, for multiplication

# Using Parsers

## Parser Structure

A parser is writen as a module in rust source code, containing the items used to parse
an input. This module assumes only that this crate (`parse`) is available as an
external crate and that there is a sister module `lexer` that contains an enum
`TokenKind`, representing the different possible [terminal symbols][term] (see
[below](crate#interfacing-with-parsers) for more information.)

The parser module contains five public items:

* A type alias `Token<'a>`, which is an alias for [`lex::Token<'a, TokenKind>`].

* An enum `NonTerm` which represents the [non-terminal symbols][term] of the grammar.
The variants of `NonTerm` are `N_<sym>` for each non-terminal [symbol](crate#format)
`<sym>` of the language. `NonTerm` implements [`Display`](std::fmt::Display),
[`Debug`](std::fmt::Debug), [`Copy`], [`Ord`], and [`Hash`].

* A struct `Ast<'a>` which implements [`ast::Ast`] with `NonTerm = NonTerm` and `Term
= Token<'a>`, using the types `NonTerm` and `Token` described above. `Ast`'s represent
branches in syntax trees, and are returned by `Parser`'s. An `Ast` contains a
[label](ast::Ast::label) in the form of a `NonTerm` variant, and a list of [child
nodes](ast::Ast::children) in the form of a vector of [`AstNode`](ast::AstNode)'s.

* A struct `Parser<'a, L>`, which implements [`Parser<'a, L, TokenKind, Ast<'a>>`]
where `L` implements [`Tokens<'a, TokenKind>`][lex::Tokens], with `TokenKind` and
`Ast<'a>` as described above. `Parser` is, as you might guess, the type of the actual
parsers responsable for parsing an input stream into a syntax tree.

* A function `parse`, which is just a convenience function for [`Parser::new`]
followed by [`Parser::parse()`].

### A Note About Traits

The public interface of `Parser` is completely described by the trait [`Parser`]. This
allows you to access documentation on the generated parser types by looking at the
documentation for the associated trait as well as write more generic code.

However, `Parser` is also guarenteed to independently implement all of the methods of
the trait [`Parser`], __with no difference between the implementations__. This
effectivly means that actually importing [`Parser`] is optional for using this type.
In other words, for each method `foo` on the trait [`Parser`], the generated type
`Parser` will also implement `foo`, with `Parser::foo` and `<Parser as
parse::Parser>::foo` guaranteed to be equivalent.

## Interfacing with Lexers

Generally, a [`Parser`][ps] is incapable of directly parsing a [`str`]; it needs a
[lexer][wl] to "lex" or "tokenize" a string into [`Token`]'s, which contain a
sub-[`str`] of the source text as well as a [terminal symbol][term] indicating how the
token should be interpreted.

Parsers (both the [generated type][ps] and anything else that implements the
[`Parser`] trait) are designed to work with the lexing framework outlined and
implemented in this crate's sister package [`lex`](::lex).

To give a brief overview[^more_info]: A [`Lexer`](::lex::Lexer) takes an input [`str`]
and returns a [`Tokens`], which is an iterator over the (lazily lexed) tokens of the
input. The [`Parser`] trait takes a [`Tokens`] and uses it as the input stream for
parsing.

[^more_info]: For more information on the interfaces expected by a parser, view the
documentation on the trait [`Lexer`](::lex::Lexer). For more information on lexers
generally, and for tools for making lexers, see the crate [`lex`](::lex).

### TokenKind and Non-Terminal Symbols

As explained [above][term], a grammar contains terminal symbols for tokens, and
non-terminal symbols for higher phrases. To distinguish the non-terminal symbols, each
parser module contains an enumeration [`NonTerm`][ps], but to distinguish the terminal
symbols, particularly for use in [`Token`]'s, an additional type for that is needed as
well.

The only assumption made by a [parser module][ps] about its environment, aside from
having this crate available, is that there is a sister module called `lexer`,
containing an enumeration called `TokenKind`, whose variants are `T_<sym>` for each
terminal symbol `<sym>` of the language.

`TokenKind` is imported into the module and used as the type discriminant for
[`Token`]'s, (as returned by [`Token::kind`](lex::Token::kind).)

What this means, if you're using the crate `lex` to generate your lexer, is that you
should use the macro [`lexer!`](::lex::lexer) and the macro
[`parse::parser!`](parser!) in the same module so that the parser can use the
`TokenKind` defined in the lexer module.

Also, if your using `lex`, make sure that the names of your lexer rules and your
terminal symbols are the same!

## `Ast`'s

When a parser has successfully parsed its input, with [`parse()`](Parser::parse), it
returns an [`Ast`][ps], which represents the [syntax tree][wc] derived by the
parser[^naming].

[^naming]: The name "Ast" may be a little confusing, since the trees returned by
parsers are not _technically_ [abstract syntax trees][wa], due to them containing all
of their constituent tokens, even the semantically redundant ones (such as a `mult`
under a `Fact` node in the [example above](crate#grammar-example).) However, `Ast`'s
can be modified after they're created, and it's not a difficult process to convert one
to a proper abstract syntax tree.

For more information on the details of `Ast`'s, including how to recursively walk
them, see the documentation on the [`Ast`](ast::Ast) trait and the module [`ast`]. For
some more information on how they relate to the grammar of a language and how they're
built, see the [above example](crate#grammar-example).

# Example

This example uses the crate `lex` to build the lexer [used when parsing][lexers]. For
more information on lexers and how the `lex` crate works, you may wish to consult the
documentation there.

For this example, lets try to build a simple calculator that can handle addition,
multiplication, and grouping terms with parentheses, with the proper precedence.

We start by making a new project called "`calculator`" using `cargo new`, which would
give us the following directory structure:

``` text
calculator/
├── Cargo.toml
└── src/
    └── main.rs
```

Next, edit `Cargo.toml` to add the crate `lex` as well as this crate as a dependency
*and* a build dependency. It should look something like this:

``` text
[package]
name = "calculator"
version = "0.1.0"
edition = "2021"

[dependencies]
lex = "0.1.0"
parse = "0.1.0"

[build-dependencies]
lex = "0.1.0"
parse = "0.1.0"
```

Now we'll specify the lexer by adding our lexer file `calculator_lex.lex` and creating
a [build script][bs] in `build.rs`.

```text
## in calculator_lex.lex

int : "[0-9]+"
plus : "\+"
mult : "\*"
lparen : "\("
rparen : "\)"
ignore : "\s+"
```

```no_run
// in build.rs

use lex::LexerBuilder;

fn main() {
	LexerBuilder::new()
		.unwrap()
		.build()
		.expect("error generating lexer")
		.set_rerun()
		.unwrap();
}
```

At this point, we would trigger the build scrip by running `cargo check` or `cargo
run` to make sure that the lexer builds properly.

After having done that, the next step is to build the parser. This is done in a
similar mannar to building lexers, where we first write the parser specification file
"`calculator_parse.y`":

```text
start -> Sum;
Sum -> Fact;
Sum -> Sum plus Fact;
Fact -> Term;
Fact -> Fact mult Term;
Term -> int;
Term -> lparen Sum rparen;
```

and then we change `build.rs` to the following:

```no_run
// in build.rs

use lex::LexerBuilder;
use parse::ParserBuilder;

fn main() {
	LexerBuilder::new()
		.unwrap()
		.build()
		.expect("error generating lexer")
		.set_rerun()
		.unwrap();

	ParserBuilder::build_parser::<u32, u32>()
		.expect("error generating parser")
		.set_rerun()
		.unwrap();
}
```

At this point it's a good idea to run `cargo check` again to make sure that the parser
is building properly as well.

Now, although we have created a build script to build the lexer and parser, we still
need to include them in our project. To do so, we use the `lex::lexer!` and
[`parser!`] macros. edit `src/main.rs` to the following:

```ignore
// in src/main.rs

use std::io;

// include the lexer
lex::lexer!();

// include the parser
parse::parser!();

use lexer::Lexer;

fn main() {
	// our input buffer
	let mut buffer = String::new();
	let stdin = io::stdin();
	// our lexer
	let lexer = Lexer::new();
	loop {
		buffer.clear();
		stdin.read_line(&mut buffer).expect("unable to read input");
		// create our `Tokens`
		let tokens = lexer.lex(&buffer);
		// parse the input
		let tree = parser::parse(tokens).expect("unable to parse input");
		// print the tree
		println!("{}", tree.display());
	}
}
```

This runs a simple loop that reads a line from the standard input and uses the lexer
and parse to create an [`Ast`][ps]. It then prints a representation of the tree using
[`Ast::display`](ast::Ast::display). Try running the program with `cargo run` and
seeing how it parses things and how the resulting trees match the grammar above. Also
try seeing what happens when you give it an invalid input: It should cause an error.

Now, although we have a [`Parser`] that can parse our input into an [`Ast`][ps], we
still have to actually _do_ something with the tree: namely, to calculate the
corresponding value. The work of grouping expression in the correct order and deciding
what operation to perform on them has essentially been done by the parser, all we have
left to do is to traverse the tree, applying the operations as appropriate. The module
[`ast`] has some features for walking an [`Ast`](ast::Ast), and you can see [the
documentation there](ast#walking-an-ast) for more information, but in
short we implement the [`Walker`](ast::Walker) trait on a struct by describing three
methods: a method to be called upon entering a branch node
([`on_branch`](ast::Walker::on_branch)), a method to be called on leaf nodes
([`on_leaf`](ast::Walker::on_leaf)), and a method to be called upon exiting a branch
node ([`exit`](ast::Walker::exit).)

We do this by, essentially, creating a struct that keeps track of all the previously
calculated values of the current branch node and all ancestral branch nodes. When it
encounters a leaf node, if that node is an `int` it parses the value as a [`u32`] and
records it. When it leaves a branch node, it takes all the recorded values of the
child nodes of that branch node and combines them as appropriate (either adding them
for a `Sum` node or multiplying them for a `Fact` node) and records the result as the
value for that branch node under the previous branch node.

To implement this, edit `src/main.rs` to look like the following:

```ignore
// in src/main.rs

use std::io;

use parse::ast::{Ast, Walker};

//include the lexer
lex::lexer!();

use lexer::{Lexer, TokenKind, Tokens};

//include the parser
parse::parser!();

use parser::{NonTerm, Token};

fn main() {
	let mut buffer = String::new();
	let stdin = io::stdin();
	let lexer = Lexer::new();
	let mut calculator = Calculator::new();
	loop {
		buffer.clear();
		stdin.read_line(&mut buffer).expect("unable to read input");
		let tokens = lexer.lex(&buffer);
		let n = parse_input(tokens, &mut calculator);
		println!("{}", n);
	}
}

fn parse_input<'r, 's>(tokens: Tokens<'r, 's>, mut calculator: &mut Calculator) -> u32 {
	// parses the tree and handles any errors
	let tree = match parser::parse(tokens) {
		Ok(t) => t,
		Err(e) => panic!("unable to parse input: {}", e),
	};
	// walks the tree
	assert!(tree.walk(&mut calculator).next().is_none());
	// calculates the end result
	calculator.final_result()
}

// Our Walker for actually calculating the value of an Ast.
//
// stack is a list of the parsed values of the child nodes of each of the ancestral branch 
// nodes, as well as those of the current branch node which is the Vec on top of the 
// stack.
//
// When an 'int' leaf node is encountered, it's parsed as a u32 and pushed on to the 
// vector on the top of the stack. When a branch node is encountered, a new empty Vec is 
// made and pushed onto the stack.
//
// When a branch node is left, the top of the stack (the Vec corresponding to the child 
// nodes of that branch) is poped, and the Vec is then either summed, multiplied, or has 
// its single value poped, depending on if the branch node is a 'Sum', 'Fact', or 'Term' 
// respectively. The result is then pushed onto the end of the new Vec on top of the 
// stack.
//
// After the tree has been walked, the stack consists of a single Vec representing the 
// child nodes of the top-level 'start' node, which should itself consist of a single 
// element representing the single child 'Sum' node. final_result can then be run to 
// extract that value and return the calculator to a fresh state.
struct Calculator {
	stack: Vec<Vec<u32>>,
}

impl Calculator {
	fn new() -> Self {
		Self { stack: vec![Vec::new()] }
	}

	// pushes 'n' onto the end of the Vec on top of self.stack
	fn push(&mut self, n: u32) {
		self.stack.last_mut().unwrap().push(n)
	}

	// pops the top Vec of off self.stack
	fn pop(&mut self) -> Vec<u32> {
		self.stack.pop().unwrap()
	}

	// resets self to a fresh state and returns the final result of walking a tree.
	fn final_result(&mut self) -> u32 {
		assert_eq!(self.stack.len(), 1);
		let mut summands = self.pop();
		self.stack.push(Vec::new());
		assert_eq!(summands.len(), 1);
		summands.pop().unwrap()
	}
}

impl<'a, 's> Walker<'a, NonTerm, Token<'s>, ()> for Calculator {
	// pushes a new Vec onto self.stack for the child nodes of '_tree'
	fn on_branch(&mut self, _tree: &'a Ast<NonTerm, Token<'s>>) -> (Option<()>, bool) {
		self.stack.push(Vec::new());
		(None, true)
	}

	// if leaf is an 'int', parses the underlying str as a u32 and pushes it
	fn on_leaf(&mut self, leaf: &'a Token<'s>) -> Option<()> {
		if *leaf.kind() != TokenKind::T_int {
			return None;
		};
		let n = leaf.val().parse().unwrap();
		self.push(n);
		None
	}

	// pops the top off off self.stack, combines the values as appropriate, and then 
	// pushes the result
	fn exit(&mut self, tree: &'a Ast<NonTerm, Token<'s>>) -> Option<()> {
		let mut operands = self.pop();
		let n = match tree.label() {
			NonTerm::N_Sum => operands.into_iter().sum(),
			NonTerm::N_Fact => operands.into_iter().product(),
			NonTerm::N_Term => {
				assert_eq!(operands.len(), 1);
				operands.pop().unwrap()
			}
			NonTerm::N_start => unreachable!(),
		};
		self.push(n);
		None
	}
}
```

Try testing it out by running `cargo run` and seeing how it works!

[wp]: https://en.wikipedia.org/wiki/LR_parser
[wc]: https://en.wikipedia.org/wiki/Parse_tree
[wa]: https://en.wikipedia.org/wiki/Abstract_syntax_tree
[wt]: https://en.wikipedia.org/wiki/Canonical_LR_parser#Constructing_LR(1)_parsing_tables
[tp]: http://david.tribble.com/text/lrk_parsing.html
[honalee]: http://david.tribble.com/text/honalee.html
[wr]: https://en.wikipedia.org/wiki/Recursive_ascent_parser
[bs]: https://doc.rust-lang.org/cargo/reference/build-scripts.html
[od]: https://doc.rust-lang.org/stable/cargo/reference/environment-variables.html#environment-variables-cargo-sets-for-build-scripts
[pr]: https://en.wikipedia.org/wiki/Production_(computer_science)
[cf]: https://en.wikipedia.org/wiki/Context-free_grammar
[rw]: https://en.wikipedia.org/wiki/Rewrite_rule
[term]: crate#terminal-and-non-terminal-symbols
[ps]: crate#parser-stucture
[wl]: https://en.wikipedia.org/wiki/Lexer
[`Tokens`]: lex::Tokens
[`Token`]: lex::Token
[lexers]: crate#interfacing-with-lexers
