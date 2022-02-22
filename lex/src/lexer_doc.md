This crate contains facilities for generating [lexers][wl] which can parse or lex input
into [`Token`]'s.

Creating [lexers](Lexer) can be done using either the [`LexerWriter`] struct:

```
use lex::LexerWriter;

let mut buffer = Vec::new();

let rules = r#"
id : "[a-zA-Z_][0-9a-zA-Z_]*"
ignore : "[[:space:]]+"
int : "[0-9]+"
error : "/""#;

let writer = LexerWriter::from_str(rules).unwrap();

writer.write(&mut buffer).unwrap();

let lexer_text = String::from_utf8(buffer).unwrap();
```

the [`write_from_str`] or [`write_from_reader`] functions:

```
let mut buffer = Vec::new();

let rules = r#"
id : "[a-zA-Z_][0-9a-zA-Z_]*"
ignore : "[[:space:]]+"
int : "[0-9]+"
error : "/""#;

lex::write_from_str(rules, &mut buffer).unwrap();

let lexer_text = String::from_utf8(buffer).unwrap();
```

or using the [`LexerBuilder`]struct or [`build_lexer`] function inside a [build
script][bs] (this is most likely what you want):

``` no_run
// in build.rs
use lex::{LexerBuilder, LexerBuilderError};

fn main() -> Result <(), LexerBuilderError> {
	let mut builder = LexerBuilder::new().unwrap();
	builder
		.with_name("my_lexer")?
		.build()?;
	Ok(())
}
```

All three methods ultimately use [`LexerWriter`], which is created using
[`from_str`](LexerWriter::from_str) to parse a source string, and which contains the data
necessary to write a lexer module. The other two methods are essentially just convinience
wrappers around [`LexerWriter::from_str`] and [`LexerWriter::write`].

When using the [`LexerBuilder`] struct, the resulting lexer can be included using the
macro [`lexer`]. For example:

In `build.rs`

``` no_run
// in build.rs
use lex::{LexerBuilder, LexerBuilderError};

fn main() -> Result <(), LexerBuilderError> {
	let mut builder = LexerBuilder::new().unwrap();
	builder
		.with_name("my_lexer")?
		.build()?;
	Ok(())
}
```

In `src/lib.rs`

``` ignore
lex::lexer!("my_lexer");
use lexer::LexerRules;

//
//

let rules = LexerRules::new();

let tokens = rules::lex(src);
```

# Lexers

## About

[Lexers][wl] (also called "tokenizers",) are, generally speaking, components that can scan
a text and "tokenize" it or brake it up into "tokens", which are the basic, discreet units
used to analyze the text. For example, in the following line of Rust code:

```
let x = 5 + 4;
```

the tokens would be: `let`, `x`, `=`, `5`, `+`, `4`, and `;` (there are also spaces
inbetween these tokens, but these are [ignored][ei] by the compiler.) These tokens are
also categorized in a way that the compiler understand (namely `KW_LET`, `IDENTIFIER`,
`Eq`, `INTEGER_LITERAL`, `Plus`, `INTEGER_LITERAL`, and `Semi` respectively) and may also
carry around data about their location in the source for error messages.[^rust_tok]

[^rust_tok]: See the
[reference](https://doc.rust-lang.org/stable/reference/lexical-structure.html) for more
details on how Rust in particular handles tokens.

This crate contains code for automatically generating Rust source code for lexers, as well
as the dependencies used by them. Once generated, these lexers can be included and used in
any package that has this crate as a dependency. This process can be automated using
[build scripts][bs] with cargo, with the helper struct [`LexerBuilder`] and macro
[`lexer!`].

## Lexer Structure

These lexers are written as module named `lexer` containing 4 public items. These are:

* An enum called `TokenKind`, whose variants are constants of the form `<name>` for each
[token rule](crate#rules) except for [`ignore` and `error`][ei] (if present,) and acts as
the discriminant for [`Token`]'s returned by the lexer. `TokenKind` implements
[`Debug`](std::fmt::Debug), [`Clone`], [`Copy`], [`PartialEq`], [`Eq`], [`PartialOrd`],
[`Ord`], and [`Hash`](std::hash::Hash). It also implements [`Display`](std::fmt::Display),
with the displayed value for a variant being "`<name>`".

* A type alias `Token<'a>` which is an alias for [`Token<'a, TokenKind>`], the type of
tokens parsed by the lexer. [See there] for more details.

* A struct `Lexer`, which is the type of lexers created for the modules. `Lexer`
implements two methods described in the trait [`Lexer`]: [`new`](Lexer::new), which
creates a new instance of a `Lexer`, containing all the rules and data necessary for
lexing an input, and [`lex`](IntoTokens::lex), which creates an instance of `Tokens`,
which iterates over the lazily parsed `Token`'s of a given input.

* And finaly, a struct called `Tokens<'r, 's>`, where `'r` is the lifetime of the `Lexer`
that spawned it (see above), and `'s` is the lifetime of its input text. `Tokens<'_, 's>`
implements the [`Tokens<'s, TokenKind>`] trait with `TokenKind` (see above) being the
discriminant. This means in particular that `Tokens` is an [Iterator] over the lazily
parsed tokens of its input, with the [item](Iterator::Item) type being [`Result<Token<'_>,
Error>`]; returning an [`Err`] when the [error rule][ei] is triggered, or when
encountering an unmatchable string, and returning [`Ok(token)`] otherwise.

The public interfaces of both `Lexer` and `Tokens` are completely described by the
corresponding traits [`Lexer`] and [`Tokens`], respectively. However, both types are
guarenteed to seperately implement all off the methods of their respective traits, **with
no difference between the two implementation**. In particular the type `Lexer` implements
`lex` as a method of type `<'r, 's>(&'r self, inp: &'s str) -> Tokens<'r, 's>`. This means
that the interfaces for these types can be used without having to import the associated
traits. For example:

``` ignore
lex::lexer!();

use lexer::Lexer;

let first_lexer = Lexer::new();

let identical_lexer = <Lexer as lex::Lexer<_>>::new();	// same as 'first_lexer';
```

Note that the `#[allow(unused_code)]` attribute is set for the generated module, so
compiler warnings wont be generated for not using any of the items, just like with an
external crate. For example, in the above example the items `Error`, `Token`, and `Tokens`
are not used, but no warning would be generated.

# Lexer Definitions

## Rules

Lexer definitions are utf-8 formatted strings (such as rust's [str] and [String]) that
define a list of rules for parsing tokens (see [below](crate#syntax) for the syntax.) Each
rule defines a *name* and a *regex*, where the *name* introduces a new category of tokens
to recognize, and *regex* is a non-empty-matching regex that describes how to identify the
category of token. For example, the following line introduced a rule with name "`ident`"
and with regex "`\[a-zA-Z\]+\[_a-zA-Z0-9\]*`":

``` text
ident : "[a-zA-Z]+[_a-zA-Z0-9]*"
```

Again, see [below](crate#syntax) for details about the syntax. This means that when the
generated lexer (or, more accurately, an instance of [`Tokens`](crate#lexer-structure)
spawned by an instance of the generated [`Lexer`](crate#lexer-structure) type) is parsing
an input string, and the regex "`\[a-bA-B\]+\[_a-bA-B0-9\]*`" matches the begining of the
unparsed portion, the matching text gets parsed and returned as an "`ident`" token (see
[above](crate#lexer-structure) and [`Token`].) The exceptions to this are rules with the
name "`error`" or "`ignore`" (see [below][ei].)

If no rules can be matched to the begining of the unparsed input, then the lexer returns
an [`Error`].

Note that the order in which the rules are defined *does* matter: if multiple rules match
the begining of the unparsed portion of the input, then the first defined rule matches.
This may cause unexpected problems where an input is valid when parsed one way, but
invalid when parsed another. For example, suppose you have a lexer with two rules:

``` text
foo : "abc"
bar : "abc.*def"
```

And suppose you tried to lex the following input:

``` text
abc def
```

This whole string would match "`bar`", but since "`foo`" is defined first it instead
matches "`abc`" to `foo`, and then raises an error for "` def`", since neither "`foo`" nor
"`bar`" matches "` def`".

Rules also cannot be defined twice: that is, no two rules can have the same name.

## `error` and `ignore`

Rules with the [name](crate#rules) "`error`" or "`ignore`" behave differently from normal
rules: rather than of defining a type of token and describing how to recognize it, they
insted trigger special behaviour by the lexer when ther [regexes](crate#rules) match.

When the `error` rule is matched, instead of returning a token, the lexer returns an
[`Error`] with [kind](ErrorKind) [`ErrorRule`](ErrorKind::ErrorRule) and with the
offending text as the [`val`](Error::val). When the `ignore` rule is matched, instead of
returning anything, the lexer simply skips over the matched text.

Note that, just as with normal rules, the order in which `error` and/or `ignore` are
defined relatve to the other rules matters for matching. For example, suppose you have a
lexer with the following rules:

``` text
foo : "abc"
bar : "def"
error : "abc def"
ignore : "[[:space:]]+"
```

And suppose it's trying to lex the following input:

``` text
abc def
```

This would return the tokens "`foo(abc)`" and "`bar(def)`" without error, despite the fact
that `error` matches the whole text, because `foo` is defined before `error`; it would
first match `foo` against "`abc`", then `ignore` against "` `", and then `bar` against
"`def`".

## Syntax

### Rule Syntax

As decribed [above](crate#rules), a lexer definition is a utf-8 string defining a list of
rules to use when lexing. Rules are seperated by newlines ('\n' `U+000A`) and empty lines
are ignored. The general syntax for a rule is as follows:

``` text
rule ::= name | divider | regex			(no newlines)
name ::= [[:alpha:]][_0-9[:alpha:]]*	(except 'crate', 'self', 'super', and 'Self')
divider ::= [[:space:]]:[[:space:]]
regex ::= ".+"
```

Whitespace between the components of a `rule` is generally ignored, with the exception of
`divider`'s which, as noted above, must have at least one whitespace character between it
and the `name` and `regex`, and with the exception that newlines (`U+000A`) cannot occur
within a rule.

A `rule` consists of a [`name`](crate#rules), a `divider` ('`:`'), and a
[`regex`](crate#rules). A `name` must start with an ASCII alphabetical character
(`[a-zA-Z]`) followed by any sequence of ASCII alphabetical characters, underscores
('`_`'), or digits (`[0-9]`). For example

``` text
Foo : "\W(Foo)+\W"

f_0O : "(?P<interpunct>\u00B7)(?P<word>\w+)"

trailing_whitespace : "((?m)\s+$)"
```

The only exceptions to this are the terms "`crate`", "`self`", "`super`", and "`Self`",
which cannot be used as `name`'s. This is due to restrictions rust places on its own
identifiers and how the generated [lexers](crate#lexer-structure) are implemented.

A `divider` is the character '`:`' (`U+003A`) with at least one (non-newline) whitespace
character between it and the `name`, and between it and the `regex`

A `regex` is a [regular expression](https://en.wikipedia.org/wiki/Regular_expression)
introduced by a '`"`' (`U+0022`) and ended by another '`"`'. `"`'s within a `regex` do not
need to be escaped (and in fact, trying to escape them will raise an
[error](::regex::Error) as a non-recognized escape sequence,) but no non-whitespace
characters can occur after the final '`"`'. For example, in the following definition:

``` text
quote : "("\w*")|('\w*')"
```

the rule `quote` matches any word surrounded by '`"`', or by '`'`', with the two `"`'s
appearing between the initial '`"`' and the final '`"`' being interpreted as literal
'`"`''s.

`regex`'s are parsed according to the crate [`regex`](::regex) (with one
exception[^exception],) using the same default flags, and must be valid regular
expressions according to the [rules of that crate](::regex#syntax). For example, the rule:

``` text
space_no_nl : "[[:space:]&&[^\n]]"
```

would be valid and would match any sing ASCII whitespace character except for '`\n`',
while the rule:

``` text compile_fail
start_with_a_invalid : "a(*)"
```

would be invalid since the repition operator `*` is unescaped and lacks an expression to
operate on.

See the [documentation on the crate `regex`](::regex#syntax) for more info.

[^exception]: The one exception is that an anchor '`^`' always matches the begining of the
unparsed input (as well as the beginings of lines if [the `m` flag is
set](#grouping-and-flags).) For example the regex "`^abc`" would behave almost exactly
like the regex "`abc`", the one exception to *that* being error messages, where, upon
encountering a section of text that cannot be matched, the lexer will search ahead to find
the nearest matching text in order to define the range of text that cannot be matched.
When this happens, anchors in regexes currently still match against the begining the
remaining text, including the unmachable portion. So, for example, if you were to have two
lexers, each with a single rule, with regexes "`^abc`" and "`abc`" respectively, both
would behave the same on the input "`abcabc`", returning two tokens with the content
"`abc`". But, on the string "`abcdefabc`", while both lexers would retrun a token with
"`abc`", and both lexers would then return an error, in that error the second lexer would
report the string "`def`" (up to the begining of "`abc`" in "`defabc`") as being
unparsable, while the first would report the string "`defabc`" as being unparsable (since
"`^abc`" doesn't match anywhere in "`defabc`",) returning a less precise error message.
This might be fixed later.

#### Escapes

Note that, because the utf-8 text is used directly to create a [`Regex`](crate::Regex),
when writing a `.lex` source file with a text editor the result is equivalent to calling
[`Regex::new`] on the `regex` interpreted as a rust [raw string
literal](https://doc.rust-lang.org/reference/tokens.html#raw-string-literals) (with an `r`
before the string, followed by as many `#`' as necessary.) For example, the rule:

``` text
name : "\w+"
```

matches any non-empty sequence of unicode word characters, but if you were to try the
following in rust:

``` compile_fail
# //use lex::regex;
use regex::Regex;

fn main() {
	let name = Regex::new("\w+").unwrap();
}
```

you would get the following error:

``` text
error: unknown character escape: `w`
 --> src/main.rs:4:26
  |
4 |     let name = Regex::new("\w+").unwrap();
  |                             ^ unknown character escape
  |
  = help: for more information, visit <https://static.rust-lang.org/doc/master/reference.html#literals>
```

because the sequence "`\w`" would be parsed as an escape sequence at the level of the rust
source code, which would trigger an error since "`\w`" is not a valid [escape
sequence](https://doc.rust-lang.org/reference/tokens.html#character-escapes) in rust.
However, if we were to instead use one of the following examples:

```
# //use lex::regex;
use regex::Regex;

let name = Regex::new(r"\w+").unwrap();

let equivalent_name = Regex::new("\\w+").unwrap();

assert_eq!(name.as_str(), equivalent_name.as_str());
```

it would work fine, since, with either option, a string consisting of the characters
'`\`', '`w`', and '`+`' would be sent to [`Regex::new`](::regex::Regex::new), and so the
sequence "`\w`" would get processed on the level of the regex (specifically [as a
character class matching unicode word
characters](::regex#perl-character-classes-unicode-friendly).) However, if were to use the
second option, "`\\w+`", for our rule instead:

``` text
incorect_word : "\\w+"
```

This would be the equivalent of:

```
# //use lex::regex;
use regex::Regex;
Regex::new(r"\\w+").unwrap();
```

which would match a literal '`\`', followed by a non-empty sequence of `w`'s!

### Coments

Comments can also be used with lexer definitions: A line that has `#` (`U+0023`) as its
first non-space character is interpreted as a comment and is ignored. For example:

``` text
## this is a lexer definition file

## this rule is for identifiers
id : "[[:alpha:]][_0-9[:alpha:]]*"

## this is for integer literals
int : "[0-9]+"

## multiplication and addition
mult : "\*"
plus : "\+"

## this line is a comment explaning that the following line is a rule for identifying comments
comment : "[[:space:]]*#.*$"
```

# Example

Suppose you want to build a simple calculator that can handle addition and subtraction on
integers, as well as understand decimal, hexadecimal, octal, and binary integers in the
same format as [rust integer literals][il] (without underscores, for simplicity.) We would
start by making a new project "`calculator`" with `cargo new`, which would give us
something like the following directory structure:

``` text
calculator/
├── Cargo.toml
└── src/
    └── main.rs
```

Next, edit `Cargo.toml` to add this crate as a dependency *and* a build dependency. It
should look something like this:

``` text
[package]
name = "calculator"
version = "0.1.0"
edition = "2021"

[dependencies]
lex = { version = "0.1.0", git = "https://github.com/dsmcdermott/rly" }

[build-dependencies]
lex = { version = "0.1.0", git = "https://github.com/dsmcdermott/rly" }
```

([`lex`](self) needs to be added as a build dependency so that we can use it in
`build.rs`.)

Then, make a file called "[`build.rs`][bs]" in the package root directory with the
following contents:

``` no_run
// build.rs

use lex::{LexerBuilder, LexerBuilderError};

fn main() -> Result<(), LexerBuilderError> {
	LexerBuilder::new()
		.unwrap()
		.build()?
		.set_rerun()
		.unwrap();
	Ok(())
}
```

What this does is create a new [`LexerBuilder`], call [`build`](LexerBuilder::build) to
build a lexer, and then call [`set_rerun`](LexerBuilder::set_rerun) to set cargo to watch
our lexer source file for changes and rerun the build script when it detects one.

Now, if you were to try to build the package as-is, with `cargo build`, you would
encounter the following error:

``` text
   Compiling calculator v0.1.0 (/path/to/project/calculator)
error: failed to run custom build command for `calculator v0.1.0 (/path/to/project/calculator)`

Caused by:
  process didn't exit successfully: `/path/to/project/calculator/target/debug/build/calculator-<hash>/build-script-build` (exit status: 1)
  --- stderr
  Error: IO(Os { code: 2, kind: NotFound, message: "No such file or directory" })
```

This is because [`LexerBuilder`] cannot find our lexer source file (because we haven't
written any yet.) As explained at [`LexerBuilder`](LexerBuilder#name-and-location), the
[`LexerBuilder`], by default, looks for a source file with the name of the current project
plus "`_lex.lex`".

So, our next step is to make this file. Remember, we want to be able to recognize addition
and subtraction (as well as negation,) and be able to recognize numbers written in base 2,
8, 10, and 16 using [the same format as rust][il]. Let's also say that whitespace is
ignored.

(Before reading further, it might be worthwhile to try and come up with a `.lex` file
yourself as an exercise. Using [the 'syntax' section of this documentation](self#syntax)
and [the rust integer literal rules][il] (remember, we're ignoring underscores '`_`'
between digits for simplicity's sake) as guides, try and make a valid `.lex` file that
achieves what we want, and compare your answer to the sample given below.)

We would therefore make a file called `calculator_lex.lex` as follows[^precedence]:

``` text
## calculator_lex.lex

BIN : "0b[01]+"
OCT : "0o[0-7]+"
HEX : "0x[0-9a-fA-F]+"
DEC : "[0-9]+"
PLUS : "\+"
MINUS : "-"
ignore : "\s+"
```

[^precedence]: Note that because of the [precedence rules](self#rules) the order in which
`DEC` is placed relative to `BIN`, `OCT`, and `HEX` does matter! For example, if `DEC`
were placed higher than `HEX`, then when trying to lex "`0xA`" it would first return "`0`"
as a `DEC`, and then return an [`Error`] for "`xA`", instead of just parsing the whole
thing as a `HEX`, which is clearly not what we want.

Your directory structure should look something like this (minus any `Cargo.lock` or
`target/` files:)

``` text
calculator/
├── build.rs
├── calculator_lex.lex
├── Cargo.toml
└── src/
    └── main.rs
```

The next step, after having made a build script to automatically generate our lexer, is to
include that lexer in our source code. [`LexerBuilder`] writes the
[module](self#lexer-structure) it generates to the directory set by cargo in the
[`OUT_DIR`][od] environment variable, and it by default writes it as a file with the name
of the package plus "`_lex.rs`". Therefore, if wanted to include the lexer in our code, we
could do something like this:

``` ignore
include!(concat!(env!("OUT_DIR"), "/calculator_lex.rs"));
```

However, this crate already contains a helper macro [`lexer!`] which we can use instead:

``` ignore
// src/main.rs

lex::lexer!();
```

Either way, this includes a [module](self#lexer-structure) called "`lexer`", generated by
[`LexerBuilder`] which contains the type `Lexer` whose instances can lex inputs by
spawning `Tokens`', which iterate over the lazily parsed tokens of a given input (see
[above](self#lexer-structure) for more details.)

Now that we have our lexer, we can use it to write our calculator. Write the following for
`src/main.rs`:

``` ignore
// src/main.rs

use std::io;

lex::lexer!();

use lexer::{Lexer, Token, TokenKind, Tokens};

// Our error type.
#[derive(Debug)]
enum Error {
    MissingOperand,
    UnexpectedInt,
    LexerError(lex::Error),
}

use Error::*;

impl From<lex::Error> for Error {
    fn from(err: lex::Error) -> Self {
        LexerError(err)
    }
}

type Result<T> = std::result::Result<T, Error>;

fn main() {
    let mut buffer = String::new();
    let stdin = io::stdin();
    loop {
        buffer.clear();
        stdin.read_line(&mut buffer).expect("unable to read input");
        println!("{}", parse(&buffer).expect("unable to parse input"));
    }
}

fn parse_dec(tok: Token<'_>) -> i32 {
    tok.val().parse::<i32>().unwrap()
}

fn parse_bin(tok: Token<'_>) -> i32 {
    i32::from_str_radix(&tok.val()[2..], 2).unwrap()
}

fn parse_oct(tok: Token<'_>) -> i32 {
    i32::from_str_radix(&tok.val()[2..], 8).unwrap()
}

fn parse_hex(tok: Token<'_>) -> i32 {
    i32::from_str_radix(&tok.val()[2..], 16).unwrap()
}

// Parses an integer when expecting one as an operand to "op". Like parse_integer except
// returns an err if no tokens remain in 'tokens'.
fn parse_operand(tokens: &mut Tokens<'_, '_>) -> Result<i32> {
    parse_integer(tokens)?.ok_or(MissingOperand)
}

// Attempts to parse an integer from 'tokens', returnin Ok(None) if no tokens remain.
fn parse_integer(tokens: &mut Tokens<'_, '_>) -> Result<Option<i32>> {
    let tok = match tokens.next() {
        Some(result) => result?,
        None => return Ok(None),
    };
    // Match the token kind to determine how to proceed.
    Ok(Some(match tok.kind() {
        TokenKind::DEC => parse_dec(tok),
        TokenKind::BIN => parse_bin(tok),
        TokenKind::OCT => parse_oct(tok),
        TokenKind::HEX => parse_hex(tok),
        // If the current token is a unary "+" operator, just return the next parsed
        // integer. ("+3" is the same as "3")
        TokenKind::PLUS => parse_operand(tokens)?,
        // If the current token is a unary "-" operator, return the negative version of
        // the next integer.
        TokenKind::MINUS => -parse_operand(tokens)?,
    }))
}

// Parse a string by calculating its value.
fn parse<S: AsRef<str>>(inp: S) -> Result<i32> {
    // our lexer
    let lexer = Lexer::new();
    // our 'Tokens' instance. Iterates over the lazily parsed tokens of 'inp'
    let mut tokens = lexer.lex(inp.as_ref());
    // our accumulator, initialized to the first integer
    let mut acc = match parse_integer(&mut tokens)? {
        Some(n) => n,
        // if the input is empty return the additive identity
        None => return Ok(0),
    };
    // add or subtract from the accumulator for the remaining values
    loop {
        // break if no more tokens remaining
        let tok = match tokens.next() {
            Some(res) => res?,
            None => break,
        };
        // if the current token is "+", add the next integer, if it's "-" subtract the
        // next one instead, if it's and intiger return an error
        match tok.kind() {
            TokenKind::PLUS => acc += parse_operand(&mut tokens)?,
            TokenKind::MINUS => acc -= parse_operand(&mut tokens)?,
            _ => return Err(UnexpectedInt),
        };
    }
    Ok(acc)
}
```

Then test it out by using `cargo run`.

[od]: https://doc.rust-lang.org/stable/cargo/reference/environment-variables.html#environment-variables-cargo-sets-for-build-scripts
[il]: https://doc.rust-lang.org/reference/tokens.html#number-literals
[wl]: https://en.wikipedia.org/wiki/Lexer
[bs]: https://doc.rust-lang.org/cargo/reference/build-scripts.html
[drv]: https://doc.rust-lang.org/reference/attributes/derive.html
[ei]: crate#error-and-ignore
