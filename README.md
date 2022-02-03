# About This Package

This is a combined lexer/parser generator that can be used as a build dependency to read
parser and lexer specifications and generate rust source-code modules that can then be
included in your project.

At its heart, this package contains facilities for reading its custom parser and lexer
specification formats, and then using them to write out strings that contain valid rust
source-code for a module containing items for parsing or lexing according to input
specification. These modules can be written to stand-alone files and then "imported" using
rust's built-in [`include`] macro. This can be automated using build scripts, and to that
end this package also contains helper tools for using build scripts with Cargo to watch
and compile specification files and for including the result.

Additionally, the crates in this package provide various types and traits which are used
by the generated modules. These serve three purposes: 1. Reducing the amount of code that
must be included in each module. 2. Providing accessable documentation on the behaviour of
the generated items. 3. Providing a common interface accross the generated items and
providing a way to generalize over them.

While the lexing and parsing facilities are designed to be able to work with each other,
they are also designed to be usable independently of each other, with parsers only
assuming that a given lexer implements certain interfaces, and lexers being usable without
any parser at all.

Note that this project is still very much a work-in-progress. See `TODO.md` for more
information about what needs to be done.

For more information, the online documentation for the package can be read [here].

## Parsers

The parsers built by this package (specifically, the crate `parse`) are normal [LR
parsers], however they are implemented using a ["recursive ascent"] strategy, meaning
that, essentially, the states of the parser are implemented as seperate functions
implementing the behaviour of the parser at a given state, rather than the traditional
method of having a data table of states and an interpreter function which looks up the
current state and decides which actions to take accordingly.

The parsers are built by generating states for a [cannonical LR(1) parser] and merging
those states in the manner of an [LALR parser] where it is possible to do so without
introducing conflicts. The result is that, for LALR grammars, it produces an LALR parser,
and for grammars which are not LALR, it produces a parser capable of parsing them but with
less memory usage than for a full cannonical LR parser.

Parsers require a lexing step to first break an input into tokens, each containing a
[`str`] and a discriminant value, which can then be parsed. They do not act on input
directly, but instead use a lexer type which, essentially, implements [`Iterator`] by
returning tokens. Parser use traits defined in the crate `lex` to interact with lexers
and, while these traits are implemented by lexers generated by `lex` and those lexers are
guarenteed to be compatable with the parsers generated by `parse` (provided that the lexer
and parser specifications are compatible,) the parsers generated by `parse` are usable
with any lexer which properly implements those traits.

Parser specifications take the form of a simple context-free grammar which is then used as
the basis for parsing tokens and constructing a syntax tree.

## Lexers

Lexer specifications consist of pairs of labels and regexes which define rules for lexing
the associated tokens. Lexers generated from a given specification lex their inputs by
attempting to match the regexes in each of the rules, in order, against the beginning of
the unmatched portion of the input; when a match is found, the lexer returns the matched
portion of the text as a token with the corresponding label.

The exception to this is are rules with the label `ignore` and `error`. When the lexer
matches a portion of the input with the `ignore` rule, instead of returning portion it
simply skips over it and attempts to return another token. When it matches the `error`
rule, it returns the matched text as an error.

The lexers generated by `lex` take [`str`]'s and produce iterators that implement
[`Iterator`] by using data stored in the lexer to lazily parse the input [`str`] for
tokens.

# Contents

This package consists of three crates: `lex`, `parse`, and `rly_common`. `lex` and `parse`
contain the code for generating lexers and parsers, respectively, as well as the traits
and types imported by their generated modules. Parser modules generated by `parse`
additionally rely on reexports in `parse` of certain traits and types from `lex`.
`rly_common` contains code that is used in both `parse` and `lex` and is used internally
by those crates.

For both `lex` and `parse`, the top-level documentation and the code for their `lib.rs`
files are split into seperate files (`lexer_doc.md` and `parser_doc.md` and
`lib_content.rs` respectively) to make editing the documentation more convenient. These
crates use `rly_common` as a build dependency to combine the documentation in the markdown
file with the code in the content file to generate the `lib.rs` file.

# Building the Package

Once the repository has been cloned, all you need to do to build it is run `cargo build`
inside the root directory of the project.

However, since this is (currently) a library package only, there's not much point to
building it on its own. To use it as a part of another project, you can either clone the
repository and add the necessary crates as [path dependencies] to you `Cargo.toml` file,
or you can add the crates as [git dependencies] and cargo will automatically download and
build them as necessary.

## Building the Documentation

The documentation for the package can be read online [here], but it can also be built
locally.

To build the documentation for this project, run `cargo doc` inside the top-level
directory for the workspace. The html documentation for `lex`, `parse`, and `rly_common`
can then be found as directories in `targed/doc`.



[`include`]: https://doc.rust-lang.org/std/macro.include.html
[here]: https://dsmcdermott.github.io/rly-docs/
[LR parsers]: https://en.wikipedia.org/wiki/LR_parser
["recursive ascent"]: https://en.wikipedia.org/wiki/Recursive_ascent_parser
[cannonical LR(1) parser]: https://en.wikipedia.org/wiki/Canonical_LR_parser
[LALR parser]: https://en.wikipedia.org/wiki/LALR_parser
[`str`]: https://doc.rust-lang.org/std/primitive.str.html
[`Iterator`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html
[path dependencies]: file:///home/sam/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/share/doc/rust/html/cargo/reference/specifying-dependencies.html#specifying-path-dependencies
[git dependencies]: file:///home/sam/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/share/doc/rust/html/cargo/reference/specifying-dependencies.html#specifying-dependencies-from-git-repositories