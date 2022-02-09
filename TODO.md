This is a list of changes to be made. Aside from the categories of "Important", "Less
Important" etc., they are in no particular order.

# Important Changes

## Architectural Changes

- [x] Get rid of the crate `rly_common` (or at least the modules `parse` and `tokens`
and incorporate it into the crates `lex` and `parse`

- [x] Make the `Ast` type created for parsers a permanent struct in
`rly_common::parse` (or wherever the trait `rly_common::parse::Ast` gets moved to) and
have it replace the `Ast` trait.

## Interface Changes

- [ ] ~~Change instances of the name `NonTerm` in the `Ast` trait (associated type,
methods, documentation, etc.) to `Label`; having `NonTerm` and `Term` refer concepts
in slightly different categories is confusing, and `Label` is more
descriptive/accurate anyway~~

## Documentation

- [ ] Fill out the documentation on the items in `rly_common::parse` to include
examples.

## Parser Specification Language

- [ ] ~~Eliminate the need for `start` and `eof` to be reserved words: Change the parser
generation process to no longer assume that the strings "`start`" and "`eof`" are
available without conflicts with the original specification, and change the specification
format to include a way of explicitly declaring a starting symbol.~~

- [x] `eof` is no longer reserved. `start` however has been changed to `Start` and is
still reserved, which is how I intend to keep it for now. `crate`, `self`, `super`, and
`Self` have been added as reserved words, in line with the new use of raw identifiers for
variant names.

## Testing

- [ ] Come up with a better/more comprehensive automated testing suite.

This one is tricky since the nature of this project (focused on dynamically generating
rust code at build time) doesn't play nice with the normal cargo testing tools, but it
should be doable.

## Clippy

- [ ] Learn how clippy works and see if there's anything I need to do to make the
generated modules play nice with it.

# Less Important Changes

## Architectural/Interface Changes

- [ ] Change how generated parser (and possibly lexer) modules import from their
environment: Make them dependent on the on the importer macro `parser!` to set up a
hygenic environment and allow the importer macro to take additional paramaters
specifying where to import the necessary items.

## Error Recovery

- [ ] Improve the ability of lexers to recover from errors by allowing them to "skip"
erronious sections after reporting the error.

- [ ] Improve the ability of parsers to recover from errors by implementing a strategy
where, upon encountering erronious tokens, the parser tries to correct it and then
continue parsing in order to search for further errors.

## Interface Changes

- [x] Change how the variants on the generated types `TokenKind` and `NonTerm` are
named: From `T_<name>` and `N_<name>`, respectively, to using raw identifiers.

- [ ] Review the internal types used for parser generation and see if any should be
made public.

## Parser Generation Changes

- [ ] Review the item set generation process for potential improvements (particularly,
using hashing to improve the performance of comparing item sets for merging.)

## Parser Specification Language

- [ ] Add the ability to specify an explicit list of terminal and non-terminal
symbols, which can then be verified against the given rules.

## Unicode

- [ ] Change `ErrorData` and `LineOffset` to accurately display the location of an
error within a line that may contain characters consisting of multiple unicode code
points, such as "`Ü`".

## Module Formatting

- [ ] Review the process for formatting compiled lexers and parsers into rust source code
modules and see if it can be changed to make it simpler and/or easier to modify to module
templates.

# Stretch Goals

## Parser Capability

- [ ] Add the ability to use empty production rules when generating parsers.

## Specifications

- [ ] Add the ability to link lexer and parser specifications for verification and
error checking on the non-terminal symbols.

- [ ] Allow you to use string literals in parser specifications.

### Unicode

- [ ] Change the specification formats to have identifiers conform to Unicode standard
annex #31

## Interface

### Builds

- [ ] Make an installable binary for generating parsers (and lexers) that can be called as
an external process in build scripts.

### Parser Generation

- [ ] Add an option for reproducible builds using BTree Sets/Maps instead of Hash
Sets/Maps.

# Super Stretch Goals

- [ ] Make `parse` more like yacc by allowing you to specify types and functions to go
along with the production rules.

- [ ] Investigate using, and possibly implement, procedural macros for generating lexers
and parsers
