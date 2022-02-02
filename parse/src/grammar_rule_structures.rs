// This module contains some common structures used throughout the crate.
//
// Additional parts of this module may be made public in the future, but for now only the
// minimum necessary for building an using parsers is being made available.

use std::hash::Hash;

/// An alias for [`Copy`] + [`Hash`] + [`Ord`].
///
/// Used to indicate that a type is "primitive" and suitable for use as a discriminant
/// for generating parsers.
pub trait Prim: Copy + Hash + Ord {}
impl<T: Copy + Hash + Ord> Prim for T {}

// An enumeration for symbols. Can be either non-terminal (NonTerm) or terminal
// (Term).
//
// In general, throughout this crate the generic variable 'N' should be used for
// non-terminal symbols and 'T' for terminal symbols.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Symbol<N: Prim, T: Prim> {
	NonTerm(N),
	Term(T),
}

impl<N: Prim, T: Prim> Symbol<N, T> {
	pub fn as_non_term(self) -> Option<N> {
		match self {
			Self::NonTerm(n) => Some(n),
			Self::Term(_) => None,
		}
	}

	pub fn as_term(self) -> Option<T> {
		match self {
			Self::Term(t) => Some(t),
			Self::NonTerm(_) => None,
		}
	}
}

// A grammar or production rule.
#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct GrammarRule<N: Prim, T: Prim> {
	// the left hand side of the production rule
	lhs: N,

	// the right hand side
	rhs: Vec<Symbol<N, T>>,
}

impl<N: Prim, T: Prim> GrammarRule<N, T> {
	pub(crate) fn new(lhs: N, rhs: Vec<Symbol<N, T>>) -> Self {
		Self { lhs, rhs }
	}

	pub fn lhs(&self) -> &N {
		&self.lhs
	}

	pub fn rhs(&self) -> &[Symbol<N, T>] {
		&self.rhs
	}

	pub fn into_pair(self) -> (N, Vec<Symbol<N, T>>) {
		(self.lhs, self.rhs)
	}

	// Copies self.lhs
	pub fn as_basic_item(&self) -> BasicItem<'_, N, T> {
		BasicItem::new(self.lhs, self.rhs())
	}
}

// Used for testing purposes.
#[cfg(test)]
pub fn grammar_rule<N: Prim, T: Prim>(lhs: N, rhs: Vec<Symbol<N, T>>) -> GrammarRule<N, T> {
	GrammarRule { lhs, rhs }
}

//
//	BasicItem, LR0Item, and Item follow a pretty obvious inheritance pattern.
//	Unfortunately, rust intentionally does not allow inheritance. What I've done
//	instead is compose the items and implement, for LR0Item and Item, a method
//	producing a reference to the field containing an element of the previous type in
//	the chain. I then re-implemented the relevant methods in a straightforward way by
//	calling the method in question on the that reference to the field containing the
//	composed object. I've tried to keep the re-implemented methods visually seperate
//	and tidy.
//
//	In the future I may implement this using traits.
//

// A version of GrammarRule that borrows instead of owns self.rhs
#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug)]
pub struct BasicItem<'a, N: Prim, T: Prim> {
	lhs: N,
	rhs: &'a [Symbol<N, T>],
}

impl<'a, N: Prim, T: Prim> BasicItem<'a, N, T> {
	pub fn new(lhs: N, rhs: &'a [Symbol<N, T>]) -> Self {
		Self { lhs, rhs }
	}

	pub fn lhs(&self) -> &N {
		&self.lhs
	}

	pub fn rhs(&self) -> &'a [Symbol<N, T>] {
		self.rhs
	}

	pub fn len(&self) -> usize {
		self.rhs().len()
	}

	pub fn get(&self, i: usize) -> Option<&Symbol<N, T>> {
		self.rhs().get(i)
	}
}

impl<'a, N: Prim, T: Prim> From<&'a GrammarRule<N, T>> for BasicItem<'a, N, T> {
	fn from(rule: &'a GrammarRule<N, T>) -> Self {
		rule.as_basic_item()
	}
}

// An LR0 item; A BasicItem with an index indicating the progress of the abstract
// state machine in parsing the right hand side of the production rule.
//
// Instances of this struct should have an index no greater than self.len() (the
// length of basic.rhs().) That is to say that self.index can be equal to self.len()
// (and thus greater than the index of any element in self.rhs(),) representing a
// parser that has finished parsing the right hand side of the production rule, but it
// cannot be any higher.
//
// Having an index past self.len() can cause innacurate behaviour, but it generally
// won't be checked for unless the debug_assertions flag is set.
#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug)]
pub struct LR0Item<'a, N: Prim, T: Prim> {
	basic: BasicItem<'a, N, T>,

	// Position of the parser in the rule.
	index: usize,
}

impl<'a, N: Prim, T: Prim> LR0Item<'a, N, T> {
	// Creates a new LR0Item. Does not check that index <= rhs.len() unless running
	// with the debug_assertions flag.
	fn new_unchecked(lhs: N, rhs: &'a [Symbol<N, T>], index: usize) -> Self {
		Self::from_basic(BasicItem::new(lhs, rhs), index)
	}

	pub fn basic(&self) -> &BasicItem<'a, N, T> {
		&self.basic
	}

	pub fn index(&self) -> usize {
		self.index
	}

	// Returns whether self is terminal, i.e. whether self.index() == self.len().
	pub fn is_terminal(&self) -> bool {
		debug_assert!(!self.index() > self.len());
		self.index() == self.len()
	}

	// The current symbol pointed to by self.index(). Returns None if self is terminal.
	pub fn current(&self) -> Option<&Symbol<N, T>> {
		self.get(self.index())
	}

	// Creates a new LR0Item from a BasicItem. Does not check that index <= rhs.len()
	// unless running with the debug_assertions flag.
	pub fn from_basic(basic: BasicItem<'a, N, T>, index: usize) -> Self {
		debug_assert!(index <= basic.len());
		Self { basic, index }
	}

	// Used for testing purposes.
	#[cfg(test)]
	pub fn from_rule(rule: &'a GrammarRule<N, T>, index: usize) -> Self {
		Self::from_basic(BasicItem::from(rule), index)
	}

	// Creates a new LR0Item from self with the index being self.index() incremented
	// by one. When self is terminal, it returns an invalid item.
	pub fn increment(self) -> Self {
		debug_assert!(!self.is_terminal());
		Self::from_basic(self.basic, self.index + 1)
	}

	//
	// Re-implemented methods from BasicItem.
	//

	pub fn lhs(&self) -> &N {
		self.basic().lhs()
	}

	// BasicItem::rhs is unused from LR0Item.

	pub fn len(&self) -> usize {
		self.basic().len()
	}

	pub fn get(&self, i: usize) -> Option<&Symbol<N, T>> {
		self.basic().get(i)
	}
}

// An LR1 item; An LR0 item (LR0Item) with a single look-ahead 'la' indicating the
// look-ahead terminal expected after self.rhs() is parsed.
//
// The word 'core' is typically used here to refer to LR0Items, but this should be
// avoided elsewhere in order to avoid confusion with the "core items" of a parser
// table.
#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug)]
pub struct Item<'a, N: Prim, T: Prim> {
	core: LR0Item<'a, N, T>,
	la: T,
}

impl<'a, N: Prim, T: Prim> Item<'a, N, T> {
	// Creates a new instance of Item with self.index() = 0.
	pub fn new_init(lhs: N, rhs: &'a [Symbol<N, T>], la: T) -> Self {
		Self::new_unchecked(lhs, rhs, 0, la)
	}

	// Creates a new Item. Does not check that index is less than or equal to
	// rhs.len() unless running with debug assertions.
	fn new_unchecked(lhs: N, rhs: &'a [Symbol<N, T>], index: usize, la: T) -> Self {
		Self::from_core(LR0Item::new_unchecked(lhs, rhs, index), la)
	}

	pub fn from_core(core: LR0Item<'a, N, T>, la: T) -> Self {
		Self { core, la }
	}

	// Used for testing purposes.
	#[cfg(test)]
	pub fn from_rule(rule: &'a GrammarRule<N, T>, index: usize, la: T) -> Self {
		Self::from_core(LR0Item::from_rule(rule, index), la)
	}

	pub fn core(&self) -> &LR0Item<'a, N, T> {
		&self.core
	}

	pub fn look_ahead(&self) -> &T {
		&self.la
	}

	// Returns the "follow" symbol: the symbol expected next after a shift.
	// self.rhs[self.index()+1] unless self is penultimate, in which case it returns
	// Symbol::Term(self.la). Gives improper value for terminal items, which don't
	// actually have follow symbols.
	pub fn follow(&self) -> Symbol<N, T> {
		debug_assert!(self.index() < self.len());
		match self.get(self.index() + 1) {
			Some(sym) => *sym,
			None => Symbol::Term(*self.look_ahead()),
		}
	}

	// Same as LR0Item::increment but for Items, keping the same la.
	pub fn increment(self) -> Self {
		Self::from_core(self.core.increment(), self.la)
	}

	//
	// re-implemented methods from LR0Item
	//

	pub fn index(&self) -> usize {
		self.core().index()
	}

	pub fn is_terminal(&self) -> bool {
		self.core().is_terminal()
	}

	pub fn lhs(&self) -> &N {
		self.core().lhs()
	}

	pub fn len(&self) -> usize {
		self.core().len()
	}

	pub fn get(&self, i: usize) -> Option<&Symbol<N, T>> {
		self.core().get(i)
	}

	pub fn current(&self) -> Option<&Symbol<N, T>> {
		self.core().current()
	}
}

mod display {
	use super::{GrammarRule, Item, Prim, Symbol};
	use std::fmt::{Arguments, Display, Formatter, Result as FmtResult};

	#[rustfmt::skip]
	fn id<T>(t: T) -> T { t }

	//  For displaying or writing Item's while formating their symbols.
	//
	//  'f' writes the components. e.g. |a: Arguments| write!(fout, "{}", a).
	//  'dn', or "display non-terminal" discribes how to display a non-terminal
	//  symbol.
	//  'dt' discribes how to display a terminal symbol.
	//
	//  Item's are written using 'f' according to the format:
	//  '[{lhs} -> {rhs_0} {rhs_1} ... {rhs_(index-1)} ·{rhs_index} ... {rhs_(self.len())}, {la}]'
	//
	//  with an interpunt '·' (U+00B7) before the rhs item pointed to by self.index().
	//  If self is terminal (with self.index() == self.len()), then an interpunct is
	//  written after the last item, like so: '{rhs_(self.len())}·, {la}]'.
	//
	//  Item's implement Display (for N: Display and T: Display) by calling this
	//  method with f = |arg| write!(formatter, "{}", arg), and dn, dt = id.
	impl<'a, N: Prim, T: Prim> Item<'a, N, T> {
		pub fn display_with<'b, F, G, H, D, L, E>(
			&'b self,
			mut f: F,
			mut dn: G,
			mut dt: H,
		) -> Result<(), E>
		where
			F: FnMut(Arguments<'_>) -> Result<(), E>,
			G: FnMut(&'b N) -> D,
			H: FnMut(&'b T) -> L,
			D: Display,
			L: Display,
		{
			f(format_args!("[{} ->", dn(self.lhs())))?;
			for i in 0..self.len() {
				let sym = self.get(i).unwrap();
				if i == self.index() {
					sym.display_with(|arg| f(format_args!(" \u{00B7}{}", arg)), &mut dn, &mut dt)?;
				} else {
					sym.display_with(|arg| f(format_args!(" {}", arg)), &mut dn, &mut dt)?;
				};
			}
			if self.is_terminal() {
				f(format_args!("\u{00B7}"))?;
			};
			f(format_args!(", {}]", dt(&self.look_ahead())))
		}

		pub fn displayer<'b, G, H, D, L>(
			&'b self,
			dn: G,
			dt: H,
		) -> Displayer<'a, 'b, N, T, G, H, D, L>
		where
			G: Fn(&'b N) -> D,
			H: Fn(&'b T) -> L,
			D: Display,
			L: Display,
		{
			Displayer(self, dn, dt)
		}
	}

	//  A wrapper that implements Display by calling display_with using self.1 and
	//  self.2
	pub struct Displayer<'a, 'b, N, T, G, H, D, L>(&'b Item<'a, N, T>, G, H)
	where
		N: Prim,
		T: Prim,
		G: Fn(&'b N) -> D,
		H: Fn(&'b T) -> L,
		D: Display,
		L: Display;

	impl<'a, 'b, N, T, G, H, D, L> Display for Displayer<'a, 'b, N, T, G, H, D, L>
	where
		N: Prim,
		T: Prim,
		G: Fn(&'b N) -> D,
		H: Fn(&'b T) -> L,
		D: Display,
		L: Display,
	{
		fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
			self.0
				.display_with(|arg| write!(f, "{}", arg), &self.1, &self.2)
		}
	}

	//  Item's are displayed according to the format:
	//  '[{lhs} -> {rhs_0} {rhs_1} ... {rhs_(index-1)} ·{rhs_index} ... {rhs_(self.len())}, {la}]'
	//
	//  with an interpunt '·' (U+00B7) before the rhs item pointed to by self.index().
	//  If self is terminal (with self.index() == self.len()), then an interpunct is
	//  written after the last item, like so: '{rhs_(self.len())}·, {la}]'.
	impl<'a, N: Prim + Display, T: Prim + Display> Display for Item<'a, N, T> {
		fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
			self.display_with(|arg| write!(f, "{}", arg), id, id)
		}
	}

	impl<N: Prim, T: Prim> Symbol<N, T> {
		pub fn display_with<'a, F, G, H, D, L, E>(&'a self, f: F, dn: G, dt: H) -> Result<(), E>
		where
			F: FnOnce(Arguments<'_>) -> Result<(), E>,
			G: FnOnce(&'a N) -> D,
			H: FnOnce(&'a T) -> L,
			D: Display,
			L: Display,
		{
			macro_rules! farg {
				($arg: expr) => {
					format_args!("{}", $arg)
				};
			}
			match self {
				Self::NonTerm(n) => f(farg!(dn(n))),
				Self::Term(t) => f(farg!(dt(t))),
			}
		}
	}

	impl<N: Prim + Display, T: Prim + Display> Display for Symbol<N, T> {
		fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
			self.display_with(|arg| write!(f, "{}", arg), id, id)
		}
	}

	impl<N: Prim + Display, T: Prim + Display> Display for GrammarRule<N, T> {
		fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
			write!(f, "[{} ->", self.lhs())?;
			for i in 0..self.rhs().len() {
				write!(f, " {}", self.rhs()[i])?;
			}
			write!(f, "]")
		}
	}
}
