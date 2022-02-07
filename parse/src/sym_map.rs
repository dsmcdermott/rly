// This module contains the struct SymMap, which is responsable for defining and
// processing the mapping between discriminants for terminal and non-terminal symbols and
// the str representations of those symbols.
//
// To be converted from a str, a discriminant type must implement FromUsize, and to be
// converted, a discriminant type must implement IntoUsize.
//
// SymMap converts between str's and discriminants by keeping a Vec of str's for non-terms
// and a Vec of str's for terminals, both of which are sorted. To convert from a
// discriminant to a str, IntoUsize::into is called on the discriminant and the resulting
// value is used as an index into the corresponding Vec of str's to retrieve the str value
// of the discriminant. To convert from a str to a discriminant, the string is found in
// the corresponding vector using slice::binary_search(), and FromUsize::from is called on
// the resulting index to get the discriminant.

// TODO: Combine FromUsize and IntoUsize into a single trait; I dont see the sense in
// keeping them seperate anymore.

use std::{
	collections::BTreeSet,
	error,
	fmt::{self, Debug},
};

use crate::{
	START,
	grammar_rule_structures::{Prim, Symbol},
	scanning::RuleMap,
};

/// A trait for converting from [`usize`] to a discriminant. This is required for
/// generating a [`Rules`](super::Rules) or [`ParserSpec`](super::ParserSpec) from a
/// source text.
///
/// A type that implements both [`FromUsize`] and [`Eq`] must ensure that the
/// implementation of [`from`](FromUsize::from) must preserve and reflect equality, e.g.:
///
/// ```
/// use parse::FromUsize;
///
/// fn test_eq<T: Eq + FromUsize>(l: usize, r: usize) {
/// 	let is_eq_int = l == r;
/// 	let is_eq = T::from(l) == T::from(r);
/// 	assert_eq!(is_eq_int, is_eq);	// l == r if and only if T::from(l) == T::from(r)
/// }
/// ```
///
/// # Implementing both FromUsize and IntoUsize
///
/// If a type implements both [`FromUsize`] and [`IntoUsize`], it should ensure that
/// [`from`] and [`into`] are isomorphisms. That is, calling [`from`] and then [`into`]
/// should return the same number as the one you started with (or panic,) and calling
/// [`into`] and then [`from`] should return an equivalent object to the original (or
/// panic.) For example:
///
/// ```
/// use parse::{FromUsize, IntoUsize};
///
/// fn endo_t<T: FromUsize + IntoUsize>(t: T) -> T {
/// 	T::from(t.into())
/// }
///
/// fn endo_usize<T: FromUsize + IntoUsize>(n: usize) -> usize {
/// 	T::from(n).into()
/// }
///
/// assert_eq!(128u8, endo_t(128u8));
/// assert_eq!(128, endo_usize::<u8>(128));
/// ```
///
/// [`into`]: IntoUsize::into
/// [`from`]: FromUsize::from
pub trait FromUsize {
	/// The maximum size that `Self` can be converted from.
	const MAX: usize;

	/// Converts a [`usize`] to a `Self`. Returns [`None`] if `n` is greater than
	/// [`Self::MAX`], otherwise returns [`Some`]. For exmple:
	///
	/// ```
	/// use parse::FromUsize;
	///
	/// assert_eq!(<u8 as FromUsize>::MAX, 255);
	///
	/// let none = <u8 as FromUsize>::try_from(256);
	/// let some = <u8 as FromUsize>::try_from(255);
	///
	/// assert!(matches!(none, None));
	/// assert!(matches!(some, Some(255)));
	/// ```
	fn try_from(n: usize) -> Option<Self>
	where
		Self: Sized;

	/// Equivalent to [`Self::try_from(n).unwrap()`](FromUsize::try_from).
	///
	/// # Panic
	///
	/// Implementations should panic if `n` is greater than [`Self::MAX`]. Otherwise, the
	/// result should be the same as calling [`unwrap`](Option::unwrap) on the result of
	/// [`Self::try_from`].
	///
	fn from(n: usize) -> Self
	where
		Self: Sized,
	{
		Self::try_from(n).expect("called FromUsize::from on an invalid value")
	}
}

//impl<T> FromUsize for T
//	where
//		T: TryFrom<usize, Error = TryFromIntError>,
//{
//	fn from(n: usize) -> Self {
//		Self::try_from(n).unwrap()
//	}
//}

macro_rules! impl_from_usize {
	($($size: ty),*) => {
		$(impl FromUsize for $size {
			const MAX: usize = Self::MAX as usize;
			fn try_from(n: usize) -> Option<Self> {
				<Self as TryFrom<usize>>::try_from(n).ok()
			}
		})*
	};
}

impl_from_usize!(u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize);

/// A trait for converting from a discriminant to [`usize`]. This is required for writing
/// a parser using a [`ParserSpec`](super::ParserSpec).
///
/// A type that implements both [`IntoUsize`] and [`Eq`] must ensure that the
/// implementation of [`into`] must preserve and reflect equality, e.g.:
///
/// ```
/// use parse::IntoUsize;
///
/// fn test_eq<T: Eq + IntoUsize>(l: T, r: T) {
/// 	let is_eq = &l == &r;
/// 	let is_eq_int = l.into() == r.into();
/// 	assert_eq!(is_eq, is_eq_int);	// l == r if and only if l.into() == r.into()
/// }
/// ```
///
/// # Implementing both FromUsize and IntoUsize
///
/// If a type implements both [`FromUsize`] and [`IntoUsize`], it should ensure that
/// [`from`] and [`into`] are isomorphisms. That is, calling [`from`] and then [`into`]
/// should return the same number as the one you started with (or panic,) and calling
/// [`into`] and then [`from`] should return an equivalent object to the original (or
/// panic.) For example:
///
/// ```
/// use parse::{FromUsize, IntoUsize};
///
/// fn endo_t<T: FromUsize + IntoUsize>(t: T) -> T {
/// 	T::from(t.into())
/// }
///
/// fn endo_usize<T: FromUsize + IntoUsize>(n: usize) -> usize {
/// 	T::from(n).into()
/// }
///
/// assert_eq!(128u8, endo_t(128u8));
/// assert_eq!(128, endo_usize::<u8>(128));
/// ```
///
/// [`into`]: IntoUsize::into
/// [`from`]: FromUsize::from
pub trait IntoUsize {
	/// Converts `self` into a [`usize`].
	///
	/// If `Self` implements both [`FromUsize`] and [`IntoUsize`], then this function
	/// should always return [`Some`] on a value that can be generated by [`FromUsize`].
	///
	/// ```
	/// use parse::{FromUsize, IntoUsize};
	///
	/// let n = <u8 as FromUsize>::from(128);
	///
	/// let result = <u8 as IntoUsize>::try_into(n);
	///
	/// assert!(matches!(result, Some(_)));
	/// ```
	///
	/// See also the requirements
	/// [here](IntoUsize#implementing-both-fromusize-and-intousize) for a type that
	/// implements both [`FromUsize`] and [`IntoUsize`].
	fn try_into(self) -> Option<usize>
	where
		Self: Sized;

	/// Equivalent to calling [`self.try_into().unwrap()`](IntoUsize::try_into).
	///
	/// # Panic
	///
	/// Implementations should panic when [try_into](IntoUsize::try_into) would return
	/// [`None`]. Otherwise, they should return the equivalent of calling
	/// [`unwrap`](Option::unwrap) on [`self.try_into`].
	fn into(self) -> usize
	where
		Self: Sized,
	{
		self.try_into()
			.expect("called IntoUsize::into on an invalid value")
	}
}

//impl<T> IntoUsize for T
//where
//	T: TryInto<usize, Error = TryFromIntError>,
//{
//	fn into(self) -> usize {
//		self.try_into().unwrap()
//	}
//}

macro_rules! impl_into_usize {
	($($size: ty),*) => {
		$(impl IntoUsize for $size {
			fn try_into(self) -> Option<usize> {
				<Self as TryInto<usize>>::try_into(self).ok()
			}
		})*
	};
}

impl_into_usize!(u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize);

#[derive(Debug)]
pub struct SymMap<'a> {
	non_terms: Vec<&'a str>,
	terms: Vec<&'a str>,
}

#[rustfmt::skip]
impl<'a> SymMap<'a> {
	pub fn new(map: &RuleMap<'a>) -> Self {
		let mut non_terms: Vec<_> = map.keys().copied().collect();
		debug_assert!(non_terms.contains(&START));
		non_terms.sort_unstable();
		let is_term = |s: &&str| !non_terms.binary_search(s).is_ok();
		let mut terms: BTreeSet<_> = map
			.values()           //Item = &Vec<Box<[&str]>>
			.flatten()          //Item = &Box<[&str]>
			.map(|x| x.iter())  //Item = Iter<&str>
			.flatten()          //Item = &&str
			.copied()           //Item = &str
			.filter(is_term)
			.collect();
		debug_assert!(!terms.contains(&"eof"));
		terms.insert("eof");
		let terms: Vec<_> = terms.into_iter().collect();
		debug_assert!(is_sorted(&terms));
		Self { non_terms, terms }
	}

	// Panics when the index of 'name' in self.non_terms is greater than T::MAX
	pub fn non_term_val<T: FromUsize>(&self, name: &str) -> Option<T> {
		search(&self.non_terms, name)
	}

	// Panics when the index of 'name' in self.terms is greater than T::MAX
	pub fn term_val<T: FromUsize>(&self, name: &str) -> Option<T> {
		search(&self.terms, name)
	}

	pub fn non_term<T: IntoUsize>(&self, sym: T) -> &'a str {
		self.non_terms[sym.into()]
	}

	pub fn term<T: IntoUsize>(&self, sym: T) -> &'a str {
		self.terms[sym.into()]
	}

	pub fn terms(&self) -> &[&'a str] {
		&self.terms
	}

	pub fn non_terms(&self) -> &[&'a str] {
		&self.non_terms
	}

	fn is_valid_non_term_discrim<N: FromUsize>(&self) -> Result<(), InvalidDiscriminant> {
		(self.non_terms().len() <= N::MAX)
			.then(|| ())
			.ok_or(InvalidDiscriminant::NonTerm)
	}

	fn is_valid_term_discrim<T: FromUsize>(&self) -> Result<(), InvalidDiscriminant> {
		(self.terms().len() <= T::MAX)
			.then(|| ())
			.ok_or(InvalidDiscriminant::Term)
	}

	fn are_valid_discrims<N: FromUsize, T: FromUsize>(&self) -> Result<(), InvalidDiscriminant> {
		self.is_valid_non_term_discrim::<N>()
			.and_then(|_| self.is_valid_term_discrim::<T>())
	}

	fn sym_vec<'s, I, N, T>(&self, iter: I) -> Vec<Symbol<N, T>>
	where
		I: IntoIterator<Item = &'s str>,
		N: Prim + FromUsize,
		T: Prim + FromUsize,
	{
		let mut vec = Vec::new();
		for sym in iter {
			if let Some(n) = self.non_term_val(sym) {
				vec.push(Symbol::NonTerm(n));
			} else if let Some(t) = self.term_val(sym) {
				vec.push(Symbol::Term(t));
			} else {
				panic!("Unrecognized symbol {}", sym);
			};
		}
		vec
	}

	// Returns an iterator of GrammarRule's (see grammar_rule_structures::GrammarRules)
	// from 'self' and 'rules'. Returns None if the discriminants are not large enough for
	// the number of symbols.
	pub fn grammar_rules<'b, N, T>(
		&'b self,
		rules: &'b RuleMap<'a>,
	) -> Result<GrammarRules<'a, 'b, N, T>, InvalidDiscriminant>
	where
		N: Prim + FromUsize,
		T: Prim + FromUsize,
	{
		self.are_valid_discrims::<N, T>()
			.map(|_| GrammarRules::new(self, rules).unwrap())
	}
}

/// An error type for discriminants that aren't large enough
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InvalidDiscriminant {
	/// Non-Terminal dicriminant.
	NonTerm,

	/// Terminal discriminant.
	Term,
}

impl fmt::Display for InvalidDiscriminant {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		use InvalidDiscriminant::*;
		let kind = match self {
			NonTerm => "non-terminal",
			Term => "terminal",
		};
		write!(
			f,
			"invalid {} discriminant type for number of symbols used",
			kind
		)
	}
}

impl error::Error for InvalidDiscriminant {}

mod grammar_rules {
	use super::{FromUsize, RuleMap, SymMap};
	use crate::grammar_rule_structures::{GrammarRule, Prim};
	use std::{collections::hash_map, marker::PhantomData, slice};

	// GrammarRules (not to be confused with crate::grammar_rules::GrammarRules) is
	// generated by a SymMap and a RuleMap. 'b is the lifetime of the SymMap and RuleMap
	// and 'a is the lifetime of the source str.
	//
	// GrammarRules iterates over the 'GrammarRule's (see
	// grammar_rule_structures::GrammarRule) represented by the RuleMap, using the SymMap
	// to convert the str's into Symbol's.
	pub struct GrammarRules<'a, 'b, N, T> {
		map: &'b SymMap<'a>,
		iter: hash_map::Iter<'b, &'a str, Vec<Box<[&'a str]>>>,
		lhs: &'a str,
		rhs: slice::Iter<'b, Box<[&'a str]>>,
		non_term_type: PhantomData<N>,
		term_type: PhantomData<T>,
	}

	fn next_lhs<'a, 'b>(
		iter: &mut hash_map::Iter<'b, &'a str, Vec<Box<[&'a str]>>>,
	) -> Option<(&'a str, slice::Iter<'b, Box<[&'a str]>>)> {
		iter.next().map(|(lhs, rhs)| (*lhs, rhs.iter()))
	}

	impl<'a, 'b, N, T> GrammarRules<'a, 'b, N, T> {
		fn next_lhs(&mut self) -> Option<()> {
			let (lhs, rhs) = next_lhs(&mut self.iter)?;
			self.lhs = lhs;
			self.rhs = rhs;
			Some(())
		}

		fn next_rhs(&mut self) -> Option<&'b [&'a str]> {
			match self.rhs.next() {
				Some(rhs) => Some(&rhs),
				None => {
					self.next_lhs()?;
					self.next_rhs()
				}
			}
		}
	}

	impl<'a, 'b, N, T> GrammarRules<'a, 'b, N, T>
	where
		N: Prim + FromUsize,
		T: Prim + FromUsize,
	{
		pub(crate) fn new(map: &'b SymMap<'a>, rules: &'b RuleMap<'a>) -> Option<Self> {
			let mut iter = rules.iter();
			let (lhs, rhs) = next_lhs(&mut iter)?;
			Some(Self {
				map,
				iter,
				lhs,
				rhs,
				non_term_type: PhantomData,
				term_type: PhantomData,
			})
		}
	}

	impl<'a, 'b, N, T> Iterator for GrammarRules<'a, 'b, N, T>
	where
		N: Prim + FromUsize,
		T: Prim + FromUsize,
	{
		type Item = GrammarRule<N, T>;

		fn next(&mut self) -> Option<Self::Item> {
			let rhs = self.next_rhs()?;
			let lhs = self.lhs;
			Some(GrammarRule::new(
				self.map.non_term_val(lhs).unwrap(),
				self.map.sym_vec(rhs.iter().copied()),
			))
		}
	}
}

pub use grammar_rules::GrammarRules;

// Panics when the index of 'name' is greater than T::MAX
fn search<'a, T>(l: &[&'a str], name: &str) -> Option<T>
where
	T: FromUsize,
{
	l.binary_search(&name).ok().map(|n| T::from(n))
}

#[cfg(debug_assertions)]
fn is_sorted<T, I>(iter: I) -> bool
where
	T: PartialOrd,
	I: IntoIterator<Item = T>,
{
	let mut iter = iter.into_iter();
	let mut current = match iter.next() {
		Some(x) => x,
		None => return true,
	};
	for x in iter {
		if !(current <= x) {
			return false;
		};
		current = x;
	}
	true
}

#[cfg(test)]
mod tests {
	use super::SymMap;
	use crate::scanning::Scanner;

	const TEST_DOC: &'static str = r#"

Start -> Expr;
Expr -> Fact ; 

Fact -> lparen Expr rparen
; Fact -> n;
	Fact 
-> plus Fact;

Fact -> 
	Fact
	plus
	n
;"#;

	#[test]
	fn test_new() {
		println!("{:?}", SymMap::new(&Scanner::scan_text(TEST_DOC).unwrap()));
	}

	#[test]
	fn test_impl_from_usize_max() {
		use super::FromUsize;
		assert_eq!(<u128 as FromUsize>::MAX, usize::MAX);
		assert_eq!(<i128 as FromUsize>::MAX, usize::MAX);
	}
}
