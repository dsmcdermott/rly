// This module contains the GrammarRules struct, which is responsable for storing and
// organising information about the rules of a particular grammar for use in building
// parser tables. In particular it provides the right-hand-sides of a given non-terminal
// with the method 'get' and it is responsable for generating and providing the first sets
// for symbols. It also provides the symbols used for 'start' and 'eof'.

use std::{
	boxed::Box,
	collections::{HashMap, HashSet, VecDeque},
};

use super::grammar_rule_structures::{GrammarRule, Prim, Symbol};

use super::table_construction::{Table, TableBuilder};

#[derive(Debug)]
pub struct GrammarRules<N: Prim, T: Prim> {
	rules: HashMap<N, Vec<Box<[Symbol<N, T>]>>>,
	firsts: HashMap<N, HashSet<T>>,
	start: N,
	eof: T,
}

impl<N: Prim, T: Prim> GrammarRules<N, T> {
	// Converts an iterator of GrammarRule's into a mapping from non-terms to
	// right-hand-sides. It then uses this mapping to create a new GrammarRules with an
	// empty 'firsts', then calls 'gen_first_sets' on that instance, populating the
	// 'firsts' field.
	pub fn new<I>(iter: I, start: N, eof: T) -> Self
	where
		I: IntoIterator<Item = GrammarRule<N, T>>,
	{
		let mut rules = HashMap::new();
		for rule in iter {
			let (lhs, rhs) = rule.into_pair();
			let entry = rules.entry(lhs).or_insert_with(|| Vec::new());
			entry.push(rhs.into_boxed_slice());
		}
		let mut rules = Self {
			rules,
			firsts: HashMap::new(),
			start,
			eof,
		};
		rules.gen_first_sets();
		rules
	}

	// Returns the firsts for the symbol 'lhs' corresponding to those rules where the
	// first symbol on the right-hand-side is a terminal.
	fn firsts_basic(&self, lhs: &N) -> HashSet<T> {
		self.rules
			.get(lhs)
			.unwrap()
			.iter()
			.filter_map(|rhs| rhs[0].as_term())
			.collect()
	}

	fn gen_first_sets(&mut self) {
		// Creates a deque of non-terms, collecting their immediate firsts (see
		// firsts_basic) in the process
		let mut deq = VecDeque::new();
		for key in self.rules.keys().copied() {
			self.firsts.insert(key, self.firsts_basic(&key));
			deq.push_front(key);
		}

		loop {
			// Pops a non-term 'lhs' from the deque. Breakes the loop if empty.
			let lhs = match deq.pop_front() {
				Some(sym) => sym,
				None => break,
			};

			// Adds the firsts for each non-term that appears at the beginning of a rule
			// for lhs. If any new firsts were added, or if the set of firts for lhs is
			// still empty, lhs is pushed to the back of the deque to be processed again
			// later.
			let mut is_complete = true;
			let mut set = self.firsts.remove(&lhs).unwrap();
			self.update_firsts(&lhs, &mut set, &mut is_complete);
			is_complete &= !set.is_empty();
			self.firsts.insert(lhs, set);
			if !is_complete {
				deq.push_back(lhs);
			};
		}
	}

	pub fn firsts(&self) -> &HashMap<N, HashSet<T>> {
		&self.firsts
	}

	pub fn start(&self) -> &N {
		&self.start
	}

	pub fn eof(&self) -> &T {
		&self.eof
	}

	// Adds to 'set' all the known firsts of each non-term that appears at the beginning
	// of some rule for 'lhs', setting 'is_complete' to false if any new terminals are
	// added.
	fn update_firsts(&self, lhs: &N, set: &mut HashSet<T>, is_complete: &mut bool) {
		self.rules
			.get(lhs)
			.unwrap()
			.iter()
			.filter_map(|rhs| rhs[0].as_non_term())
			.filter(|sym| sym != lhs)
			.flat_map(|sym| self.firsts.get(&sym).unwrap())
			.copied()
			.for_each(|sym| {
				*is_complete &= set.insert(sym);
			});
	}

	// Returns a slice of righ-hand-sides for each rule that has 'lhs' as its
	// left-hand-side.
	pub fn get(&self, lhs: &N) -> &[Box<[Symbol<N, T>]>] {
		self.rules.get(lhs).unwrap().as_slice()
	}

	pub fn table_builder(&self) -> TableBuilder<'_, N, T> {
		TableBuilder::new(&self)
	}

	pub fn build_tables(&self) -> Vec<Table<'_, N, T>> {
		self.table_builder().return_tables()
	}
}

#[cfg(test)]
pub mod tests {

	mod test_grammar_rules {
		use crate::grammar_rule_structures as grs;
		use grs::{Prim, Symbol};
		use std::fmt;

		trait IntoSym<S: Prim, T: Prim> {
			fn into_sym(self) -> Symbol<S, T>;
		}

		impl<'s, T: Prim> IntoSym<&'s str, T> for &'s str {
			fn into_sym(self) -> Symbol<&'s str, T> {
				grs::Symbol::NonTerm(self)
			}
		}

		#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
		pub enum Term {
			Int,
			Id,
			Plus,
			Mul,
			EOF,
		}
		use Term::*;

		impl fmt::Display for Term {
			fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
				let s = match self {
					Int => "int",
					Id => "id",
					Plus => "+",
					Mul => "*",
					EOF => "$",
				};
				write!(f, "{}", s)
			}
		}

		impl<S: Prim> IntoSym<S, Term> for Term {
			fn into_sym(self) -> Symbol<S, Self> {
				Symbol::Term(self)
			}
		}

		macro_rules! grammar_rule {
			( $lhs : expr, $($rhs : expr),+ ) => { grs::grammar_rule($lhs, vec![$($rhs.into_sym()),*]) };
		}

		pub fn test_rules() -> Vec<grs::GrammarRule<&'static str, Term>> {
			vec![
				grammar_rule!["start", "sum"],
				grammar_rule!["sum", "sum", Plus, "prod"],
				grammar_rule!["sum", "prod"],
				grammar_rule!["prod", "prod", Mul, "term"],
				grammar_rule!["prod", "term"],
				grammar_rule!["term", Int],
				grammar_rule!["term", Id],
			]
		}

		#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
		pub enum AltTerm {
			LParen,
			RParen,
			Add,
			Num,
			AEOF,
		}
		use AltTerm::*;

		impl fmt::Display for AltTerm {
			fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
				let s = match self {
					LParen => "(",
					RParen => ")",
					Add => "+",
					Num => "n",
					AEOF => "$",
				};
				write!(f, "{}", s)
			}
		}

		impl<S: Prim> IntoSym<S, AltTerm> for AltTerm {
			fn into_sym(self) -> Symbol<S, Self> {
				Symbol::Term(self)
			}
		}

		pub fn alt_test_rules() -> Vec<grs::GrammarRule<&'static str, AltTerm>> {
			vec![
				grammar_rule!["start", "expr"],
				grammar_rule!["expr", "factor"],
				grammar_rule!["expr", LParen, "expr", RParen],
				grammar_rule!["factor", Num],
				grammar_rule!["factor", Add, "factor"],
				grammar_rule!["factor", "factor", Add, Num],
			]
		}
	}

	pub use test_grammar_rules::{alt_test_rules, test_rules, AltTerm, Term};

	pub fn test_gr() -> super::GrammarRules<&'static str, Term> {
		super::GrammarRules::new(test_rules(), "start", Term::EOF)
	}

	pub fn alt_test_gr() -> super::GrammarRules<&'static str, AltTerm> {
		super::GrammarRules::new(alt_test_rules(), "start", AltTerm::AEOF)
	}

	#[test]
	fn test_new_gr() {
		let rules = test_gr();
		for (k, v) in rules.rules.iter() {
			println!("{:?}: {:?}", k, v);
		}
	}

	#[test]
	fn test_first_sets() {
		let rules = test_gr();
		let firsts = rules.firsts();
		println!("{:?}", firsts);
	}
}
