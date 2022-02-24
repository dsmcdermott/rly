// This module contains the TableBuilder struct, which is responsable for actually
// building the LR1 parser tables. It also contains the Table datatype, representing an
// LR1 table.
//
// Tables are built using a 'merge-as-you-go' strategy: As soon as a table is fully
// generated, the TableBuilder attempts to merge it with a previously finished table. If
// it is unable to do so, the table is added to the list of finished tables. This produces
// the same result as if you generated all the tables first and then merged them, but uses
// much less memory.
//
// For grammars which are LALR, this process results in the normal set of LALR tables. For
// grammars which are not LALR, this results in a hybrid between the full, un-merged,
// LR(1) table set and an LALR table set, where the tables that would introduce
// reduce-reduce conflicts are not merged.

use std::{
	collections::{HashMap, HashSet, VecDeque},
	ops::Deref,
};

use super::grammar_rule_structures::{Item, LR0Item, Prim, Symbol};
use super::grammar_rules::GrammarRules;

// This struct represents LR(1) tables. 'number' is initially None, but is set once it has
// been determined that the table cannot be merged. 'transitions' records the transitions
// for the table, mapping Symbol's to 'number's.
#[derive(Debug, PartialEq, Eq)]
pub struct Table<'a, N: Prim, T: Prim> {
	number: Option<usize>,
	kernel_items: HashSet<Item<'a, N, T>>,
	closure_items: HashSet<Item<'a, N, T>>,
	transitions: HashMap<Symbol<N, T>, usize>,
}

mod table_display {
	use super::{Prim, Table};
	use std::fmt::{Arguments, Display, Formatter, Result as FmtResult};

	fn id<T>(t: T) -> T {
		t
	}

	impl<'a, N: Prim + Display, T: Prim + Display> Display for Table<'a, N, T> {
		fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
			self.display_items(|arg| write!(f, "{}\n", arg), id, id)
		}
	}

	macro_rules! farg {
		($arg: expr) => {
			format_args!("{}", $arg)
		};
	}

	// Formats and writes the components of a table. 'f' is a closure that writes a line
	// to the desired output (which may be a String or an fmt::Formatter, not just an IO
	// object.) 'display_n' and 'display_t' format non-terminals and terminals,
	// respectively, for printing.
	//
	// The lines are printed according to the general format:
	// {num}.
	// kernel:
	// \t{item}
	// ...
	// closure:
	// \t{item}
	// ...
	// transitions:
	// \t{sym} -> {transitions.get(&sym)}
	// ...
	//
	// For example, if you wanted to write a table to the writer 'fout' with an
	// indentation of 'indent' spaces, you could use:
	// table.display_items(|arg| write!(fout, "{:n}{}\n", " ", arg, n = indent), id, id)
	// (Assuming N and T implement Display)

	impl<'a, N: Prim, T: Prim> Table<'a, N, T> {
		pub fn display_items<'b, F, G, H, D, L, E>(
			&'b self,
			mut f: F,
			display_n: G,
			display_t: H,
		) -> Result<(), E>
		where
			F: FnMut(Arguments<'_>) -> Result<(), E>,
			G: Fn(&'b N) -> D,
			H: Fn(&'b T) -> L,
			D: Display,
			L: Display,
		{
			f(format_args!("{}.", self.number()))?;
			f(farg!("kernel:"))?;
			for item in self.kernel() {
				f(format_args!(
					"\t{}*",
					item.displayer(&display_n, &display_t)
				))?;
			}
			f(farg!("closure:"))?;
			for item in self.closure() {
				f(format_args!("\t{}", item.displayer(&display_n, &display_t)))?;
			}
			f(farg!("transitions:"))?;
			for (sym, num) in self.transitions.iter() {
				sym.display_with(
					|arg| f(format_args!("\t{} -> {}", arg, num)),
					&display_n,
					&display_t,
				)?;
			}
			Ok(())
		}
	}
}

impl<'a, N: Prim, T: Prim> Table<'a, N, T> {
	// Creates a new table with empty number, closure, and transitions.
	fn from_kernel(kernel_items: HashSet<Item<'a, N, T>>) -> Self {
		Self {
			number: None,
			kernel_items,
			closure_items: HashSet::new(),
			transitions: HashMap::new(),
		}
	}

	fn kernel(&self) -> &HashSet<Item<'a, N, T>> {
		&self.kernel_items
	}

	fn closure(&self) -> &HashSet<Item<'a, N, T>> {
		&self.closure_items
	}

	fn kernel_mut(&mut self) -> &mut HashSet<Item<'a, N, T>> {
		&mut self.kernel_items
	}

	fn closure_mut(&mut self) -> &mut HashSet<Item<'a, N, T>> {
		&mut self.closure_items
	}

	// Adds 'item' to self.kernel, removing it from self.closure if it was present there.
	// Returns false if self already contained the item.
	fn add_item_kernel(&mut self, item: Item<'a, N, T>) -> bool {
		let mut is_new = self.kernel_mut().insert(item);
		if is_new {
			is_new &= !self.closure_mut().remove(&item);
		};
		is_new
	}

	// Extends self.kernel with the items in 'iter', returning a Vec of newly added
	// nonterminal items if there were any.
	//
	// If an item in 'iter' was not in self.kernel but was in self.closure, it is moved.
	fn extend_kernel<I>(&mut self, iter: I) -> Option<VecDeque<Item<'a, N, T>>>
	where
		I: IntoIterator<Item = Item<'a, N, T>>,
	{
		let mut new_non_redc = None;
		for item in iter {
			let is_new = self.add_item_kernel(item);
			if is_new && !item.is_terminal() {
				new_non_redc
					.get_or_insert_with(|| VecDeque::new())
					.push_back(item);
			};
		}
		new_non_redc
	}

	pub fn number(&self) -> usize {
		self.number.unwrap()
	}

	fn number_mut(&mut self) -> &mut Option<usize> {
		&mut self.number
	}

	// Sets self.number from None to 'num'
	fn update_num(&mut self, num: usize) {
		debug_assert!(self.number_mut().is_none());
		let _ = self.number_mut().insert(num);
	}

	// Adds 'item' to self. Returns true if self did not contain 'item', false otherwise,
	// just like a HashSet.
	//
	// If 'item' is in self.kernel(), it's not added. This ensures that no items in
	// self.closure() are also in self.kerne()
	fn add_item(&mut self, item: Item<'a, N, T>) -> bool {
		if self.is_kernel(&item) {
			false
		} else {
			self.closure_mut().insert(item)
		}
	}

	// Adds 'item' to self.kernel
	fn add_core_item(&mut self, item: Item<'a, N, T>) -> bool {
		self.kernel_mut().insert(item)
	}

	fn is_kernel(&self, item: &Item<'a, N, T>) -> bool {
		self.kernel().contains(item)
	}

	// Returns a HashSet of the core (LR(0)) items in self's kernel
	fn core(&self) -> HashSet<&LR0Item<'a, N, T>> {
		self.kernel().iter().map(|i| i.core()).collect()
	}

	// Checks for reduce/reduce conflicts. Assumes that self and other have the same core
	// (LR(0)) items in their kernels.
	fn check_no_reduce_conflicts(&self, other: &Self) -> bool {
		other
			.kernel()
			.iter()
			.filter(|item| item.is_terminal())
			.all(|item| self.kernel().contains(item))
	}

	// Attempts to merge self with other. If self and other can be merged, this method
	// does so and returns Err(self.num). Otherwise self is unchanged and it returns Ok(other).
	//
	// (This returns Err when the merge is successfull, and Ok when not, to make use of
	// '?' for propagating the results of a successfull merge and short-circuiting
	// searches for merging candidates.)
	//
	// Does not check for closure reductions on rules with empty productions.
	fn attempt_merge(&mut self, other: Self) -> Result<Self, usize> {
		if self.core() == other.core() && self.check_no_reduce_conflicts(&other) {
			let num = self.number();
			for item in other.kernel_items {
				self.add_core_item(item);
			}
			for item in other.closure_items {
				self.add_item(item);
			}
			Err(num)
		} else {
			Ok(other)
		}
	}

	fn add_transition(&mut self, sym: Symbol<N, T>, num: usize) {
		self.transitions.insert(sym, num);
	}

	fn get_transition(&self, sym: &Symbol<N, T>) -> Option<usize> {
		self.transitions.get(sym).map(|n| *n)
	}

	fn reduction_fixes(&self) -> Vec<(usize, Vec<Item<'a, N, T>>)> {
		let mut fixes = HashMap::new();
		for item in self.iter() {
			if !item.is_terminal() {
				let sym = item.current().unwrap();
				fixes
					.entry(sym)
					.or_insert_with(|| Vec::new())
					.push(item.increment());
			}
		}
		fixes
			.drain()
			.map(|(sym, vec)| (self.get_transition(sym).unwrap(), vec))
			.collect()
	}

	// Returns the actions of self as a tuple of (shifts, reductions, gotos). Shifts and
	// gotos are tuples of a symble and table num, while reductions are tuples of a
	// lookahead and a tuple of the left-hand-side of the production rule and the length
	// of the right-hand-side minus 1 (which is the number of elements left to be
	// collected for the rule after the element on top of the stack has been poped.)
	pub fn actions(&self) -> (Vec<(T, usize)>, Vec<(T, (N, usize))>, Vec<(N, usize)>) {
		let mut shifts = Vec::new();
		let mut gotos = Vec::new();
		let mut reductions = Vec::new();
		for (sym, i) in self.transitions.iter() {
			match sym {
				Symbol::NonTerm(n) => gotos.push((*n, *i)),
				Symbol::Term(t) => shifts.push((*t, *i)),
			};
		}
		for rule in self.iter() {
			if rule.is_terminal() {
				reductions.push((*rule.look_ahead(), (*rule.lhs(), rule.len() - 1)));
			};
		}
		(shifts, reductions, gotos)
	}
}

// Provides the method 'iter' for Table, which returns an iterator over the Items of that
// table.
mod table_iter {
	use super::{Item, Prim, Table};
	use std::{collections::hash_set::Iter, iter::Chain};

	impl<'a, N: Prim, T: Prim> Table<'a, N, T> {
		pub fn iter(&self) -> Chain<Iter<'_, Item<'a, N, T>>, Iter<'_, Item<'a, N, T>>> {
			self.kernel().iter().chain(self.closure().iter())
		}
	}
}

// A struct that builds a complete set of Table's for a GrammarRules.
//
// 'tables' is the queue of generated tables waiting to have their transitions generated.
// 'finished_tables' is the list of tables that have been fully processed. 'table_num' is
// the counter for generating new numbers for Table's.
#[derive(Debug)]
pub struct TableBuilder<'a, N: Prim, T: Prim> {
	rules: &'a GrammarRules<N, T>,
	tables: VecDeque<Table<'a, N, T>>,
	finished_tables: Vec<Table<'a, N, T>>,
	table_num: usize,
}

impl<'a, N: Prim, T: Prim> TableBuilder<'a, N, T> {
	// Creates and initializes a new TableBuilder for 'rules', generating a single initial
	// table for the rule for "Start".
	pub(crate) fn new(rules: &'a GrammarRules<N, T>) -> Self {
		let mut builder = Self {
			rules,
			tables: VecDeque::new(),
			finished_tables: Vec::new(),
			table_num: 0,
		};
		debug_assert_eq!(builder.rules().get(builder.start()).len(), 1);
		let starting_rhs = &builder.rules().get(builder.start())[0];
		let starting_item = Item::new_init(*builder.start(), starting_rhs, *builder.eof());
		let mut starting_table = builder.gen_table([starting_item]);
		builder.update_num(&mut starting_table);
		builder.push_table(starting_table);
		builder
	}

	pub fn rules(&self) -> &'a GrammarRules<N, T> {
		&self.rules
	}

	fn push_table(&mut self, table: Table<'a, N, T>) {
		self.tables.push_front(table)
	}

	fn pop_table(&mut self) -> Option<Table<'a, N, T>> {
		self.tables.pop_back()
	}

	fn push_finished(&mut self, table: Table<'a, N, T>) {
		self.finished_tables.push(table)
	}

	fn start(&self) -> &N {
		self.rules.start()
	}

	fn eof(&self) -> &T {
		self.rules.eof()
	}

	fn update_num(&mut self, table: &mut Table<'a, N, T>) -> usize {
		let num = self.table_num;
		table.update_num(num);
		self.table_num += 1;
		num
	}

	// Generates a new table from a kernel 'kernel'
	//
	// Adds the closure item to the table but doesnt set the number and leaves the
	// transitions empty.
	//
	// Gets called by process_table, which merges the created table or adds a num and then
	// pushes the table to the back of self.tables.
	fn gen_table<I>(&mut self, kernel: I) -> Table<'a, N, T>
	where
		I: IntoIterator<Item = Item<'a, N, T>>,
	{
		let mut kernel_items = HashSet::new();
		let mut items = VecDeque::new();
		for item in kernel {
			kernel_items.insert(item);
			items.push_back(item);
		}
		let mut table = Table::from_kernel(kernel_items);
		fill_table(self.rules(), &mut table, items);
		table
	}

	// Attempts to merge 'new_table' into a previously generated table, including
	// self.finished_tables, self.tables, and 'current_table' which is the table currently
	// being processed by process_table. If 'new_table' can be merged, the function
	// returns Err(num), where 'num' is the num of the table it was merged into. Otherwise
	// it returns Ok(new_table).
	fn merge_table(
		&mut self,
		current_table: &mut Table<'a, N, T>,
		mut new_table: Table<'a, N, T>,
	) -> Result<Table<'a, N, T>, usize> {
		let iter = std::iter::once(current_table)
			.chain(self.finished_tables.iter_mut())
			.chain(self.tables.iter_mut());
		for table in iter {
			new_table = table.attempt_merge(new_table)?;
		}
		Ok(new_table)
	}

	// Attempts to merge the table 'new' into a previously generated table, returning
	// either the num of the table it was merged into, or pushing 'new' onto self.tables
	// and assigning it a new number and returning that. Either way the return value is a
	// number that can be used to refer to 'new'.
	//
	// 'current' is the table currently being processed and is a candidate for merging.
	fn add_table(&mut self, current: &mut Table<'a, N, T>, new: Table<'a, N, T>) -> usize {
		match self.merge_table(current, new) {
			Ok(mut table) => {
				let num = self.update_num(&mut table);
				self.push_table(table);
				num
			}
			Err(num) => num,
		}
	}

	// Pops a table from the front of self.tables and processes it, generating and filling
	// in its transitions before pushing the finished table onto self.finished_tables.
	// This process may generate additional tables to be processed, which are then pushed
	// to the back of self.tables.
	//
	// If self.tables is empty, the function returns false, otherwise it returns true,
	// indicating that there is still processing to be done.
	fn process_table(&mut self) -> bool {
		let mut table = match self.pop_table() {
			Some(table) => table,
			None => {
				return false;
			}
		};
		let mut nexts = HashMap::new();
		for item in table.iter() {
			if let Some(n) = item.current() {
				let entry = nexts.entry(*n).or_insert_with(|| Vec::new());
				entry.push(item.increment());
			};
		}
		for (sym, items) in nexts.drain() {
			let new_table = self.gen_table(items.into_iter());
			let num = self.add_table(&mut table, new_table);
			table.add_transition(sym, num);
		}
		self.push_finished(table);
		true
	}

	// Builds a set of tables by repeatedly calling self.process_table.
	//
	// TableBuilder's are created by TableBuilder::new() with a single table in the
	// 'tables' queue, representing the table for the "Start" rule. Calling this method
	// will then populate self.finished_tables with the complete set of LR(1) tables,
	// leaving self.tables empty.
	//
	// When self.tables is empty, the method does nothing.
	fn build_tables(&mut self) {
		while self.process_table() {}
		debug_assert!(self.tables.is_empty());
	}

	// Adds the items in 'new_items' to the kernel of self.finished_tables[num], then
	// re-calculates the closure.
	//
	// Returns true if new non-terminal items were added to self.finished_tables[num]
	fn fix_reductions_with(&mut self, num: usize, new_items: Vec<Item<'a, N, T>>) -> bool {
		let newly_added = self.finished_tables[num].extend_kernel(new_items);
		match newly_added {
			Some(deque) => {
				fill_table(self.rules(), &mut self.finished_tables[num], deque);
				true
			}
			None => false,
		}
	}

	fn fix_reductions(&mut self) {
		debug_assert!(self
			.finished_tables
			.iter()
			.enumerate()
			.all(|(n, table)| n == table.number()));
		let len = self.finished_tables.len();
		let mut fixes = VecDequeSet::from_iter(0..len);
		loop {
			let i = match fixes.pop() {
				Some(i) => i,
				None => break,
			};
			let reduction_fixes = self.finished_tables[i].reduction_fixes();
			for (num, new_items) in reduction_fixes {
				if self.fix_reductions_with(num, new_items) {
					fixes.push(num);
				};
			}
		}
	}

	pub fn return_tables(mut self) -> Vec<Table<'a, N, T>> {
		self.build_tables();
		self.fix_reductions();
		self.finished_tables
	}
}

// Processes the closure items for 'table' genereated by 'items'.
//
// Gets called by gen_table and fix_reductions.
fn fill_table<'a, N: Prim, T: Prim>(
	rules: &'a GrammarRules<N, T>,
	table: &mut Table<'a, N, T>,
	mut items: VecDeque<Item<'a, N, T>>,
) {
	loop {
		let item = match items.pop_front() {
			Some(item) => item,
			_ => break,
		};
		let lhs = match item.current() {
			Some(Symbol::NonTerm(n)) => n,
			_ => continue,
		};
		let bodies = rules.get(lhs);
		let mut add = |la| {
			for rhs in bodies {
				let item = Item::new_init(*lhs, rhs.deref(), la);
				if table.add_item(item) {
					items.push_back(item);
				};
			}
		};
		match follows(rules, &item) {
			Follows::Term(la) => add(la),
			Follows::NonTerm(set) => {
				for la in set {
					add(*la);
				}
			}
		};
	}
}

struct VecDequeSet {
	deque: VecDeque<usize>,
	set: HashSet<usize>,
}

impl VecDequeSet {
	fn pop(&mut self) -> Option<usize> {
		let t = self.deque.pop_front()?;
		assert!(self.set.remove(&t));
		Some(t)
	}

	fn push(&mut self, n: usize) -> bool {
		if self.set.insert(n) {
			self.deque.push_back(n);
			true
		} else {
			false
		}
	}

	fn from_iter<I: IntoIterator<Item = usize>>(iter: I) -> Self {
		let iter = iter.into_iter();
		let (lower, uper) = iter.size_hint();
		let size = uper.unwrap_or(lower);
		let mut ds = Self {
			deque: VecDeque::with_capacity(size),
			set: HashSet::with_capacity(size),
		};
		for t in iter {
			ds.push(t);
		}
		ds
	}
}

//fn add_items<'a, N, T>(
//	lhs: N,
//	bodies: &'a [Box<[Symbol<N, T>]>],
//	la: T,
//	items: &mut VecDeque<Item<'a, N, T>>,
//	table: &mut Table<'a, N, T>)
//where
//	N: Prim,
//	T: Prim,
//{
//}

enum Follows<'r, T: Prim> {
	NonTerm(&'r HashSet<T>),
	Term(T),
}

// Returns the Follows for an Item. If item.follow() is a terminal, returns that
// terminal, otherwise returns the follow set for the non-terminal.
fn follows<'a, N: Prim, T: Prim>(
	rules: &'a GrammarRules<N, T>,
	item: &Item<'a, N, T>,
) -> Follows<'a, T> {
	match item.follow() {
		Symbol::Term(t) => Follows::Term(t),
		Symbol::NonTerm(n) => Follows::NonTerm(rules.firsts().get(&n).unwrap()),
	}
}

#[cfg(test)]
mod tests {
	use crate::grammar_rules::tests::{alt_test_gr, test_gr, test_rules, Term};

	#[test]
	fn test_new_builder() {
		let rules = test_gr();
		let builder = rules.table_builder();
		assert_eq!(builder.table_num, 1);
		assert_eq!(builder.tables.len(), 1);
		assert_eq!(builder.finished_tables.len(), 0);
		//		println!("{:?}", builder);
	}

	#[test]
	fn test_gen_table() {
		use crate::grammar_rule_structures::{Item, Symbol};
		use std::collections::HashSet;
		use Term::*;
		let rules = test_gr();
		let mut builder = rules.table_builder();
		builder.table_num = 0;
		let rhs: &[_] = &[Symbol::NonTerm("sum")];
		let kernel: [_; 1] = [Item::new_init("start", rhs, Term::EOF)];
		let mut table = builder.gen_table(kernel);
		assert_eq!(table.number, None);
		table.update_num(0);
		assert_eq!(table, builder.tables[0]);
		let super::Table {
			kernel_items: kernel,
			closure_items: closure,
			..
		} = table;
		//		println!("rules");
		//		for rule in test_rules() {
		//			println!("\t{}", rule);
		//		}
		let test_rules = test_rules();
		let f = |i, la| Item::from_rule(&test_rules[i], 0, la);
		let test_items = [
			f(1, EOF),
			f(2, EOF),
			f(1, Plus),
			f(2, Plus),
			f(3, EOF),
			f(4, EOF),
			f(3, Plus),
			f(4, Plus),
			f(3, Mul),
			f(4, Mul),
			f(5, Plus),
			f(6, Plus),
			f(5, Mul),
			f(6, Mul),
			f(5, EOF),
			f(6, EOF),
		];
		assert_eq!(closure, HashSet::from(test_items));
		assert_eq!(kernel, HashSet::from([f(0, EOF)]));
	}
}
