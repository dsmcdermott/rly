//! Types and traits for working with (abstract) syntax trees.
//!
//! This includes the enum [`AstNode`] and the struct [`Ast`], as well as traits such as
//! [`Walker`] for walking a tree.
//!
//! # `Ast`, `AstNode`, and (Abstract) Syntax Trees
//!
//! [Abstract syntax trees][wa] and [concrete syntax trees][wc] are represented through
//! [`Ast`] and [`AstNode`]. [`AstNode`] represents a node in a syntax tree, either a
//! [leaf](AstNode::Leaf) containing a terminal, or a [branch](AstNode::Branch) containing
//! an [`Ast`]. An instance of [`Ast`] represents a branch node in a syntax tree, with a
//! [label](Ast#label-and-children) and one or more [child](Ast#label-and-children)
//! [`AstNode`]'s.
//!
//! In an [`Ast<N, T>`], the generic types `N` and `T` recursively determine the type of
//! labels on branch nodes and the type of leaf nodes, respectively, on the tree as a
//! whole; the [label](Ast#name-and-label) of an [`Ast<N, T>`] is of type `N`, and the
//! children are of type [`AstNode<N, T>`], where the [leafs](AstNode::Leaf) of an
//! [`AstNode<N, T>`] are of type `T` and the [branches](AstNode::Branch) are of type
//! [`Ast<N, T>`]
//!
//! # Walking an Ast
//!
//! This module also contains facilities for recursively walking an [`Ast`]. These consist
//! of a single general pattern with three variations differing based on ownership:
//! borrowing, mutable borrowing, and consuming. For each degree of ownership, there are
//! two items:
//!
//! * A walker trait, containing three methods: `on_branch`, to be called when entering a
//! branch node, `on_leaf`, to be called on leaf nodes, and `exit`, to be called when
//! exiting a branch node.
//!
//! * And a walking iterator struct that adapts a Walker and implements Iterator by
//! recursively walking a tree and returning the results of calling the appropriate
//! methods on the Walker.
//!
//! The different items for each access type/role combo are illustrated on the following
//! table.
//!
//! |                    | Trait         | Iter Adapter       |
//! |--------------------|---------------|--------------------|
//! | **Borrowing**:     | [`Walker`]    | [`WalkerIter`]     |
//! | **Mut Borrowing**: | [`WalkerMut`] | [`WalkerIterMut`]  |
//! | **Consuming**:     | [`Consumer`]  | [`WalkerIntoIter`] |
//!
//! For the walker trait, the methods return options; if the returned variant is [`None`],
//! the iterator adapter will skip it and move on to the next node.[^branch_none]
//!
//! [^branch_none]: Note that the "next node" is the one it would have gone to on a
//! subsequent call to [`next`](Iterator::next). In other words, if `on_branch` returns
//! [`None`] on a node `n`, the iterator adapter will descend and move on to the first
//! child node of `n`, rather than going to the next sibling node. For skipping a branch
//! node _and_ all its descendants, see the next paragraph.
//!
//! The `on_branch` method is also used as a guard by returning a tuple where the second
//! item is a [`bool`][^consumer_branch]. If the [`bool`] is [`false`], the iterator
//! adapter does not descend for that branch, and skips to the next node under the current
//! parent branch[^returning].
//!
//! [^consumer_branch]: With a slight exception for [`Consumer`]. See the documentation
//! there and in the next section for more details.
//!
//! [^returning]: Note that the boolean value only controls whether or not the iterator
//! descends for that branch node; if the [`Option`] result is [`Some`], the iterator
//! still returns that result, and simply moves on to the next sibling node on the next
//! call to [`Iterator::next`].
//!
//!
//! ## Differences
//!
//! There are minor differences between the three variations, having to do with the
//! different constraints (or lack thereof) on the differeing degrees of ownership.
//! Namely:
//!
//! * For [`WalkerMut`], the mutable walker trait, all three methods accept an additional
//! `parent` parameter, which is a reference to the [`label`] of the parent node. This
//! helps alleviate the need for the [`WalkerMut`] to alias references to the [`label`]'s
//! to keep track of state.
//!
//! * For [`Consumer<A, T>`], the consuming walker trait, the method
//! [`on_branch`](Consumer::on_branch) takes ownership of the branch node and returns
//! `(Option<T>, Option<A>)` instead of `(Option<T>, bool)`. If the [`Option<A>`] is
//! [`None`], that node and its descendents are skipped, just like returning [`false`] for
//! the other traits. If the [`Option<A>`] is [`Some(ast)`], then the iterator adapter
//! ([`WalkerIntoIter`]) recursively descends along that tree.
//!
//! * For [`Walker`], the borrowing walking trait, the method [`exit`](Walker::exit) takes
//! a reference to the branch node as a whole, while the other two traits only act on the
//! [`label`] of the branch being exited.
//
//  # Iterating Over an `Ast`
//
//!
//!
//! [wc]: https://en.wikipedia.org/wiki/Parse_tree
//! [wa]: https://en.wikipedia.org/wiki/Abstract_syntax_tree
//! [`label`]: Ast#label-and-children

use std::default::Default;

/// A node in an [(abstract) syntax tree](self#ast-astnode-and-abstract-syntax-trees).
///
/// `T` is the type of [Leaf](Self::Leaf) variants, and [`Branch`](Self::Branch) are of
/// type [`Ast<N, T>`].
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum AstNode<N, T> {
	/// A branch node in a [syntax tree](self#ast-astnode-and-abstract-syntax-trees)
	Branch(Ast<N, T>),

	/// A leaf node in a [syntax tree](self#ast-astnode-and-abstract-syntax-trees)
	Leaf(T),
}

impl<N, T> AstNode<N, T> {
	/// Converts `self` into an [`Option`], returning [`Some`] if `self` is a
	/// [`Branch`][var] and [`None`] otherwise.
	///
	/// [var]: Self::Branch
	pub fn branch(self) -> Option<Ast<N, T>> {
		match self {
			Self::Branch(a) => Some(a),
			_ => None,
		}
	}

	/// Converts `self` into an [`Option`], returning [`Some`] if `self` is a
	/// [`Leaf`][var] and [`None`] otherwise.
	///
	/// [var]: Self::Leaf
	pub fn leaf(self) -> Option<T> {
		match self {
			Self::Leaf(l) => Some(l),
			_ => None,
		}
	}

	/// Returns [`true`] if self is a [`Branch`][var].
	///
	/// [var]: Self::Branch
	pub fn is_branch(&self) -> bool {
		self.by_ref().is_branch()
	}

	/// Returns [`true`] if self is a [`Leaf`][var].
	///
	/// [var]: Self::Leaf
	pub fn is_leaf(&self) -> bool {
		self.by_ref().is_leaf()
	}

	/// Adapts `self` by borrowing its contents, returning a [`RefNode`].
	pub fn by_ref(&self) -> RefNode<'_, N, T> {
		match self {
			Self::Branch(b) => RefNode::Branch(b),
			Self::Leaf(l) => RefNode::Leaf(l),
		}
	}

	/// Adapts `self` by mutably borrowing its contents, returning a [`MutRefNode`].
	pub fn by_mut(&mut self) -> MutRefNode<'_, N, T> {
		match self {
			Self::Branch(b) => MutRefNode::Branch(b),
			Self::Leaf(l) => MutRefNode::Leaf(l),
		}
	}
}

/// A borrowing adapter for [`AstNode`].
///
/// Like [`AstNode`] except it borrows its contents instead of owning them. For the
/// mutable version of this enum, see [`MutRefNode`].
#[derive(Clone, Copy)]
pub enum RefNode<'a, N, T> {
	Branch(&'a Ast<N, T>),
	Leaf(&'a T),
}

impl<'a, N, T> RefNode<'a, N, T> {
	/// Converts `self` into an [`Option`], returning [`Some`] if `self` is a
	/// [`Branch`][var] and [`None`] otherwise.
	///
	/// [var]: Self::Branch
	pub fn branch(self) -> Option<&'a Ast<N, T>> {
		match self {
			Self::Branch(a) => Some(a),
			_ => None,
		}
	}

	/// Converts `self` into an [`Option`], returning [`Some`] if `self` is a
	/// [`Leaf`][var] and [`None`] otherwise.
	///
	/// [var]: Self::Leaf
	pub fn leaf(self) -> Option<&'a T> {
		match self {
			Self::Leaf(l) => Some(l),
			_ => None,
		}
	}

	/// Returns [`true`] if self is a [`Branch`][var].
	///
	/// [var]: Self::Branch
	pub fn is_branch(self) -> bool {
		self.branch().is_some()
	}

	/// Returns [`true`] if self is a [`Leaf`][var].
	///
	/// [var]: Self::Leaf
	pub fn is_leaf(self) -> bool {
		self.leaf().is_some()
	}
}

impl<'a, N, T> From<&'a AstNode<N, T>> for RefNode<'a, N, T> {
	fn from(node: &'a AstNode<N, T>) -> Self {
		node.by_ref()
	}
}

impl<'a, N, T> From<MutRefNode<'a, N, T>> for RefNode<'a, N, T> {
	fn from(node: MutRefNode<'a, N, T>) -> Self {
		use MutRefNode::*;
		match node {
			Branch(a) => Self::Branch(a),
			Leaf(a) => Self::Leaf(a),
		}
	}
}

impl<'a, 'b, N, T> From<&'a MutRefNode<'b, N, T>> for RefNode<'a, N, T> {
	fn from(node: &'a MutRefNode<'b, N, T>) -> Self {
		node.as_ref_node()
	}
}

/// A mutably borrowing adapter for [`AstNode`].
///
/// Like [`AstNode`] except it borrows its contents mutably instead of owning them. For
/// the non-mutable version of this enum, see [`RefNode`].
pub enum MutRefNode<'a, N, T> {
	Branch(&'a mut Ast<N, T>),
	Leaf(&'a mut T),
}

impl<'a, N, T> MutRefNode<'a, N, T> {
	pub fn as_ref_node(&self) -> RefNode<'_, N, T> {
		match self {
			Self::Branch(a) => RefNode::Branch(*a),
			Self::Leaf(a) => RefNode::Leaf(*a),
		}
	}

	/// Returns [`true`] if self is a [`Branch`][var].
	///
	/// [var]: Self::Branch
	pub fn is_branch(&self) -> bool {
		self.as_ref_node().is_branch()
	}

	/// Returns [`true`] if self is a [`Leaf`][var].
	///
	/// [var]: Self::Leaf
	pub fn is_leaf(&self) -> bool {
		self.as_ref_node().is_leaf()
	}

	/// Converts `self` into an [`Option`], returning [`Some`] if `self` is a
	/// [`Branch`][var] and [`None`] otherwise.
	///
	/// [var]: Self::Branch
	pub fn branch(self) -> Option<&'a mut Ast<N, T>> {
		match self {
			Self::Branch(a) => Some(a),
			_ => None,
		}
	}

	/// Converts `self` into an [`Option`], returning [`Some`] if `self` is a
	/// [`Leaf`][var] and [`None`] otherwise.
	///
	/// [var]: Self::Leaf
	pub fn leaf(self) -> Option<&'a mut T> {
		match self {
			Self::Leaf(l) => Some(l),
			_ => None,
		}
	}
}

impl<'a, N, T> From<&'a mut AstNode<N, T>> for MutRefNode<'a, N, T> {
	fn from(node: &'a mut AstNode<N, T>) -> Self {
		node.by_mut()
	}
}

/// This is the trait for [branch nodes in a (abstract) syntax
/// tree](self#ast-astnode-and-abstract-syntax-trees).
///
/// The generic types `N` and `T` determine the nature of the full tree rooted at any
/// given instance of [`Ast<N, T>`]: `N` determines the labels used for branch nodes (i.e.
/// the non-terminal symbols,) typically an enum of some kind, and `T` determines the
/// contents of the leaf nodes, typically, but not necessarily, [`Token<'_,
/// K>`](lex::Token) for some choice of terminal discriminant `K`.
///
/// # Label and Children
///
/// Generally speaking, there are two components to an [`Ast<N, T>`]: The `label`, which
/// is an instance of `N` and describes what kind of branch node `self` is, and the
/// `children`, which is a [vec][`Vec`] of [`AstNode<N, T>`] representing the child nodes
/// to `self`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Ast<N, T> {
	label: N,
	children: Vec<AstNode<N, T>>,
}

impl<N, T> Ast<N, T> {
	/// Returns a reference to the [`label`](Ast#label-and-children) of `self`.
	pub fn label(&self) -> &N {
		&self.label
	}

	/// Returns a mutable reference to the [`label`](Ast#label-and-children) of `self`.
	pub fn label_mut(&mut self) -> &mut N {
		&mut self.label
	}

	/// Consumes `self` and returns the [`label`](Ast#label-and-children).
	pub fn into_label(self) -> N {
		self.label
	}

	/// Returns a reference to the [`children`](Ast#label-and-children) of `self`.
	pub fn children(&self) -> &[AstNode<N, T>] {
		&self.children
	}

	/// Returns a mutable referenct to the [`children`](Ast#label-and-children) of `self.
	pub fn children_mut(&mut self) -> &mut Vec<AstNode<N, T>> {
		&mut self.children
	}

	/// Consumes `self` and returns the [`children`](Ast#label-and-children).
	pub fn into_children(self) -> Vec<AstNode<N, T>> {
		self.children
	}

	/// Returns a reference to the [`label`][comps] and [`children`][comps] of `self`.
	///
	/// [comps]: Ast#label-and-children
	pub fn components(&self) -> (&N, &[AstNode<N, T>]) {
		(&self.label, &self.children)
	}

	/// Returns a mutable reference to the [`label`][comps] and [`children`][comps] of
	/// `self`.
	///
	/// [comps]: Ast#label-and-children
	pub fn components_mut(&mut self) -> (&mut N, &mut Vec<AstNode<N, T>>) {
		(&mut self.label, &mut self.children)
	}

	/// Consumes `self` the [`label`][comps] and [`children`][comps].
	///
	/// [comps]: Ast#label-and-children
	pub fn into_components(self) -> (N, Vec<AstNode<N, T>>) {
		(self.label, self.children)
	}

	/// Takes a [`Walker`] and returns a [`WalkerIter`] for [walking
	/// `self`](self#walking-and-ast).
	pub fn walk<'a, W, R>(&'a self, walker: W) -> WalkerIter<'a, N, T, R, W>
	where
		W: Walker<'a, N, T, R>,
	{
		WalkerIter::new(self, walker)
	}

	/// Like [`walk`](Ast::walk) but uses the default value of `W`.
	pub fn walk_default<'a, W, R>(&'a self) -> WalkerIter<'a, N, T, R, W>
	where
		W: Walker<'a, N, T, R> + Default,
	{
		self.walk(W::default())
	}

	/// Takes a [`WalkerMut`] and returns a [`WalkerIterMut`] for [mutably walking
	/// `self`](self#walking-and-ast).
	pub fn walk_mut<'a, W, R>(&'a mut self, walker: W) -> WalkerIterMut<'a, N, T, R, W>
	where
		W: WalkerMut<'a, N, T, R>,
	{
		WalkerIterMut::new(self, walker)
	}

	/// Like [`walk_mut`](Ast::walk_mut) but uses the default value of `W`.
	pub fn walk_mut_default<'a, W, R>(&'a mut self) -> WalkerIterMut<'a, N, T, R, W>
	where
		W: WalkerMut<'a, N, T, R> + Default,
	{
		self.walk_mut(W::default())
	}

	/// Takes a [`Consumer`] and returns a [`WalkerIntoIter`] for [walking `self` while
	/// taking ownership of the nodes](self#walking-and-ast).
	pub fn consume<C, R>(self, consumer: C) -> WalkerIntoIter<N, T, R, C>
	where
		C: Consumer<N, T, R>,
	{
		WalkerIntoIter::new(self, consumer)
	}

	/// Like [`consume`](Ast::consume) but uses the default value of `W`.
	pub fn consume_default<C, R>(self) -> WalkerIntoIter<N, T, R, C>
	where
		C: Consumer<N, T, R> + Default,
	{
		self.consume(C::default())
	}

	/// Creates a new instance of `Self` with the given [`label`][comps] and
	/// [`children`][comps]
	///
	/// [comps]: Ast#label-and-children
	pub fn new(label: N, children: Vec<AstNode<N, T>>) -> Self {
		Self { label, children }
	}

	/// Pushes a new [node](AstNode) onto the end of the
	/// [`children`](Ast#label-and-children) of `self`.
	pub fn push(&mut self, node: AstNode<N, T>) {
		self.children_mut().push(node);
	}

	/// Pushes a new branch [node](AstNode) onto the end of the
	/// [`children`](Ast#label-and-children) of `self`.
	///
	/// Equivalent to [`self.push(AstNode::Branch(branch)`](Self::push).
	pub fn push_branch(&mut self, branch: Self) {
		self.push(AstNode::Branch(branch))
	}

	/// Pushes a new leaf [node](AstNode) onto the end of the
	/// [`children`](Ast#label-and-children) of `self`.
	///
	/// Equivalent to [`self.push(AstNode::Leaf(leaf)`](Self::push).
	pub fn push_leaf(&mut self, leaf: T) {
		self.push(AstNode::Leaf(leaf))
	}

	/// Wraps `self` in a [`DisplayTree`] for printing.
	pub fn display(&self) -> DisplayTree<'_, N, T>
	where
		T: std::fmt::Display,
		N: std::fmt::Display,
	{
		DisplayTree::new(self)
	}

	/// Returns an iterator over references to the nodes of `self`.
	pub fn iter(&self) -> Iter<'_, N, T> {
		Iter::new(self)
	}

	/// Returns an iterator over mutable references to the [labels] and leafs of `self`.
	///
	/// [labels]: Ast#label-and-children
	pub fn iter_mut(&mut self) -> IterMut<'_, N, T> {
		IterMut::new(self)
	}

	/// Returns an iterator over the [labels] and leafs of `self`.
	///
	/// [labels]: Ast#label-and-children
	pub fn into_iter(self) -> IntoIter<N, T> {
		IntoIter::new(self)
	}
}

mod iter;

pub use iter::{
	AstElem, Consumer, IntoIter, Iter, IterMut, MutNode, Walker, WalkerIntoIter, WalkerIter,
	WalkerIterMut, WalkerMut,
};

mod display {
	// This module contains the DisplayTree struct, which is a wrapper struct for Ast's
	// that implements Display using Walker.
	//
	// Trees are formatted according to the format:
	//
	//     branch => ({branch label} {child}*)
	//     leaf   => {leaf}
	//

	use super::{Ast, Walker};
	use std::fmt::{Display, Formatter, Result};

	// the Walker for DisplayTree
	struct TreeFormatter<'a, 'b> {
		formatter: &'a mut Formatter<'b>,
	}

	impl<'a, 'b> TreeFormatter<'a, 'b> {
		fn write<T: Display>(&mut self, t: T) -> Result {
			write!(self.formatter, "{}", t)
		}
	}

	impl<'a, 'b, N, T> Walker<'a, N, T, Result> for TreeFormatter<'a, 'b>
	where
		T: Display,
		N: Display,
	{
		fn on_branch(&mut self, tree: &'a Ast<N, T>) -> (Option<Result>, bool) {
			(Some(self.write(format_args!(" ({}", tree.label()))), true)
		}

		fn on_leaf(&mut self, leaf: &'a T) -> Option<Result> {
			Some(self.write(format_args!(" {}", leaf)))
		}

		fn exit(&mut self, _tree: &'a Ast<N, T>) -> Option<Result> {
			Some(self.write(")"))
		}
	}

	/// A wrapper for an [`Ast`] that implements [`Display`] by recursively printing the
	/// labels of the branch node and the leaf nodes of its
	/// [tree](super#ast-astnode-and-abstract-syntax-trees)
	///
	/// Can be generated by [`new`](DisplayTree::new) or [`Ast::display`]
	///
	/// # Example
	///
	/// ```
	/// use parse::ast::{Ast, AstNode};
	///
	/// type Tree = Ast<String, u32>;
	///
	/// fn main() {
	/// 	let tree_repr = "(sum 1 (fact 2 3))";
	///
	/// 	let mut tree = Tree::new("sum".into(), [].into());
	///
	/// 	tree.push_leaf(1);
	/// 	tree.push_branch({
	/// 		let mut fact_tree = Tree::new("fact".into(), [].into());
	///
	/// 		fact_tree.push_leaf(2);
	/// 		fact_tree.push_leaf(3);
	/// 		fact_tree
	/// 	});
	///
	/// 	let displayed_tree = format!("{}", tree.display());
	/// 	assert_eq!(&displayed_tree, tree_repr);
	/// }
	/// ```
	pub struct DisplayTree<'a, N, T> {
		tree: &'a Ast<N, T>,
	}

	impl<'a, N, T> DisplayTree<'a, N, T>
	where
		T: Display,
		N: Display,
	{
		/// Wraps `tree` in a new [`DisplayTree`].
		pub fn new(tree: &'a Ast<N, T>) -> Self {
			Self { tree }
		}
	}

	impl<'a, N, T> Display for DisplayTree<'a, N, T>
	where
		T: Display,
		N: Display,
	{
		fn fmt(&self, f: &mut Formatter<'_>) -> Result {
			write!(f, "({}", self.tree.label())?;
			let mut formatter = TreeFormatter { formatter: f };
			for res in self.tree.walk(&mut formatter) {
				res?;
			}
			write!(formatter.formatter, ")")
		}
	}
}

pub use display::DisplayTree;

// The walker for the function 'reverse'
struct Reverser;

impl<'a, N, T> WalkerMut<'a, N, T, ()> for Reverser {
	fn on_branch(&mut self, _parent: &mut N, tree: &mut Ast<N, T>) -> (Option<()>, bool) {
		(Some(tree.children_mut().reverse()), true)
	}

	fn on_leaf(&mut self, _parent: &mut N, _leaf: &'a mut T) -> Option<()> {
		None
	}

	fn exit(&mut self, _parent: &mut N, _label: &'a mut N) -> Option<()> {
		None
	}
}

/// Recursively reverses the order of all the [child](Ast#label-and-children)
/// [nodes](AstNode) of an [`Ast`] and of all sub-trees.
pub fn reverse<N, T>(tree: &mut Ast<N, T>) {
	WalkerIterMut::new(tree, Reverser).for_each(|()| {})
}
