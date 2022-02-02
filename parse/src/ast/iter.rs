//
//
//                | trait     | iter adapter      | iter unit     | iterator  |
//----------------|-----------|-------------------|---------------|-----------|
// borrowing:     | Walker    | WalkerIter        | IterWalker    | Iter      |
//----------------|-----------|-------------------|---------------|-----------|
// mut borrowing: | WalkerMut | WalkerIterMut     | IterWalkerMut | IterMut   |
//----------------|-----------|-------------------|---------------|-----------|
// consuming:     | Consumer  | WalkerIntoIter    | IterConsumer  | IntoIter  |
//----------------|-----------|-------------------|---------------|-----------|
//
//
// The items in this module come in three variations: (immutable) borrowing, mutable
// borrowing, and consuming. For each degree of ownership, there are four items:
//
// A walker trait, containing three methods: on_branch, to be called when entering a
// branch node, on_leaf, to be called on leaf nodes, and exit, to be called when exiting a
// branch node.
//
// A walking iterator struct that adapts a Walker and implements Iterator by recursively
// walking a tree and returning the results of calling the appropriate methods on the
// Walker.
//
// A unit struct that implements the Walker trait by simply returning the elements it's
// called on
//
// An iterator stuct that iterates over the nodes of a tree by using the walking iterator
// adapter and the above mentioned unit struct.
//
// For the walker trait, the methods return options; if the returned variant is None, the
// iterator adapter will skip on to the next node.
//
// The on_branch method is also used as a guard by returning a tuple where the second item
// is a bool. If the bool is false, the iterator adapter does not descend for that branch,
// and skips to the next node under the parent branch.
//
//
// There are minor differences between the three variations, having to do with the
// different constraints on the differeing degrees of ownership.
//

use super::{Ast, AstNode, RefNode};
use std::{marker::PhantomData, mem, ops::DerefMut};

/// A trait for borrowing [walkers][mod].
///
/// Used in conjunction with [`WalkerIter`], which takes a [`Walker`] and an [`Ast`] and
/// implements [`Iterator`] by recursively walking the [`Ast`] and (lazily) calling the
/// associated methods.
///
/// If a value of [`None`] is returned, the [`WalkerIter`] skips that node and moves on to
/// the next one.
///
/// if the second value returned by [`on_branch`](Self::on_branch) is [`false`], the
/// [`WalkerIter`] does not descend to the child nodes of that branch (it will still
/// return the value for the current node if the [`Option`] was [`Some(t)`].)
///
/// The three methods of this trait are called by the [`WalkerIter`] at different points
/// when walking the tree:
///
/// * [`on_branch`](Self::on_branch) is called on a branch (non-leaf) node before
/// descending to its child nodes.
///
/// * [`on_leaf`](Self::on_leaf) is called on a leaf node.
///
/// * [`exit`](Self::exit) is called upon exiting a branch node, after having covered all
/// of its children. It will not be called if [`on_branch`](Self::on_branch) returned
/// [`false`] for that branch.
///
/// See the [module documentation for more][mod].
///
/// [mod]: super#walking-an-ast
pub trait Walker<'a, B, L, T> {
	/// Called when entering a branch node.
	///
	/// If the boolean value is [`false`], the [`WalkerIter`] does not descend for that
	/// branch node, and skips all of its child nodes.
	///
	/// If the [`Option`] value is [`None`], that node is skipped. Otherwise the
	/// [`WalkerIter`] returns the value contained in the [`Some`] variant.
	fn on_branch(&mut self, tree: &'a Ast<B, L>) -> (Option<T>, bool);

	/// Called on leaf nodes.
	///
	/// If the return value is [`None`], that node is skipped. Otherwise the
	/// [`WalkerIter`] returns the value contained in the [`Some`] variant.
	fn on_leaf(&mut self, leaf: &'a L) -> Option<T>;

	/// Called on branch nodes after having covered all of their child nodes.
	///
	/// If [`on_branch`](Self::on_branch) returned [`false`] for that branch node, this
	/// method is not called.
	///
	/// If the return value is [`None`], that node is skipped. Otherwise the
	/// [`WalkerIter`] returns the value contained in the [`Some`] variant.
	fn exit(&mut self, tree: &'a Ast<B, L>) -> Option<T>;
}

impl<'a, B, L, T, W, V> Walker<'a, B, L, T> for V
where
	W: Walker<'a, B, L, T>,
	V: DerefMut<Target = W>,
{
	fn on_branch(&mut self, tree: &'a Ast<B, L>) -> (Option<T>, bool) {
		self.deref_mut().on_branch(tree)
	}

	fn on_leaf(&mut self, leaf: &'a L) -> Option<T> {
		self.deref_mut().on_leaf(leaf)
	}

	fn exit(&mut self, tree: &'a Ast<B, L>) -> Option<T> {
		self.deref_mut().exit(tree)
	}
}

/// A struct for [walking](super#walking-an-ast) an [`Ast`] by reference.
///
/// Takes a [`Walker`] and an [`Ast`] and implements [`Iterator`] by recursively walking
/// the [`Ast`] and (lazily) calling the methods of the [`Walker`]
pub struct WalkerIter<'a, B, L, T, W> {
	// Keeps track of the iter's location within the original Ast
	stack: Vec<(&'a Ast<B, L>, usize)>,
	// The current Ast
	tree: &'a Ast<B, L>,
	// The index of a child node within self.tree
	index: usize,
	walker: W,
	ret_type: PhantomData<T>,
}

impl<'a, B, L, T, W> WalkerIter<'a, B, L, T, W>
where
	W: Walker<'a, B, L, T>,
{
	/// Creates a new [`WalkerIter`] from `tree` and `walker`.
	///
	/// See also [`Ast::walk`].
	pub fn new(tree: &'a Ast<B, L>, walker: W) -> Self {
		Self {
			stack: Vec::new(),
			tree,
			index: 0,
			walker,
			ret_type: PhantomData,
		}
	}

	fn on_branch(&mut self, tree: &'a Ast<B, L>) -> (Option<T>, bool) {
		self.walker.on_branch(tree)
	}

	fn on_leaf(&mut self, leaf: &'a L) -> Option<T> {
		self.walker.on_leaf(leaf)
	}

	fn exit(&mut self, tree: &'a Ast<B, L>) -> Option<T> {
		self.walker.exit(tree)
	}
}

impl<'a, B, L, T, W> WalkerIter<'a, B, L, T, W> {
	// pushes self.tree and self.index onto self.stack
	// replaces them with 'tree' and 0
	fn push(&mut self, tree: &'a Ast<B, L>) {
		let old_tree = mem::replace(&mut self.tree, tree);
		let index = mem::replace(&mut self.index, 0);
		self.stack.push((old_tree, index));
	}

	// pops the top of self.stack into self.tree and self.index
	// returns the old self.tree and self.index
	fn pop(&mut self) -> Option<(&'a Ast<B, L>, usize)> {
		let (new_tree, new_index) = self.stack.pop()?;
		let tree = mem::replace(&mut self.tree, new_tree);
		let index = mem::replace(&mut self.index, new_index);
		Some((tree, index))
	}

	fn slice(&self) -> &'a [AstNode<B, L>] {
		self.tree.children()
	}

	fn get(&self, index: usize) -> Option<&'a AstNode<B, L>> {
		self.slice().get(index)
	}

	// Fetches an AstNode and the increments self.index
	// Returns None if self.index >= self.slice.len()
	fn attempt_next(&mut self) -> Option<&'a AstNode<B, L>> {
		let ret = self.get(self.index);
		self.index += 1;
		ret
	}
}

impl<'a, B, L, T, W> Iterator for WalkerIter<'a, B, L, T, W>
where
	W: Walker<'a, B, L, T>,
{
	type Item = T;

	// Walks through the elements of the tree, calling self.push when descending, and
	// self.pop when ascending after finishing with all the child nodes of self.tree.
	//
	// Returns None when the stack is empty and self.pop is called.
	fn next(&mut self) -> Option<Self::Item> {
		let ret = self.attempt_next();
		match ret {
			Some(node) => match node {
				AstNode::Branch(a) => {
					let (item, guard) = self.on_branch(a);
					if guard {
						self.push(a);
					};
					item.or_else(|| self.next())
				}
				AstNode::Leaf(l) => self.on_leaf(l).or_else(|| self.next()),
			},
			None => {
				let (tree, _index) = self.pop()?;
				self.exit(tree).or_else(|| self.next())
			}
		}
	}
}

// the walker type for Iter
struct IterWalker;

impl<'a, B, L> Walker<'a, B, L, RefNode<'a, B, L>> for IterWalker {
	fn on_branch(&mut self, tree: &'a Ast<B, L>) -> (Option<RefNode<'a, B, L>>, bool) {
		(Some(RefNode::Branch(tree)), true)
	}

	fn on_leaf(&mut self, leaf: &'a L) -> Option<RefNode<'a, B, L>> {
		Some(RefNode::Leaf(leaf))
	}

	fn exit(&mut self, _tree: &'a Ast<B, L>) -> Option<RefNode<'a, B, L>> {
		None
	}
}

/// An [`Iterator`] by reference over the nodes of an [`Ast`].
///
/// For [branch nodes](super::AstNode::Branch) it returns a node and then recursively
/// iterates over its children.
///
/// It does not return a reference to the original [`Ast`].
///
/// # Example
///
/// Supose you have the following tree
///
/// ```text
///            Sum
///         ┌───┴───────────┐
///        Sum              │
/// ┌───────┴───┐           │
/// │          Fact         │
/// │       ┌───┴───┐       │
/// 1       2       3       4
/// ```
///
/// And you call [`Iter::new`] on it. The resulting iterator would return the following
/// values:
///
/// ```text
/// Branch(&Sum(1, Fact(2, 3)))
/// Leaf(&1)
/// Branch(&Fact(2, 3))
/// Leaf(&2)
/// Leaf(&3)
/// Leaf(&4)
/// ```
///
pub struct Iter<'a, B, L> {
	iter: WalkerIter<'a, B, L, RefNode<'a, B, L>, IterWalker>,
}

impl<'a, B, L> Iter<'a, B, L> {
	/// Creates a new [`Iter`] from `tree`.
	///
	/// See also [`Ast::iter`].
	pub fn new(tree: &'a Ast<B, L>) -> Self {
		Self {
			iter: WalkerIter::new(tree, IterWalker),
		}
	}
}

impl<'a, B, L> Iterator for Iter<'a, B, L> {
	type Item = RefNode<'a, B, L>;

	fn next(&mut self) -> Option<Self::Item> {
		self.iter.next()
	}
}

/// A trait for mutably borrowing [walkers][mod].
///
/// Used in conjunction with [`WalkerIterMut`], which takes a [`WalkerMut`] and an [`Ast`]
/// and implements [`Iterator`] by recursively walking the [`Ast`] and (lazily) calling
/// the associated methods.
///
/// If a value of [`None`] is returned, the [`WalkerIterMut`] skips that node and moves on
/// to the next one.
///
/// if the second value returned by [`on_branch`](Self::on_branch) is [`false`], the
/// [`WalkerIterMut`] does not descend to the child nodes of that branch (it will still
/// return the value for the current node if the [`Option`] was [`Some(t)`].)
///
/// The three methods of this trait are called by the [`WalkerIterMut`] at different
/// points when walking the tree:
///
/// * [`on_branch`](Self::on_branch) is called on a branch (non-leaf) node before
/// descending to its child nodes.
///
/// * [`on_leaf`](Self::on_leaf) is called on a leaf node.
///
/// * [`exit`](Self::exit) is called upon exiting a branch node, after having covered all
/// of its children. It will not be called if [`on_branch`](Self::on_branch) returned
/// [`false`] for that branch.
///
/// Each method takes a mutable reference to the [`label`] of the parent node. This helps
/// alleviate the need to alias references to the label's to keep track of state.
///
/// See the [module documentation for more][mod].
///
/// [mod]: super#walking-an-ast
/// [`label`]: Ast#label-and-children
pub trait WalkerMut<'a, B, L, T> {
	/// Called when entering a branch node.
	///
	/// If the boolean value is [`false`], the [`WalkerIterMut`] does not descend for that
	/// branch node, and skips all of its child nodes.
	///
	/// If the [`Option`] value is [`None`], that node is skipped. Otherwise the
	/// [`WalkerIterMut`] returns the value contained in the [`Some`] variant.
	fn on_branch(&mut self, parent: &mut B, tree: &mut Ast<B, L>) -> (Option<T>, bool);

	/// Called on leaf nodes.
	///
	/// If the return value is [`None`], that node is skipped. Otherwise the
	/// [`WalkerIterMut`] returns the value contained in the [`Some`] variant.
	fn on_leaf(&mut self, parent: &mut B, leaf: &'a mut L) -> Option<T>;

	/// Called on the [`label`] of a branch node after having covered all of its child
	/// nodes.
	///
	/// If [`on_branch`](Self::on_branch) returned [`false`] for that branch node, this
	/// method is not called.
	///
	/// If the return value is [`None`], that node is skipped. Otherwise the
	/// [`WalkerIterMut`] returns the value contained in the [`Some`] variant.
	///
	/// [`label`]: Ast#label-and-children
	fn exit(&mut self, parent: &mut B, label: &'a mut B) -> Option<T>;
}

impl<'a, B, L, T, W, V> WalkerMut<'a, B, L, T> for V
where
	W: WalkerMut<'a, B, L, T>,
	V: DerefMut<Target = W>,
{
	fn on_branch(&mut self, parent: &mut B, tree: &mut Ast<B, L>) -> (Option<T>, bool) {
		self.deref_mut().on_branch(parent, tree)
	}

	fn on_leaf(&mut self, parent: &mut B, leaf: &'a mut L) -> Option<T> {
		self.deref_mut().on_leaf(parent, leaf)
	}

	fn exit(&mut self, parent: &mut B, label: &'a mut B) -> Option<T> {
		self.deref_mut().exit(parent, label)
	}
}

/// A struct for [walking](super#walking-an-ast) an [`Ast`] by mutable reference.
///
/// Takes a [`WalkerMut`] and an [`Ast`] and implements [`Iterator`] by recursively
/// walking the [`Ast`] and (lazily) calling the methods of the [`WalkerMut`]
pub struct WalkerIterMut<'a, B, L, T, W> {
	// keeps track of the iter's location within the original Ast
	stack: Vec<(&'a mut B, &'a mut [AstNode<B, L>])>,

	// The label of the current Ast. Gets passed as `parent` to the WalkerMut
	label: &'a mut B,

	// the children of the current Ast
	children: &'a mut [AstNode<B, L>],

	// Holds a branch node after it has been operated on by on_branch: self.branch is set
	// to the branch node and self.walker.on_branch is then called on
	// self.branch.unwrap(). On the next call to Iterator::next, self.branch is removed
	// and descended along (if self.descend is set)
	branch: Option<&'a mut Ast<B, L>>,

	// stores the boolean return value of on_branch
	descend: bool,

	walker: W,
	ret_type: PhantomData<T>,
}

impl<'a, B, L, T, W> WalkerIterMut<'a, B, L, T, W>
where
	W: WalkerMut<'a, B, L, T>,
{
	/// Creates a new [`WalkerIterMut`] from `tree` and `walker`.
	///
	/// See also [`Ast::walk_mut`].
	pub fn new(tree: &'a mut Ast<B, L>, walker: W) -> Self {
		let (label, children) = tree.components_mut();
		Self {
			stack: Vec::new(),
			label,
			children: children.deref_mut(),
			branch: None,
			descend: false,
			walker,
			ret_type: PhantomData,
		}
	}

	fn on_branch(&mut self) -> Option<T> {
		let (res, b) = self
			.walker
			.on_branch(&mut self.label, self.branch.as_mut().unwrap());
		self.descend = b;
		res
	}

	fn on_leaf(&mut self, leaf: &'a mut L) -> Option<T> {
		self.walker.on_leaf(&mut self.label, leaf)
	}

	fn exit(&mut self, label: &'a mut B) -> Option<T> {
		self.walker.exit(&mut self.label, label)
	}
}

impl<'a, B, L, T, W> WalkerIterMut<'a, B, L, T, W> {
	// sets self.label and self.children to the given arguments and pushes the old values
	// onto self.stack
	fn push(&mut self, label: &'a mut B, children: &'a mut [AstNode<B, L>]) {
		let old_label = mem::replace(&mut self.label, label);
		let old_children = mem::replace(&mut self.children, children);
		self.stack.push((old_label, old_children));
	}

	// pops the top off of self.stack and sets self.label and self.children to the result,
	// returning their old values
	fn pop(&mut self) -> Option<(&'a mut B, &'a mut [AstNode<B, L>])> {
		let (new_label, new_children) = self.stack.pop()?;
		let label = mem::replace(&mut self.label, new_label);
		let children = mem::replace(&mut self.children, new_children);
		Some((label, children))
	}

	// Returns a mutable reference to self.children[0] and sets self.children to
	// self.children[1..].
	//
	// Returns None if self.children is empty.
	fn attempt_next(&mut self) -> Option<&'a mut AstNode<B, L>> {
		let slice = mem::replace(&mut self.children, &mut []);
		if slice.is_empty() {
			None
		} else {
			let (l, r) = slice.split_at_mut(1);
			self.children = r;
			l.get_mut(0)
		}
	}

	// pushes the tree
	fn recurse_branch(&mut self, tree: &'a mut Ast<B, L>) {
		let (label, children) = tree.components_mut();
		self.push(label, children.deref_mut());
	}
}

impl<'a, B, L, T, W> Iterator for WalkerIterMut<'a, B, L, T, W>
where
	W: WalkerMut<'a, B, L, T>,
{
	type Item = T;

	fn next(&mut self) -> Option<Self::Item> {
		if let Some(a) = self.branch.take() {
			if self.descend {
				self.recurse_branch(a);
			}
		};
		let ret = self.attempt_next();
		match ret {
			Some(node) => match node {
				AstNode::Branch(a) => {
					self.branch = Some(a);
					self.on_branch().or_else(|| self.next())
				}
				AstNode::Leaf(l) => self.on_leaf(l).or_else(|| self.next()),
			},
			None => {
				let (label, _children) = self.pop()?;
				self.exit(label).or_else(|| self.next())
			}
		}
	}
}

/// A component of an [`Ast`]: either a [label](Self::Label) or a [leaf](Self::Leaf).
///
/// Similar to [`MutRefNode`](super::MutRefNode), except it uses the variant
/// [`Label`](Self::Label) with a reference to the [label](Ast#label-and-children) of an
/// [`Ast`] instead of the variant [`Branch`](super::MutRefNode::Branch) with a reference
/// to the [`Ast`] itself.
///
/// Used by [`IterMut`] for iterating over the elements of an [`Ast`]
pub enum MutNode<'a, B, L> {
	/// The [label](Ast#label-and-children) of a branch node.
	Label(&'a mut B),

	/// A leaf node.
	Leaf(&'a mut L),
}

impl<'a, B, L> From<super::MutRefNode<'a, B, L>> for MutNode<'a, B, L> {
	fn from(node: super::MutRefNode<'a, B, L>) -> Self {
		use super::MutRefNode::*;
		match node {
			Branch(a) => Self::Label(a.label_mut()),
			Leaf(l) => Self::Leaf(l),
		}
	}
}

impl<'a, B, L> From<&'a mut AstNode<B, L>> for MutNode<'a, B, L> {
	fn from(node: &'a mut AstNode<B, L>) -> Self {
		super::MutRefNode::from(node).into()
	}
}

// the WalkerMut struct for IterMut
struct IterWalkerMut;

impl<'a, B, L> WalkerMut<'a, B, L, MutNode<'a, B, L>> for IterWalkerMut {
	fn on_branch(
		&mut self,
		_parent: &mut B,
		_tree: &mut Ast<B, L>,
	) -> (Option<MutNode<'a, B, L>>, bool) {
		(None, true)
	}

	fn on_leaf(&mut self, _parent: &mut B, leaf: &'a mut L) -> Option<MutNode<'a, B, L>> {
		Some(MutNode::Leaf(leaf))
	}

	fn exit(&mut self, _parent: &mut B, label: &'a mut B) -> Option<MutNode<'a, B, L>> {
		Some(MutNode::Label(label))
	}
}

/// An [`Iterator`] by mutable reference over the [labels](Ast#label-and-children) and
/// leaf nodes of an [`Ast`].
///
/// For [branch nodes](super::AstNode::Branch) it first iterates over its descendants and
/// then returns a mutable reference to its label.
///
/// It does not return a reference to the original [`Ast`].
///
/// # Example
///
/// Supose you have the following tree
///
/// ```text
///            Sum
///         ┌───┴───────────┐
///        Sum              │
/// ┌───────┴───┐           │
/// │          Fact         │
/// │       ┌───┴───┐       │
/// 1       2       3       4
/// ```
///
/// And you call [`Iter::new`] on it. The resulting iterator would return the following
/// values:
///
/// ```text
/// Leaf(&mut 1)
/// Leaf(&mut 2)
/// Leaf(&mut 3)
/// Branch(&mut Fact)
/// Branch(&mut Sum)
/// Leaf(&mut 4)
/// ```
///
pub struct IterMut<'a, B, L> {
	iter: WalkerIterMut<'a, B, L, MutNode<'a, B, L>, IterWalkerMut>,
}

impl<'a, B, L> IterMut<'a, B, L> {
	/// Creates a new [`IterMut`] from `tree`.
	///
	/// See also [`Ast::iter_mut`].
	pub fn new(tree: &'a mut Ast<B, L>) -> Self {
		Self {
			iter: WalkerIterMut::new(tree, IterWalkerMut),
		}
	}
}

impl<'a, B, L> Iterator for IterMut<'a, B, L> {
	type Item = MutNode<'a, B, L>;

	fn next(&mut self) -> Option<Self::Item> {
		self.iter.next()
	}
}

/// A trait for owning [walkers][mod].
///
/// Used in conjunction with [`WalkerIntoIter`], which takes a [`Consumer`] and an [`Ast`] and
/// implements [`Iterator`] by recursively walking the [`Ast`] and (lazily) calling the
/// associated methods.
///
/// If a value of [`None`] is returned, the [`WalkerIter`] skips that node and moves on to
/// the next one.
///
/// If the second value returned by [`on_branch`](Self::on_branch) is [`None`], the
/// [`WalkerIter`] does not descend to the child nodes of that branch (it will still
/// return the value for the current node if the [`Option`] was [`Some(t)`].) If it was
/// [`Some(A)`], it instead recursively descends along that node (if you just want to
/// descend along that node, just have the method return the node it was called on.)
///
/// The three methods of this trait are called by the [`WalkerIntoIter`] at different
/// points when walking the tree:
///
/// * [`on_branch`](Self::on_branch) is called on a branch (non-leaf) node before
/// descending to its child nodes.
///
/// * [`on_leaf`](Self::on_leaf) is called on a leaf node.
///
/// * [`exit`](Self::exit) is called upon exiting a branch node, after having covered all
/// of its children. It will not be called if [`on_branch`](Self::on_branch) returned
/// [`None`] as its second return value for that branch.
///
/// See the [module documentation for more][mod].
///
/// [mod]: super#walking-an-ast
pub trait Consumer<B, L, T> {
	/// Called when entering a branch node.
	///
	/// If the second option is [`None`], the [`WalkerIntoIter`] does not descend for that
	/// branch node, and skips all of its child nodes. Otherwise, the node contained in
	/// the [`Some`] variant effectively replaces the node `tree` and the
	/// [`WalkerIntoIter`] descends along that node instead.
	///
	/// If you just want to descend along the current node, have the method return
	/// `Some(tree)` as its second return value.
	///
	/// If the [`Option`] value is [`None`], that node is skipped. Otherwise the
	/// [`WalkerIntoIter`] returns the value contained in the [`Some`] variant.
	fn on_branch(&mut self, tree: Ast<B, L>) -> (Option<T>, Option<Ast<B, L>>);

	/// Called on leaf nodes.
	///
	/// If the return value is [`None`], that node is skipped. Otherwise the
	/// [`WalkerIntoIter`] returns the value contained in the [`Some`] variant.
	fn on_leaf(&mut self, leaf: L) -> Option<T>;

	/// Called on the [`label`] of a branch node after having covered all of its child
	/// nodes.
	///
	/// If the return value is [`None`], that node is skipped. Otherwise the
	/// [`WalkerIntoIter`] returns the value contained in the [`Some`] variant.
	///
	/// [`label`]: Ast#label-and-children
	fn exit(&mut self, tree: B) -> Option<T>;
}

impl<B, L, T, W, V> Consumer<B, L, T> for V
where
	W: Consumer<B, L, T>,
	V: DerefMut<Target = W>,
{
	fn on_branch(&mut self, tree: Ast<B, L>) -> (Option<T>, Option<Ast<B, L>>) {
		self.deref_mut().on_branch(tree)
	}

	fn on_leaf(&mut self, leaf: L) -> Option<T> {
		self.deref_mut().on_leaf(leaf)
	}

	fn exit(&mut self, tree: B) -> Option<T> {
		self.deref_mut().exit(tree)
	}
}

/// A struct for [walking](super#walking-an-ast) an [`Ast`] while taking ownership of it.
///
/// Takes a [`Consumer`] and an [`Ast`] and implements [`Iterator`] by recursively walking
/// the [`Ast`] and (lazily) calling the methods of the [`Consumer`]
pub struct WalkerIntoIter<B, L, T, W> {
	// keeps track of the position of the iter within the original tree
	stack: Vec<(B, std::vec::IntoIter<AstNode<B, L>>)>,

	// the label of the current Ast
	label: B,

	// the children of the current ast
	iter: std::vec::IntoIter<AstNode<B, L>>,
	walker: W,
	ret_type: PhantomData<T>,
}

impl<B, L, T, W> WalkerIntoIter<B, L, T, W>
where
	W: Consumer<B, L, T>,
{
	/// Creates a new [`WalkerIntoIter`] from `tree` and `consumer`.
	///
	/// See also [`Ast::consume`].
	pub fn new(tree: Ast<B, L>, consumer: W) -> Self {
		let (label, children) = tree.into_components();
		Self {
			stack: Vec::new(),
			label,
			iter: children.into_iter(),
			walker: consumer,
			ret_type: PhantomData,
		}
	}

	fn on_branch(&mut self, tree: Ast<B, L>) -> (Option<T>, Option<Ast<B, L>>) {
		self.walker.on_branch(tree)
	}

	fn on_leaf(&mut self, leaf: L) -> Option<T> {
		self.walker.on_leaf(leaf)
	}

	fn exit(&mut self, tree: B) -> Option<T> {
		self.walker.exit(tree)
	}
}

impl<B, L, T, W> WalkerIntoIter<B, L, T, W> {
	fn push(&mut self, tree: Ast<B, L>) {
		let (new_label, children) = tree.into_components();
		let new_iter = children.into_iter();
		let label = mem::replace(&mut self.label, new_label);
		let iter = mem::replace(&mut self.iter, new_iter);
		self.stack.push((label, iter));
	}

	fn pop(&mut self) -> Option<(B, std::vec::IntoIter<AstNode<B, L>>)> {
		let (new_label, new_iter) = self.stack.pop()?;
		let label = mem::replace(&mut self.label, new_label);
		let iter = mem::replace(&mut self.iter, new_iter);
		Some((label, iter))
	}

	fn attempt_next(&mut self) -> Option<AstNode<B, L>> {
		self.iter.next()
	}
}

impl<B, L, T, W> Iterator for WalkerIntoIter<B, L, T, W>
where
	W: Consumer<B, L, T>,
{
	type Item = T;

	fn next(&mut self) -> Option<Self::Item> {
		let ret = self.attempt_next();
		match ret {
			Some(node) => match node {
				AstNode::Branch(a) => {
					let (item, guard) = self.on_branch(a);
					if let Some(a) = guard {
						self.push(a);
					};
					item.or_else(|| self.next())
				}
				AstNode::Leaf(l) => self.on_leaf(l).or_else(|| self.next()),
			},
			None => {
				let (label, _iter) = self.pop()?;
				self.exit(label).or_else(|| self.next())
			}
		}
	}
}

/// A component of an [`Ast`]: either a [label](Self::Label) or a [leaf](Self::Leaf).
///
/// Similar to [`AstNode`], except it uses the variant [`Label`](Self::Label) holding the
/// [label](Ast#label-and-children) of an [`Ast`] instead of the variant
/// [`Branch`](AstNode::Branch) holding the [`Ast`] itself.
///
/// Used by [`IntoIter`] for iterating over the elements of an [`Ast`]
pub enum AstElem<B, L> {
	Label(B),
	Leaf(L),
}

impl<B, L> From<AstNode<B, L>> for AstElem<B, L> {
	fn from(node: AstNode<B, L>) -> Self {
		use AstNode::*;
		match node {
			Branch(a) => Self::Label(a.into_label()),
			Leaf(l) => Self::Leaf(l),
		}
	}
}

struct IterConsumer;

impl<B, L> Consumer<B, L, AstElem<B, L>> for IterConsumer {
	fn on_branch(&mut self, tree: Ast<B, L>) -> (Option<AstElem<B, L>>, Option<Ast<B, L>>) {
		(None, Some(tree))
	}

	fn on_leaf(&mut self, leaf: L) -> Option<AstElem<B, L>> {
		Some(AstElem::Leaf(leaf))
	}

	fn exit(&mut self, tree: B) -> Option<AstElem<B, L>> {
		Some(AstElem::Label(tree))
	}
}

/// An [`Iterator`] over the [labels](Ast#label-and-children) and leaf nodes of an [`Ast`].
///
/// For [branch nodes](super::AstNode::Branch) it first iterates over its descendants and
/// then returns its label.
///
/// It does not return the label of the original [`Ast`].
///
/// # Example
///
/// Supose you have the following tree
///
/// ```text
///            Sum
///         ┌───┴───────────┐
///        Sum              │
/// ┌───────┴───┐           │
/// │          Fact         │
/// │       ┌───┴───┐       │
/// 1       2       3       4
/// ```
///
/// And you call [`Iter::new`] on it. The resulting iterator would return the following
/// values:
///
/// ```text
/// Leaf(1)
/// Leaf(2)
/// Leaf(3)
/// Branch(Fact)
/// Branch(Sum)
/// Leaf(4)
/// ```
///
pub struct IntoIter<B, L> {
	iter: WalkerIntoIter<B, L, AstElem<B, L>, IterConsumer>,
}

impl<B, L> IntoIter<B, L> {
	/// Creates a new [`IntoIter`] from `tree`.
	///
	/// See also [`Ast::into_iter`].
	pub fn new(tree: Ast<B, L>) -> Self {
		Self {
			iter: WalkerIntoIter::new(tree, IterConsumer),
		}
	}
}

impl<B, L> Iterator for IntoIter<B, L> {
	type Item = AstElem<B, L>;

	fn next(&mut self) -> Option<Self::Item> {
		self.iter.next()
	}
}
