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
// child nodes of the top-level 'Start' node, which should itself consist of a single
// element representing the single child 'Sum' node. final_result can then be run to
// extract that value and return the calculator to a fresh state.
struct Calculator {
	stack: Vec<Vec<u32>>,
}

impl Calculator {
	fn new() -> Self {
		Self {
			stack: vec![Vec::new()],
		}
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
		if *leaf.kind() != TokenKind::int {
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
			NonTerm::Sum => operands.into_iter().sum(),
			NonTerm::Fact => operands.into_iter().product(),
			NonTerm::Term => {
				assert_eq!(operands.len(), 1);
				operands.pop().unwrap()
			}
			NonTerm::Start => unreachable!(),
		};
		self.push(n);
		None
	}
}

#[cfg(test)]
mod tests {

	const INP: &'static str = "5 + (1 + 4 * (3 + (2))) * 6";
	const ANSWER: u32 = 131;

	#[test]
	fn test() {
		use super::{Calculator, Lexer};
		let lexer = Lexer::new();
		let mut calc = Calculator::new();
		let tokens = lexer.lex(INP);
		let val = super::parse_input(tokens, &mut calc);
		assert_eq!(val, ANSWER);
	}
}
