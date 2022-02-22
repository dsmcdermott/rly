// This test is to make sure that the code in `parse/parse-tests/examples/calculator.rs`
// matches to code shown in the example in `parse/src/parser_doc.md` with appears in the
// documentation for `parse`.

use std::{
	fmt::Display,
	fs,
};
use diff::Result::{self, *};

fn prep_lines<'s, I>(inp: I) -> impl Iterator<Item = &'s str>
where
	I: Iterator<Item = &'s str>
{
	inp
		.map(str::trim)
		.filter(|s| !s.is_empty())
		.filter(|s| !s.starts_with("//"))
		// Do not take the tests in `calculator.rs` into account when computing the diff.
		.take_while(|s| *s != "#[cfg(test)]")
}

// Break `s` into lines and extract the section between the penultimate line beginning
// with '```' and the last line beginning with '```'.
fn find_final_example(s: &str) -> impl Iterator<Item = &str> {
	let src: Vec<_> = s.lines().collect();
	let len = src.len();
	let mut lines = src.into_iter();
	let example_delim = |s: &str| s.starts_with("```");
	let end = lines.rposition(example_delim).unwrap();
	let end_offset = len - end - 1;
	let start = lines.rposition(example_delim).unwrap();
	let mut ret = s.lines();
	// advance the iterator to the start of the example
	ret.nth(start).unwrap();
	// moves the end of the iterator to the end of the example
	ret.nth_back(end_offset).unwrap();
	ret
}

// If the diff contains any changes, the function prints the changes to the standard err
// and then panics.
fn handle_diff<T: Display>(diff: Vec<Result<T>>) {
	let results: Vec<_> = diff.into_iter()
		.filter(|res| match res {
			Left(_) => true,
			Right(_) => true,
			Both(_, _) => false,
		})
		.collect();
	if !results.is_empty() {
		for res in results {
			match res {
				Left(s) => eprintln!("- {}", s),
				Right(s) => eprintln!("+ {}", s),
				_ => unreachable!(),
			}
		};
		panic!("the two examples differ");
	};
}

#[test]
fn test_example() {
	let example_file = fs::read_to_string("examples/calculator.rs").unwrap();
	let doc_text = fs::read_to_string("../src/parser_doc.md").unwrap();
	let example_lines: Vec<_> = prep_lines(example_file.lines()).collect();
	let src_lines: Vec<_> = prep_lines(find_final_example(&doc_text)).collect();
	let diff = diff::slice(&src_lines, &example_lines);
	handle_diff(diff);
}
