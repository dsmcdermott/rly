// A module containing helper code for build scripts that create lexers, as well as the
// `lexer` macro which can be used to include the lexer in a src file. The `LexerBuilder`
// struct is just a thin wrapper around the more general `BuilderBase` struct found in
// rly_common/src/builder.rs that provides the appropriate defaults for lexers.

// Note: the type 'LexerBuilderError' is found in src/errors.rs

use super::{lexer_writer, LexerBuilderError};
use rly_common::builders::{check_is_cargo_run, BuilderBase};
use std::{
	env,
	ffi::{OsStr, OsString},
	fs::File,
	io::Read,
	path::{Path, PathBuf},
};

const EXT: &'static str = "lex";
const M_TYPE: &'static str = "lexer";
const ENDING: &'static str = "lex";

/// A helper struct for creating lexers in build scripts.
///
/// Instances of this stuct can be used in build scripts for creating lexers to be used in
/// a package. It has two hidden paramaters that affect its behaviour: the `name` used by
/// the builder when writing the finished lexer, and the `location` of the source file.
/// These are private and can only be accessed or modified through the provided methods
/// which automatically run correctness checks on the provided values.
///
/// Note that `LexerBuilder`'s are only intended to be run by Cargo as a part of a build
/// script, and [`LexerBuilder::new`] will not return a builder unless the [environment
/// resembles that of a build script](LexerBuilder#environment). See the [official
/// documentation](https://doc.rust-lang.org/cargo/reference/build-scripts.html) for more
/// details on build scripts.
///
/// # Name and Location
///
/// The builder will write the lexer in the current builds
/// [`OUT_DIR`](https://doc.rust-lang.org/cargo/reference/environment-variables.html#environment-variables-cargo-sets-for-build-scripts),
/// with the name `[name].rs`. `name` must be a valid filename, with no seperators[^seps]
/// and no extension. If `name` is not set, but `location` is, `name` defaults to the
/// filename for `location` minus the "`.lex`" extension. Otherwise it defaults to the
/// name of the package with "`_lex`" added to the end.
///
/// [^seps]: "`/`" on Unix/Redox and "`\`" on Windows. Note that, since this is running as
/// part of a build script, it is the host system that matters, not the compilation
/// target. This also means that you should be weary about using either `/` or `\`,
/// regardless of the platform: something that works fine on your system may fail to
/// compile when being built on a different platform!
///
/// The value for `location` must be an existing file ending with "`.lex`". If `location`
/// is not set then it defaults to `name` with "`.lex`" added to the end (if `name` and
/// `location` are not set, `name` default to the package name plus "`_lex`", so `location
/// would default to "`[package name]_lex.lex`".)
///
/// # Environment
///
/// `LexerBuilder`'s rely on a number of environment variables to be set in order to understand
/// the package being built and where to write files. These should be automatically set
/// when the code is being run by Cargo as a part of a build script. For safety,
/// [`LexerBuilder::new()`] will check the environment and will not return a builder
/// unless it is properly configured.
///
/// ```
/// // outside of build.rs
///
/// use lex::LexerBuilder;
///
/// assert!(LexerBuilder::new().is_none());
/// ```
///
/// # Reruns
///
/// Once the desired location for the source file of a lexer is set it is recommended to
/// run [`set_rerun`](LexerBuilder::set_rerun) to set Cargo to monitor the source file for
/// changes and rerun the build script when it detects one since the last build.

pub struct LexerBuilder {
	builder: BuilderBase,
}

impl LexerBuilder {
	/// Creates a new instance of a `LexerBuilder`. Returns [`None`] if the environement
	/// is not configured properly. See [here](LexerBuilder#environment) for more details.
	///
	/// # Example
	/// ``` no_run
	/// # use lex::LexerBuilder;
	/// let mut builder = LexerBuilder::new().unwrap();
	/// builder.set_default_values();
	/// ```
	pub fn new() -> Option<Self> {
		if check_is_cargo_run() {
			Some(unsafe { Self::new_unchecked() })
		} else {
			None
		}
	}

	unsafe fn new_unchecked() -> Self {
		Self {
			builder: BuilderBase::new(),
		}
	}

	/// Returns the [name](LexerBuilder#name-and-location) used by the builder if set.
	/// Returns `None` otherwise.
	pub fn name(&self) -> Option<&OsStr> {
		self.builder.name()
	}

	/// Returns the [location](LexerBuilder#name-and-location) used by the builder.
	/// Returns `None` otherwise
	pub fn location(&self) -> Option<&Path> {
		self.builder.location()
	}

	/// Attempts to set the name for `self` to `name`.
	///
	/// If `name` is a valid filename (see [here](LexerBuilder#name-and-location),) then
	/// this method returns a mutable reference to `self`, otherwise it returns an
	/// [`LexerBuilderError`].
	///
	/// # Example
	/// ``` no_run
	/// # fn main() -> Result<(), lex::LexerBuilderError> {
	/// use std::ffi::OsStr;
	/// use lex::LexerBuilder;
	/// let mut builder = LexerBuilder::new().unwrap();
	/// let builder_name = builder
	/// 	.with_name("my_lexer")?
	/// 	.name();
	/// assert_eq!(builder_name, Some(OsStr::new("my_lexer")));
	/// # Ok(())
	/// # }
	/// ```
	pub fn with_name<S: Into<OsString>>(
		&mut self,
		name: S,
	) -> Result<&mut Self, LexerBuilderError> {
		self.builder.with_name(name, M_TYPE, EXT)?;
		Ok(self)
	}

	/// Attempts to set the location for `self` to `location`.
	///
	/// If `location` is a valid path to a source file (see
	/// [here](LexerBuilder#name-and-location),) then this method returns a mutable
	/// reference to `self`, otherwise it returns an [`LexerBuilderError`].
	///
	/// # Example
	/// ```no_run
	/// # fn main() -> Result<(), lex::LexerBuilderError> {
	/// use std::path::Path;
	/// use lex::LexerBuilder;
	///
	/// let mut builder = LexerBuilder::new().unwrap();
	/// let builder_location = builder
	/// 	.at_location("lex-yacc/my_lexer.lex")?
	/// 	.location();
	///
	/// assert_eq!(builder_location, Some(Path::new("lex-yacc/my_lexer.lex")));
	/// # Ok(())
	/// # }
	/// ```
	pub fn at_location<S: Into<PathBuf>>(
		&mut self,
		location: S,
	) -> Result<&mut Self, LexerBuilderError> {
		self.builder.at_location(location, M_TYPE, EXT)?;
		Ok(self)
	}

	fn set_name(&mut self) {
		self.builder.set_name(ENDING)
	}

	fn set_path(&mut self) {
		self.builder.set_path(EXT)
	}

	/// Sets the `name` and `location` to their default values, as described
	/// [here](LexerBuilder#name-and-location). Calling this method directly is usually
	/// unecessary, as the fields will automatically be set to their default values as
	/// necessary when building a lexer. It can however be usefull for inspecting what the
	/// values _would_ be.
	///
	/// # Example
	/// ``` no_run
	/// use std::ffi::OsStr;
	/// use std::path::Path;
	/// use lex::LexerBuilder;
	///
	/// let mut builder = LexerBuilder::new().unwrap();
	/// builder.with_name("my_lexer").unwrap();
	///
	/// assert_eq!(builder.location(), None);
	///
	/// builder.set_default_values();
	///
	/// assert_eq!(builder.name(), Some(OsStr::new("my_lexer")));
	/// assert_eq!(builder.location(), Some(Path::new("my_lexer.lex")));
	/// ```
	pub fn set_default_values(&mut self) {
		self.set_name();
		self.set_path();
	}

	/// Tells Cargo to watch the source file for changes and rerun the build script if
	/// necessary. If no location is set, it returns `None`
	///
	/// # Example
	///
	/// ``` no_run
	/// // in build.rs
	///
	/// use lex::{LexerBuilder, LexerBuilderError};
	///
	/// fn main() -> Result<(), LexerBuilderError> {
	/// 	let mut builder = LexerBuilder::new().unwrap();
	/// 	builder
	/// 		.with_name("my_lexer")
	/// 		.unwrap()
	/// 		.build()?
	/// 		.set_rerun().unwrap();
	/// 	Ok(())
	/// }
	/// ```
	pub fn set_rerun(&self) -> Option<()> {
		self.builder.set_rerun_for_location()
	}

	/// Returns the file path used when writing the lexer. If the
	/// [name](LexerBuilder#name-and-location) is not set, or if it cannot determin the
	/// out dir set by cargo, then it returns `None`.
	///
	/// Note that even if the name is set, the file may not exist if the builder hasn't
	/// yet written a lexer there. This method just tells you where the builder _would_
	/// write to if you were to run [`build`](LexerBuilder::build) or something similar.
	///
	/// # Example
	///
	/// ``` no_run
	/// use std::{env, path::PathBuf};
	/// use lex::LexerBuilder;
	///
	/// # fn main() -> Result<(), lex::LexerBuilderError> {
	/// let output_loc = LexerBuilder::new().unwrap()
	/// 	.with_name("my_lexer")?
	/// 	.output_file();
	/// let path = PathBuf::from(
	/// 	format!(
	/// 		"{}/my_lexer.rs",
	/// 		env::var("OUT_DIR").unwrap()
	/// 	)
	/// );
	/// assert_eq!(output_loc, Some(path));
	/// # Ok(())
	/// # }
	/// ```
	pub fn output_file(&self) -> Option<PathBuf> {
		let mut out_loc = PathBuf::from(env::var_os("OUT_DIR")?);
		out_loc.push(Path::new(self.name()?));
		out_loc.set_extension(OsStr::new("rs"));
		Some(out_loc)
	}

	/// Builds the lexer, reading from the file at
	/// [`location`](LexerBuilder#name-and-location) and writing a file with the appropriate
	/// [`name`](LexerBuilder#name-and-location) to the out dir set by Cargo.
	///
	/// # Example
	///
	/// ```no_run
	/// // in build.rs
	///
	/// use lex::{LexerBuilder, LexerBuilderError};
	///
	/// fn main() -> Result<(), LexerBuilderError> {
	/// 	let mut builder = LexerBuilder::new().unwrap();
	/// 	builder
	/// 		.build()?
	/// 		.set_rerun().unwrap();
	/// 	Ok(())
	/// }
	/// ```
	pub fn build(&mut self) -> Result<&mut Self, LexerBuilderError> {
		let src = self.get_src()?;
		self.build_from_str(&src)
	}

	/// Like [`build`](LexerBuilder::build) but reads its source from the provided `src`
	/// rather than than an input file.
	///
	/// # Example
	///
	/// ``` no_run
	/// # fn main() -> Result<(), lex::LexerBuilderError> {
	/// use lex::LexerBuilder;
	///
	/// let rules = r#"
	/// 	id : "[a-zA-Z_][0-9a-zA-Z_]*"
	/// 	ignore : "[[:space:]]+"
	/// 	int : "[0-9]+"
	/// 	error : "/""#;
	///
	/// let mut builder = LexerBuilder::new().unwrap();
	/// builder.build_from_str(rules)?;
	/// # Ok(())
	/// # }
	/// ```
	pub fn build_from_str(&mut self, src: &str) -> Result<&mut Self, LexerBuilderError> {
		self.set_name();
		let out_loc = self.output_file().unwrap();
		let fout = File::create(out_loc)?;
		lexer_writer::write_from_str(src, fout)?;
		Ok(self)
	}

	/// Reads the file at [`location`](LexerBuilder#name-and-location) and returns it as a
	/// string if successful. Otherwise returns an [I/O error](std::io::Error).
	pub fn get_src(&mut self) -> Result<String, std::io::Error> {
		self.set_default_values();
		let mut fin = File::open(self.location().unwrap())?;
		let mut src = String::new();
		fin.read_to_string(&mut src)?;
		Ok(src)
	}
}

/// Creates a [`LexerBuilder`] and builds a lexer with the default values, returning any
/// errors that occur.
///
/// # Example
///
/// ```no_run
/// // in build.rs
///
/// use lex::{LexerBuilder, LexerBuilderError};
///
/// fn main() -> Result<(), LexerBuilderError> {
/// 	lex::build_lexer()
/// }
/// ```
pub fn build_lexer() -> Result<(), LexerBuilderError> {
	LexerBuilder::new().unwrap().build()?;
	Ok(())
}

/// A macro for including a [lexer](crate) created with a [`LexerBuilder`]. If no name is
/// provided it defaults to the same default [`name`](LexerBuilder#name-and-location) for
/// [`LexerBuilder`]'s as described [there](LexerBuilder#name-and-location).
///
/// # Example
///
/// In `build.rs`
///
/// ``` no_run
/// use lex::LexerBuilderError;
///
/// fn main() -> Result<(), LexerBuilderError> {
/// 	lex::build_lexer()
/// }
/// ```
///
/// In `src/main.rs`
///
/// ``` ignore
///
/// lex::lexer!();
///
/// fn main() {
/// 	let rules = lexer::LexerRules::new();
///
/// 	//
/// }
/// ```

//	# Example
//
//	In `build.rs`
//
//	``` no_run
//	use lex::{LexerBuilder, LexerBuilderError};
//
//	fn main() -> Result<(), LexerBuilderError> {
//
//		lex::build_lexer()?										// Builds a lexer with default values.
//
//		let mut alt_builder = LexerBuilder::new().unwrap();
//		alt_builder.with_name("alt_lexer").unwrap().build()?;	// Builds an alternative lexer with the name 'alt_lexer'.
//		Ok(())
//	}
//	```
//
//	In `src/main.rs`
//
//	``` ignore
//	use std::{
//		env,
//		fs::File,
//		ffi::OsString,
//		io::Read};
//
//	use lex::{self, Lexer};
//
//	lex::lexer!();
//
//	mod alt_lexer {
//		lex::lexer!("alt_lexer");
//		pub use lexer::*;
//	}
//
//	fn process_arg(arg: OsString) {
//		let mut src = String::new();
//
//		File::open(arg)
//			.and_then(|file| file.read_to_string(&mut src))
//			.expect("unable to open file");
//
//		let mut tokens = Vec::new();
//
//		let lexer =
//
//		for token in lexer::LexerRules::new
//
//	fn main() {

#[macro_export]
macro_rules! lexer {
	() => {
		include! {concat!(env!("OUT_DIR"), "/", env!("CARGO_PKG_NAME"), "_lex", ".rs")}
	};
	($name:expr) => {
		include! {concat!(env!("OUT_DIR"), "/", $name, ".rs")}
	};
}
