// This module contains a struct and two macros to help with generating a parser as a part
// of a cargo build script and including it in the crate in question.

use crate::{BuilderError, Discriminant, ParserError, ParserSpec, Prim, Rules};
use rly_common::builders::{check_is_cargo_run, BuilderBase};
use std::{
	env,
	ffi::{OsStr, OsString},
	fs::File,
	io::{Error as IOError, Read},
	path::{Path, PathBuf},
};

const EXT: &'static str = "y";
const M_TYPE: &'static str = "parser";
const ENDING: &'static str = "parse";

/// A helper struct for creating parsers using build scripts
///
/// Instances of this stuct can be used in build scripts for creating parsers to be used
/// in a package. It has two hidden paramaters that affect its behaviour: the `name` used
/// by the builder when writing the finished parser, and the `location` of the source
/// file. These are private and can only be accessed or modified through the provided
/// methods which automatically run correctness checks on the provided values.
///
/// Note that `ParserBuilder`'s are only intended to be run by Cargo as a part of a build
/// script, and [`ParserBuilder::new`] will not return a builder unless the [environment
/// resembles that of a build script](ParserBuilder#environment). See the [official
/// documentation](https:///doc.rust-lang.org/cargo/reference/build-scripts.html) for more
/// details on build scripts.
///
/// # Name and Location
///
/// A [`ParserBuilder`] will write the parser in the current builds [`OUT_DIR`], with the
/// name `[name].rs`. `name` must be a valid filename, with no seperators[^seps] and no
/// extension. If `name` is not set, but `location` is, `name` defaults to the filename
/// for `location` minus the "`.y`" extension. Otherwise it defaults to the name of the
/// package with "`_parse`" added to the end.
///
/// [^seps]: "`/`" on Unix or Redox, and "`\`" on Windows. Note that, since this is
/// running as part of a build script, it is the host system that matters, not the
/// compilation target. This also means that you should be weary about using either `/` or
/// `\`, regardless of the platform: something that works fine on your system may fail to
/// compile when being built on a different platform!
///
/// The value for `location` must be an existing file ending with "`.y`". If `location` is
/// not set then it defaults to `name` with "`.y`" added to the end (if `name` and
/// `location` are not set, `name` default to the package name plus "`_parse`", so
/// `location would default to "`[package name]_parse.y`".)
///
/// # Environment
///
/// `ParserBuilder`'s rely on a number of environment variables to be set in order to
/// understand the package being built and where to write files. These should be
/// automatically set when the code is being run by Cargo as a part of a build script. For
/// safety, [`ParserBuilder::new()`] will check the environment and will not return a
/// builder unless it is properly configured.
///
/// ```
/// ///outside of build.rs
///
/// use parse::ParserBuilder;
///
/// assert!(ParserBuilder::new().is_none());
/// ```
///
/// # Reruns
///
/// Once the desired location for the source file of a parser is set it is recommended to
/// run [`set_rerun`](ParserBuilder::set_rerun) to set Cargo to monitor the source file
/// for changes and rerun the build script when it detects one since the last build.
///
/// [`OUT_DIR`]: https://doc.rust-lang.org/cargo/reference/environment-variables.html#environment-variables-cargo-sets-for-build-scripts

pub struct ParserBuilder {
	builder: BuilderBase,
	src: Option<String>,
}

impl ParserBuilder {
	/// Creates a new instance of a `ParserBuilder`. Returns [`None`] if the environement
	/// is not configured properly. See [here](ParserBuilder#environment) for more
	/// details.
	///
	/// # Example
	/// ``` no_run
	/// # use parse::ParserBuilder;
	/// let mut builder = ParserBuilder::new().unwrap();
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
			src: None,
		}
	}

	/// Returns the [name](ParserBuilder#name-and-location) of `self` if set. Returns
	/// [`None`] otherwise.
	pub fn name(&self) -> Option<&OsStr> {
		self.builder.name()
	}

	/// Returns the [location](ParserBuilder#name-and-location) of `self` if set. Returns
	/// [`None`] otherwise.
	pub fn location(&self) -> Option<&Path> {
		self.builder.location()
	}

	/// Returns the source string used by the builder to generate a parser, which is read
	/// from [`self.location()`](ParserBuilder::location).
	///
	/// Returns [`Some(src)`](Some) if a source string has been loaded, and [`None`]
	/// otherwise.
	///
	/// Note that, even if the [location](ParserBuilder#name-and-location) for `self` is
	/// set, this method may still return [`None`] if the location has not been loaded
	/// yet. For a version of this method that automatically loads the source, see
	/// [`load_file`](ParserBuilder::load_file).
	///
	/// # Example
	///
	/// ```no_run
	/// # use std::error::Error;
	/// # fn main() -> Result<(), Box<dyn Error>> {
	/// use parse::ParserBuilder;
	///
	/// let mut builder = ParserBuilder::new().unwrap();
	///
	/// builder
	/// 	.at_location("my_parser.y")?
	/// 	.load_file()?;
	///
	/// let source = builder.src().unwrap();
	/// # Ok(())
	/// # }
	pub fn src(&self) -> Option<&str> {
		self.src.as_ref().map(|s| s.as_str())
	}

	/// Attempts to set the name for `self` to `name`.
	///
	/// If `name` is a valid filename (see [here](ParserBuilder#name-and-location),) then
	/// this method returns a mutable reference to `self`, otherwise it returns an
	/// [`BuilderError`].
	///
	/// # Example
	/// ``` no_run
	/// # use std::error::Error;
	/// # fn main() -> Result<(), Box<dyn Error>> {
	/// use std::ffi::OsStr;
	/// use parse::ParserBuilder;
	/// let mut builder = ParserBuilder::new().unwrap();
	/// let builder_name = builder
	/// 	.with_name("my_parser")?
	/// 	.name();
	/// assert_eq!(builder_name, Some(OsStr::new("my_parser")));
	/// # Ok(())
	/// # }
	/// ```
	pub fn with_name<S: Into<OsString>>(&mut self, name: S) -> Result<&mut Self, BuilderError> {
		self.builder.with_name(name, M_TYPE, EXT)?;
		Ok(self)
	}

	/// Attempts to set the location for `self` to `location`.
	///
	/// If `location` is a valid path to a source file (see
	/// [here](ParserBuilder#name-and-location),) then this method returns a mutable
	/// reference to `self`, otherwise it returns an [`BuilderError`].
	///
	/// # Example
	/// ```no_run
	/// # fn main() -> Result<(), parse::BuilderError> {
	/// use std::path::Path;
	/// use parse::ParserBuilder;
	///
	/// let mut builder = ParserBuilder::new().unwrap();
	/// let builder_location = builder
	/// 	.at_location("lex-yacc/my_parser.y")?
	/// 	.location();
	///
	/// assert_eq!(builder_location, Some(Path::new("lex-yacc/my_parser.y")));
	/// # Ok(())
	/// # }
	/// ```
	pub fn at_location<S: Into<PathBuf>>(
		&mut self,
		location: S,
	) -> Result<&mut Self, BuilderError> {
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
	/// [here](ParserBuilder#name-and-location). Calling this method directly is usually
	/// unecessary, as the fields will automatically be set to their default values as
	/// necessary when building a parser. It can however be usefull for inspecting what
	/// the values _would_ be.
	///
	/// # Example
	/// ``` no_run
	/// use std::ffi::OsStr;
	/// use std::path::Path;
	/// use parse::ParserBuilder;
	///
	/// let mut builder = ParserBuilder::new().unwrap();
	/// builder.with_name("my_parser").unwrap();
	///
	/// assert_eq!(builder.location(), None);
	///
	/// builder.set_default_values();
	///
	/// assert_eq!(builder.name(), Some(OsStr::new("my_parser")));
	/// assert_eq!(builder.location(), Some(Path::new("my_parser.parse")));
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
	/// use std::error::Error;
	/// use parse::ParserBuilder;
	///
	/// fn main() -> Result<(), Box<dyn Error>> {
	/// 	let mut builder = ParserBuilder::new().unwrap();
	/// 	builder
	/// 		.with_name("my_parser")
	/// 		.unwrap()
	/// 		.build::<u32, u32>()?
	/// 		.set_rerun().unwrap();
	/// 	Ok(())
	/// }
	/// ```
	pub fn set_rerun(&self) -> Option<()> {
		self.builder.set_rerun_for_location()
	}

	/// Like [`load_file`](ParserBuilder::load_file), except it always reads the
	/// [location], even if a source text has already been loaded.
	///
	/// This may be usefull if, for instance, the [location] for `self` has been changed
	/// since loading a source file, and you want to make sure that the new location is
	/// loaded.
	///
	/// # Example
	///
	/// ```no_run
	/// # use std::error::Error;
	/// # fn main() -> Result<(), Box<dyn Error>> {
	/// use std::fs;
	/// use parse::ParserBuilder;
	///
	/// let mut builder = ParserBuilder::new().unwrap();
	///
	/// let old_source = builder
	/// 	.at_location("my_parser.y")?
	/// 	.load_file()?
	/// 	.to_string();
	///
	/// let new_source = fs::read_to_string("new_parser.y")?;
	///
	/// builder.at_location("new_parser.y")?;
	///
	/// assert_eq!(old_source, builder.load_file().unwrap());	// load_file returns the cached
	/// 														// content of "my_parser.y",
	/// 														// instead of "new_parser.y"
	///
	/// assert_eq!(new_source, builder.force_load_file()?);		// loads and returns the content
	/// 														// of "new_parser.y"
	///
	/// assert_eq!(new_source, builder.load_file().unwrap());	// load_file now returns the
	/// 														// cached content of
	/// 														// "new_parser.y"
	/// # Ok(())
	/// # }
	/// ```
	///
	/// [location]: ParserBuilder#name-and-location

	pub fn force_load_file(&mut self) -> Result<&str, IOError> {
		self.set_default_values();
		self.set_rerun().unwrap();
		let mut fin = File::open(self.location().unwrap())?;
		let mut src = String::new();
		fin.read_to_string(&mut src)?;
		self.src = Some(src);
		Ok(self.src().unwrap())
	}

	/// Loads and returns the text of the source file at the
	/// [location](ParserBuilder#name-and-location) for `self`.
	///
	/// If the source file has already been loaded, this method returns the cached text of
	/// that file, rather than loading it again. For the version that reloads the source
	/// file, see [`force_load_file`](ParserBuilder::force_load_file).
	///
	/// # Example
	///
	/// ```no_run
	/// # use std::error::Error;
	/// # fn main() -> Result<(), Box<dyn Error>> {
	/// use parse::ParserBuilder;
	///
	/// let mut builder = ParserBuilder::new().unwrap();
	///
	/// let location_content = builder
	/// 	.at_location("my_parser.y")?
	/// 	.load_file()?
	/// 	.to_string();
	///
	/// let source = builder.src().unwrap();
	///
	/// assert_eq!(location_content, source);
	/// # Ok(())
	/// # }
	pub fn load_file(&mut self) -> Result<&str, IOError> {
		if self.src().is_some() {
			Ok(self.src().unwrap())
		} else {
			self.force_load_file()
		}
	}

	/// Scans [`self.src()`] and attempts to parse it into a
	/// [`Rules`](crate::Rules).
	///
	/// If [`self.src()`] is [`None`], then this function returns `None`, otherwise it
	/// returns the [`Result`] of parsing `self.src()`.
	///
	/// # Example
	///
	/// ```no_run
	/// # use std::error::Error;
	/// # fn main() -> Result<(), Box<dyn Error>> {
	/// use parse::ParserBuilder;
	///
	/// let mut builder = ParserBuilder::new().unwrap();
	///
	/// builder.load_file()?;
	///
	/// let rules = builder.scan_src::<u32, u32>().unwrap()?;
	/// # Ok(())
	/// # }
	/// ```
	///
	/// [`self.src()`]: ParserBuilder::src
	pub fn scan_src<N: Prim + Discriminant, T: Prim + Discriminant>(
		&self,
	) -> Option<Result<Rules<'_, N, T>, ParserError>> {
		self.src().map(|src| Rules::new(src))
	}

	/// Like [`scan_src`](ParserBuilder::scan_src) except it loads a source from the
	/// [location](ParserBuilder#name-and-location) if [`self.src()`](ParserBuilder::src)
	/// is [`None`].
	///
	/// # Example
	///
	/// ```no_run
	/// # use std::error::Error;
	/// # fn main() -> Result<(), Box<dyn Error>> {
	/// use parse::ParserBuilder;
	///
	/// let mut builder = ParserBuilder::new().unwrap();
	///
	/// let rules = builder.get_rules::<u32, u32>()?;
	/// # Ok(())
	/// # }
	/// ```
	pub fn get_rules<N: Prim + Discriminant, T: Prim + Discriminant>(
		&mut self,
	) -> Result<Rules<'_, N, T>, ParserError> {
		let src = self.load_file()?;
		Ok(Rules::new(src)?)
	}

	fn write_module_with_name<N: Prim + Discriminant, T: Prim + Discriminant, P: AsRef<Path>>(
		&self,
		spec: &ParserSpec<'_, '_, N, T>,
		name: P,
	) -> Result<(), IOError> {
		let mut out_loc = PathBuf::from(env::var_os("OUT_DIR").unwrap());
		out_loc.push(name);
		out_loc.set_extension("rs");
		let fout = File::create(out_loc)?;
		spec.write(fout)
	}

	/// Builds the parser, reading from the file at
	/// [`location`](ParserBuilder#name-and-location) and writing a file with the
	/// appropriate [`name`](ParserBuilder#name-and-location) to the out dir set by Cargo.
	///
	/// # Example
	///
	/// ```no_run
	/// ///in build.rs
	///
	/// use std::error::Error;
	/// use parse::ParserBuilder;
	///
	/// fn main() -> Result<(), Box<dyn Error>> {
	/// 	let mut builder = ParserBuilder::new().unwrap();
	/// 	builder
	/// 		.build::<u32, u32>()?
	/// 		.set_rerun().unwrap();
	/// 	Ok(())
	/// }
	/// ```
	pub fn build<N, T>(&mut self) -> Result<&mut Self, ParserError>
	where
		N: Prim + Discriminant,
		T: Prim + Discriminant,
	{
		self.load_file()?;
		let rules = self.scan_src::<N, T>().unwrap()?;
		self.write_module_with_name(&rules.gen_spec(), self.name().unwrap())?;
		Ok(self)
	}

	/// Builds a parser using the default [name][nl] and [location][nl].
	///
	/// Equivalent to calling [`ParserBuilder::new()`] and then calling
	/// [`build`](ParserBuilder::build) on the result.
	///
	/// # Panic
	///
	/// This function panics if not being run by cargo in a build script.
	///
	/// ```should_panic
	/// use parse::ParserBuilder;
	///
	/// ParserBuilder::build_parser::<u32, u32>();
	/// ```
	///
	/// [nl]: ParserBuilder#name-and-location

	pub fn build_parser<N, T>() -> Result<Self, ParserError>
	where
		N: Prim + Discriminant,
		T: Prim + Discriminant,
	{
		let mut builder =
			Self::new().expect("ParserBuilder::build_parser not being run in a build script");
		builder.build::<N, T>()?;
		Ok(builder)
	}
}

/// A macro allowing for building parsers with with specific discriminants.
///
/// This macro should not be used directly, instead use the [`build_parser!`] macro, which
/// has more functionality.
#[macro_export]
macro_rules! build_parser_with {
	($(name = $name: expr,)? $(location = $location: expr,)? N = $N: ty, T = $T: ty) => {
		{
			use ::parse::ParserBuilder;
			let mut builder = ParserBuilder::new()
				.expect("'parse::build_parser!' not being run in a build script");
			$(builder.with_name($name);)?
			$(builder.at_location($location);)?
			match builder.build::<$N, $T>() {
				Ok(_builder) => {
					builder.set_rerun().unwrap();
					Ok(builder)
				}
				Err(e) => Err(e),
			}
		}
	};
}

/// A convenience macro for building parsers in a [build script].
///
/// This macro can optionally take, in order, a `name`, `location`, non-terminal discriminant type
/// `N`, and terminal discriminant type `T`[^name_and_loc]. If `N` or `T` aren't
/// specified, they default to [`u32`]. `name` and `location` have the same defaults as
/// described in [`ParserBuilder`][nl].
///
/// `name` should be of a type that implements [`Into<OsString>`], and `location` should
/// be of a type that implements [`Into<PathBuf>`], as described at
/// [`ParserBuilder::with_name`] and [`ParserBuilder::at_location`], respectively.
///
/// It may also take a `discriminant` type in place of both `N` and `T`, which, if
/// specified, acts as the discriminant for both non-terminals and terminals.
///
/// [^name_and_loc]: See the documentation on [`ParserBuilder`][nl] for more information
/// on what `name` and `location` do, and what their requirements are.
///
/// Arguments are given in the form `var = $var`, seperated by commas. For example:
///
/// ```no_run
/// // in build.rs
///
/// parse::build_parser!(name = "my_parser", T = u8);
/// ```
///
/// This macro returns a [`Result<ParserBuilder, ParserError>`] containing either the
/// [`ParserBuilder`] used in constructing the parser, or any [`ParserError`]'s incurred.
///
/// ```no_run
/// // in build.rs
///
/// use std::fs;
///
/// fn main() {
/// 	let source = fs::read_to_string("my_parser.y")
/// 		.expect("error reading 'my_parser.y'");
///
/// 	let builder = parse::build_parser!(location = "my_parser.y")
/// 		.expect("error processing parser file 'my_parser.y'");
///
/// 	assert_eq!(source, builder.src().unwrap());
/// }
/// ```
///
/// # Panic
///
/// Since this macro is essentially a wrapper for [`ParserBuilder`], it panics when not
/// being run in a build script. See the documentation on [`ParserBuilder::build_parser`]
/// or [here](ParserBuilder#environment) for more details.
///
/// ```should_panic
/// // in src/main.rs
///
/// parse::build_parser!();
/// ```
///
/// # Reruns
///
/// This macro automatically runs [`ParserBuilder::set_rerun`] to set cargo to watch the
/// [`location`][nl] for changes and rerun the build script if it notices any.
///
/// Note that this also means that the build script will not be rerun _unless_ cargo
/// detects any changes in a file it has been specifically told to watch. Keep this in
/// mind if you have other components to the build script than building a parser. See the
/// [documentation][rerun] for more.
///
/// # Examples
///
/// Basic usage and default arguments.
///
/// ```no_run
/// # use parse::ParserError;
/// # fn main() -> Result<(), ParserError> {
/// // builds a parser with name "my_parser", location "parser.y", non-terminal
/// // discriminant u8, and terminal discriminant u16
/// parse::build_parser!(name = "my_parser", location = "parser.y", N = u8, T = u16)?;
///
/// // builds a parser with name "alt_parser", default location (in this instance,
/// // "alt_parser.y",) default non-terminal discriminant of u32, and terminal
/// // discriminant u8
/// parse::build_parser!(name = "alt_parser", T = u8)?;
/// Ok(())
/// # }
/// ```
///
/// Using `discriminant`.
///
/// ```no_run
/// # use parse::ParserError;
/// # fn main() -> Result<(), ParserError> {
/// // builds a parser with default name and location, and with u16 for both discriminant
/// // types
/// // parse::build_parser!(N = u16, T = u16)?;
///
/// // same thing as above, but more concise
/// parse::build_parser!(discriminant = u16)?;
/// Ok(())
/// # }
/// ```
///
/// It is an error to give the arguments out of order.
///
/// ```compile_fail
/// # use parse::ParserError;
/// # fn main() -> Result<(), ParserError> {
/// parse::build_parser!(location = "parser.y", name = "my_parser")?;
/// Ok(())
/// # }
/// ```
///
/// It is also an error to use `discriminant` with `N` or `T`.
///
/// ```compile_fail
/// # use parse::ParserError;
/// # fn main() -> Result<(), ParserError> {
/// parser::build_parser!(discriminant = u8, N = u8)?;
/// Ok(())
/// # }
/// ```
///
/// [build script]: https://doc.rust-lang.org/cargo/reference/build-scripts.html
/// [nl]: ParserBuilder#name-and-location
/// [rerun]: https://doc.rust-lang.org/cargo/reference/build-scripts.html#change-detection

#[macro_export]
macro_rules! build_parser {
	($(name = $name: expr $(, location = $location: expr)?$(,)?)?) => {
		::parse::build_parser_with!($(name = $name, $(location = $location,)?)? N = u32, T = u32)
	};

	(location = $location: expr$(,)?) => {
		::parse::build_parser_with!(location = $location, N = u32, T = u32)
	};

//	($(name = $name: expr,)? $(location = $location: expr,)?) => {
//		::parse::build_parser_with!($(name = $name,)? $(location = $location,)? N = u32, T = u32)
//	};

	($(name = $name: expr,)? $(location = $location: expr,)? discriminant = $discriminant: ty$(,)?) => {
		::parse::build_parser_with!($(name = $name,)? $(location = $location,)? N = $discriminant, T = $discriminant)
	};

	($(name = $name: expr,)? $(location = $location: expr,)? N = $N: ty$(,)?) => {
		::parse::build_parser_with!($(name = $name,)? $(location = $location,)? N = $N, T = u32)
	};

	($(name = $name: expr,)? $(location = $location: expr,)? T = $T: ty$(,)?) => {
		::parse::build_parser_with!($(name = $name,)? $(location = $location,)? N = u32, T = $T)
	};

	($(name = $name: expr,)? $(location = $location: expr,)? N = $N: ty, T = $T: ty$(,)?) => {
		::parse::build_parser_with!($(name = $name,)? $(location = $location,)? N = $N, T = $T)
	};
}

/// A macro for including a parser generated by a [`ParserBuilder`] in a project.
///
/// It optionally accepts an argument specifying the
/// [`name`](ParserBuilder#name-and-location) of the parser to include, otherwise it uses
/// the same default as `ParserBuilder`
///
/// # Example
///
/// ```no_run
/// // in build.rs
/// use parse::ParserError;
///
/// fn main() -> Result<(), ParserError> {
/// 	parse::build_parser!(name = "my_parser")?;
/// 	Ok(())
/// }
/// ```
///
/// ```ignore
/// // in src/main.rs
///
/// parse::parser!("my_parser");
/// use parser::Parser;
/// ```
#[macro_export]
macro_rules! parser {
	() => {
		include! {concat!(env!("OUT_DIR"), "/", env!("CARGO_PKG_NAME"), "_parse", ".rs")}
	};
	($name:expr) => {
		include! {concat!(env!("OUT_DIR"), "/", $name, ".rs")}
	};
}

//	pub fn with_name<S: Into<OsString>>(&mut self, name: S) -> Result<&mut Self, Error> {
//		self.name = Some(check_name(name.into())?);
//		Ok(self)
//	}
//
//	pub fn at_location<S: Into<PathBuf>>(&mut self, location: S) -> Result<&mut Self, Error> {
//		self.location = Some(check_location(location.into())?);
//		Ok(self)
//	}
