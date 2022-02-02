//! This module contains the base functionality for `lex::LexerBuilder` and
//! `parse::ParserBuilder`.
//!
//! With the possible exception of [`Error`] and [`ErrorKind`], you most likely will not
//! use anything in this module, instead using the functionality exposed in `lex` or
//! `parse`. However, the items here may be usefull for making your own `Builder`'s.

use std::{
	env,
	ffi::{OsStr, OsString},
	fmt::Display,
	path::{Path, PathBuf},
};

/// This is the base struct for the `ParserBuilder` and `LexerBuilder` types.
pub struct BuilderBase {
	/// Name of the file to be written to the outdir.
	name: Option<OsString>,
	/// Location of source file to read from.
	location: Option<PathBuf>,
}

/// Tries to determin if it's being executed by cargo as a part of a [build script].
///
/// If, as far as it can tell, it is being run by a build scrip, it returns [`true`].
/// Otherwise it returns [`false`].
///
/// # Example
///
/// ```
/// use rly_common::builders;
/// assert!(!builders::check_is_cargo_run());
/// ```
///
/// [build script]: https://doc.rust-lang.org/cargo/reference/build-scripts.html
pub fn check_is_cargo_run() -> bool {
	let is_set = |s| env::var_os(s).is_some();
	// Checks all the variables used by Builders as well as 'TARGET' to make sure it's not
	// running as a test or with 'cargo run' in a package with a build script.
	is_set("CARGO_PKG_NAME") && is_set("OUT_DIR") && is_set("TARGET")
}

// Gets the environment variable 'k' if set, otherwise panics with "the variable '<k>' was
// unexpectedly unset".
//
// Used as a convenience function for inspecting environment variables that should have
// been set.
fn get_cargo_var<K: AsRef<OsStr> + ?Sized>(k: &K) -> OsString {
	env::var_os(k)
		.unwrap_or_else(|| panic!("the variable '{:?}' was unexpectedly unset", k.as_ref()))
}

// Gets the default name for a builder to use (name of the package plus "_<end>" for the
// arg 'end'.)
fn default_name<T: AsRef<OsStr>>(end: T) -> Option<OsString> {
	let mut name = get_cargo_var("CARGO_PKG_NAME");
	name.push("_");
	name.push(end);
	Some(name)
}

impl BuilderBase {
	/// Creates a new instance of [`BuilderBase`] with [`name`] and [`location`] set to
	/// [`None`].
	///
	/// [`name`]: Self::name
	/// [`location`]: Self::location
	pub fn new() -> Self {
		Self {
			name: None,
			location: None,
		}
	}

	/// Returns the [`name`] used by the builder.
	///
	/// [`name`]: Self::name
	pub fn name(&self) -> Option<&OsStr> {
		self.name.as_ref().map(OsString::as_os_str)
	}

	/// Returns the [`location`] used by the builder.
	///
	/// [`location`]: Self::location
	pub fn location(&self) -> Option<&Path> {
		self.location.as_ref().map(PathBuf::as_path)
	}

	/// Attempts to set the value of [`self.name`](Self::name) to `name`.
	///
	/// If `name` has no path components and no file extension, then the method changes
	/// [`self.name`](Self::name) accordingly and returns `Ok(self)`. Otherwise returns an
	/// [`Error`] with a message depending in `module_type` and `file_extension`.
	pub fn with_name<S: Into<OsString>, T: Display, U: Display>(
		&mut self,
		name: S,
		module_type: T,
		file_extension: U,
	) -> Result<&mut Self, Error> {
		self.name = Some(check_name(name.into(), module_type, file_extension)?);
		Ok(self)
	}

	/// Attempts to set the value of [`self.location`](Self::location) to `location`.
	///
	/// If `location` is a [`Path`] to an existing file with extension `file_extension`,
	/// then the method changes [`self.location`](Self::location) accordingly and returns
	/// `Ok(self)`. Otherwise returns an [`Error`] with a message depending in
	/// `module_type` and `file_extension`.
	pub fn at_location<S: Into<PathBuf>, T: Display, U: Display>(
		&mut self,
		location: S,
		module_type: T,
		file_extension: U,
	) -> Result<&mut Self, Error> {
		self.location = Some(check_location(
			location.into(),
			module_type,
			file_extension,
		)?);
		Ok(self)
	}

	// Attempts to generate a default 'name' for self from self.location. Returns the file
	// stem of self.location
	fn name_from_path(&self) -> Option<OsString> {
		Some(self.location.as_ref()?.file_stem()?.to_os_string())
	}

	// Attempts to generate a default location for self from self.name. Returns self.name
	// with extention 'ext'. Panics if self.name is None.
	fn path_from_name<S: AsRef<OsStr> + ?Sized>(&self, ext: &S) -> PathBuf {
		let name = &self.name.as_ref().unwrap();
		let ext = Path::new(ext);
		let mut path = PathBuf::new();
		path.set_file_name(name);
		path.set_extension(ext);
		path
	}

	/// Sets [`self.name`](Self::name) to a default value.
	///
	/// The default value is [`self.location`](Self::location) if set, and the name of the
	/// package being built package plus "`_<end>`" if not.
	pub fn set_name<T: AsRef<OsStr>>(&mut self, end: T) {
		if self.name.is_none() {
			self.name = self.name_from_path().or_else(|| default_name(end));
		};
	}

	/// Sets [`self.name`](Self::name) to a default value.
	///
	/// The defulat value is [`self.name`] plus the extension `ext`.
	///
	/// # Panics
	///
	/// Panics if [`self.name`](Self::name) is [`None`].
	///
	/// ## Example
	///
	/// ```should_panic
	/// use rly_common::builders::BuilderBase;
	/// let mut builder = BuilderBase::new();
	/// builder.set_path("example")             // panics because 'builder.name' is 'None'
	/// ```
	pub fn set_path<S: AsRef<OsStr> + ?Sized>(&mut self, ext: &S) {
		if self.location.is_none() {
			self.location = Some(self.path_from_name(ext));
		}
	}

	/// Tells cargo to watch [`self.location`] for changes and rerun the build script if
	/// it detects any.
	///
	/// Returns [`Some`] if [`self.location`] is set and the method therefore is
	/// successful. If [`self.location`] is not set, it returns [`None`] and cargo is not
	/// set to watch anything for changes.
	///
	/// [`self.location`]: Self::location
	pub fn set_rerun_for_location(&self) -> Option<()> {
		let display = self.location()?.display();
		debug_assert_eq!(Path::new(&format!("{}", display)), self.location()?);
		Some(println!("cargo:rerun-if-changed={}", display))
	}
}

// Returns Ok(name) if is_valid_name(&name), otherwise returns and invalid_name error.
fn check_name<T: Display, U: Display>(
	name: OsString,
	module_type: T,
	file_ext: U,
) -> Result<OsString, Error> {
	case(is_valid_name(&name), name, |name| {
		Error::invalid_name(name, module_type.to_string(), file_ext.to_string())
	})
}

fn is_valid_name(name: &OsStr) -> bool {
	name == match Path::new(name).file_stem() {
		Some(s) => s,
		None => return false,
	}
}

// Returns Ok(loc) if 'loc' is a file and has 'file_ext' as it extension, otherwise
// returns an error.
fn check_location<T: Display, U: Display>(
	loc: PathBuf,
	module_type: T,
	file_ext: U,
) -> Result<PathBuf, Error> {
	let loc = case(loc.is_file(), loc, |l| {
		Error::location_is_dir(l, module_type.to_string(), file_ext.to_string())
	})?;
	case(
		loc.extension() == Some(OsStr::new(&file_ext.to_string())),
		loc,
		|l| Error::invalid_file_extension(l, module_type.to_string(), file_ext.to_string()),
	)
}

fn case<T, F: FnOnce(T) -> Error>(cond: bool, val: T, err: F) -> Result<T, Error> {
	if cond {
		Ok(val)
	} else {
		Err(err(val))
	}
}

mod error {
	use std::{error, ffi::OsString, fmt, path::PathBuf};

	/// The kind of errors used by [`Error`].
	#[derive(Debug, PartialEq, Eq)]
	pub enum ErrorKind {
		InvalidName(OsString),
		InvalidFileExtension(PathBuf),
		LocationIsDir(PathBuf),
	}

	/// The type of errors returned by [`Builders`](super::BuilderBase) including
	/// LexerBuilder and ParserBuilder.
	///
	/// `Error`'s come in three different [`kinds`](ErrorKind): [`InvalidName`],
	/// [`InvalidFileExtension`], and [`LocationIsDir`] (for when you attempt to assign a
	/// directory as a [builder location](super::BuilderBase::location) using
	/// [`BuilderBase::at_location`](super::BuilderBase::at_location) or a derived method
	/// with `LexerBuilder` or `ParserBuilder`.)
	///
	/// The [kind](ErrorKind) of and `Error` can be inspected using [`Error::kind`]. For
	/// example:
	///
	/// ```
	/// use std::ffi::OsString;
	/// use rly_common::builders::{BuilderBase, ErrorKind};
	///
	/// let mut builder = BuilderBase::new();
	///
	/// // "foo/bar" is an invalid name (at least on unix) because it has a path seperator "/" in
	/// // it
	/// let error = builder.with_name("foo/bar", "lexer", ".lex").err().unwrap();
	///
	/// let name = OsString::from("foo/bar");
	/// let error_kind = ErrorKind::InvalidName(name);
	///
	/// assert_eq!(error.kind(), &error_kind);
	/// ```
	///
	/// [`InvalidName`]: ErrorKind::InvalidName
	/// [`InvalidFileExtension`]: ErrorKind::InvalidFileExtension
	/// [`LocationIsDir`]: ErrorKind::LocationIsDir
	#[derive(Debug)]
	pub struct Error {
		kind: ErrorKind,
		module_type: String,
		file_extension: String,
	}

	impl Error {
		/// Creates a new [`Error`] with kind [`ErrorKind::InvalidName`]
		pub fn invalid_name(name: OsString, module_type: String, file_extension: String) -> Self {
			Self {
				kind: ErrorKind::InvalidName(name),
				module_type,
				file_extension,
			}
		}

		/// Creates a new [`Error`] with kind [`ErrorKind::InvalidFileExtension`]
		pub fn invalid_file_extension(
			name: PathBuf,
			module_type: String,
			file_extension: String,
		) -> Self {
			Self {
				kind: ErrorKind::InvalidFileExtension(name),
				module_type,
				file_extension,
			}
		}

		/// Creates a new [`Error`] with kind [`ErrorKind::LocationIsDir`]
		pub fn location_is_dir(name: PathBuf, module_type: String, file_extension: String) -> Self {
			Self {
				kind: ErrorKind::LocationIsDir(name),
				module_type,
				file_extension,
			}
		}

		/// Returns the [kind](ErrorKind) used by `self`.
		///
		/// # Example
		///
		/// ```
		/// use std::path::PathBuf;
		/// use rly_common::builders::{BuilderBase, ErrorKind};
		///
		/// let mut builder = BuilderBase::new();
		///
		/// let error = builder.at_location("/", "parser", ".y").err().unwrap();
		///
		/// let name = PathBuf::from("/");
		///
		/// assert_eq!(error.kind(), &ErrorKind::LocationIsDir(name));
		/// ```
		pub fn kind(&self) -> &ErrorKind {
			&self.kind
		}

		/// Returns the module type used by the error. Used in formatting error messages.
		///
		/// # Example
		///
		/// ```
		/// use std::path::PathBuf;
		/// use rly_common::builders::Error;
		///
		/// let error = Error::invalid_file_extension(PathBuf::from("foo.text"), "lexer".to_string(), "lex".to_string());
		///
		/// let error_message = format!("{}", error);
		///
		/// assert_eq!(
		/// 	error_message,
		/// 	"Invalid file 'foo.text' given for lexer specification: file must end in '.lex'",
		/// );
		///
		/// assert_eq!(error.module_type(), "lexer");
		/// ```
		pub fn module_type(&self) -> &String {
			&self.module_type
		}

		/// Returns the file extension used by the error. Used in formatting error messages.
		///
		/// # Example
		///
		/// ```
		/// use std::path::PathBuf;
		/// use rly_common::builders::Error;
		///
		/// let error = Error::invalid_file_extension(PathBuf::from("foo.text"), "lexer".to_string(), "lex".to_string());
		///
		/// let error_message = format!("{}", error);
		///
		/// assert_eq!(
		/// 	error_message,
		/// 	"Invalid file 'foo.text' given for lexer specification: file must end in '.lex'",
		/// );
		///
		/// assert_eq!(error.file_extension(), "lex");
		/// ```
		pub fn file_extension(&self) -> &String {
			&self.file_extension
		}
	}

	impl fmt::Display for Error {
		fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
			match self.kind() {
				ErrorKind::InvalidName(s) => write!(
					f,
					"Invalid {mod_type} name '{name}'. Name must be a valid file name with no extension and not a path",
					name = s.to_string_lossy(),
					mod_type = self.module_type()),
				ErrorKind::InvalidFileExtension(p) => write!(
					f,
					"Invalid file '{file}' given for {mod_type} specification: file must end in '.{ext}'",
					file = p.display(),
					mod_type = self.module_type(),
					ext = self.file_extension()),
				ErrorKind::LocationIsDir(p) => write!(
					f,
					"{mod_type} location must be a file ending in '.{ext}', not a directory: {file}",
					file = p.display(),
					mod_type = FirstCapital(self.module_type()),
					ext = self.file_extension()),
			}
		}
	}

	// a wrapper struct that displays its content with the first character capitalized
	struct FirstCapital<'a>(&'a str);

	impl<'a> fmt::Display for FirstCapital<'a> {
		fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
			let s = self.0;
			if s.len() == 0 {
				write!(f, "{}", s)
			} else {
				let mut char_indices = s.char_indices();
				let c = char_indices.next().unwrap().1;
				let n = char_indices.next().map(|p| p.0).unwrap_or_else(|| s.len());
				write!(f, "{}{}", c.to_uppercase(), &s[n..])
			}
		}
	}

	impl error::Error for Error {}

	#[cfg(test)]
	mod tests {
		#[test]
		fn test_first_capital() {
			use super::FirstCapital;
			let test = |l, u| {
				let s = format!("{}", FirstCapital(l));
				assert_eq!(s, u);
			};
			test("testing", "Testing");
			test("te", "Te");
			test("t", "T");
			test("", "");
		}
	}
}

pub use error::{Error, ErrorKind};

#[cfg(test)]
mod tests {
	use super::BuilderBase;

	#[test]
	fn test_default() {
		let mut builder = BuilderBase::new();
		builder.set_name("_lex");
	}

	#[test]
	fn test_is_valid_name() {
		use std::ffi::OsStr;
		let f = |s: &str| super::is_valid_name(OsStr::new(s));
		assert!(f("foo"));
		assert!(!f("/foo"));
		assert!(!f("foo/"));
		assert!(!f("foo/bar"));
		assert!(!f("foo.text"));
	}
}
