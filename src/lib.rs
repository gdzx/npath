#![feature(osstring_ascii)]

//! Normalized Paths
//!
//! `npath` is a Rust library providing methods for cross-platform lexical path processing and
//! normalization. These methods are implemented in extension traits to [`Path`] and [`PathBuf`].
//!
//! # Usage
//!
//! Add `npath` to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! npath = { git = "https://github.com/gdzx/npath" }
//! ```
//!
//! Import the following traits:
//!
//! ```
//! use npath::{NormPathExt, NormPathBufExt};
//! ```
//!
//! # Overview
//!
//! [`std::path`] lacks methods for lexical path processing, which:
//!
//! - Do not rely on system calls.
//! - Remove the need to handle I/O errors.
//! - Support more operations.
//! - Allow to process paths to files or directories that do not exist.
//!
//! The following sections outline the main features this library provides.
//!
//! ## Joining paths
//!
//! One of the most basic operation is joining two paths. Trying to get
//! `C:\Users\User\Documents\C:\foo` using [`Path::join`] can yield an entirely different path:
//!
//! ```
//! use std::path::Path;
//!
//! # if cfg!(windows) {
//! assert_eq!(
//!     Path::new(r"C:\Users\User\Documents").join(r"C:\foo"),
//!     Path::new(r"C:\foo"),
//! );
//! # }
//! ```
//!
//! Although paths are represented by strings, [`Path::join`] is a high-level method that processes
//! its second argument to determine if it is absolute. On the contrary, the fundamental operation
//! of appending a path to another by string concatenation is called a *lexical join*.
//!
//! [`NormPathExt::lexical_join`] joins two paths with an operation similar to string
//! concatenation, only adding a path separator in-between if needed. [`Path::join`] is a
//! refinement of a lexical join:
//!
//! ```
//! use std::path::{Path, PathBuf};
//! use npath::NormPathExt;
//!
//! fn join(base: &Path, path: &Path) -> PathBuf {
//!     if path.is_absolute() {
//!         path.to_path_buf()
//!     } else {
//!         base.lexical_join(path)
//!     }
//! }
//! ```
//!
//! ## Normalization
//!
//! If you want to check whether two paths are identical, you need to transform them into a form
//! that allows comparison. Rust provides [`std::fs::canonicalize`], which returns the true
//! canonical path on the filesystem:
//!
//! ```no_run
//! use std::path::Path;
//!
//! # fn main() -> std::io::Result<()> {
//! assert_eq!(
//!     Path::new("/srv").join("file.txt").canonicalize()?,
//!     Path::new("/srv").join("bar//../file.txt").canonicalize()?,
//! );
//! # Ok(())
//! # }
//! ```
//!
//! [`Path::canonicalize`] requires a concrete path (that refers to an existing file or directory
//! on the filesystem) or it will return an error. [`NormPathExt::normalized`] eliminates the
//! intermediate components `.`, `..`, or duplicate `/` through pure lexical processing. It is the
//! building block for comparing paths, ensuring a path is restricted to some base path, or for
//! finding the relative path between two paths. It yields the shortest lexically equivalent path:
//! it is *normalized*.
//!
//! [`NormPathExt::resolved`] uses both approaches: the longest prefix whose individual components
//! exist is canonicalized, the remaining path is normalized, and adjoined to it. The purpose is to
//! circumvent the limitations of normalization, while still being able to apply it to paths that
//! do not exist.
//!
//! ## Restricting paths
//!
//! Web servers are exposed to path traversal vulnerabilities that allow an attacker to access
//! files outside of some base directory. [`Path::join`] with the base directory `/srv` and a
//! user-supplied path can yield a path outside of `/srv`:
//!
//! ```
//! use std::path::{Path, PathBuf};
//!
//! assert_eq!(
//!     Path::new("/srv").join("/etc/passwd"),
//!     PathBuf::from("/etc/passwd")
//! );
//! ```
//!
//! Only accepting relative paths is not sufficient:
//!
//! ```
//! use std::path::{Path, PathBuf};
//! use npath::NormPathExt;
//!
//! assert_eq!(
//!     Path::new("/srv").join("../etc/passwd").normalized(),
//!     PathBuf::from("/etc/passwd")
//! );
//! ```
//!
//! Stripping `..` prefixes is not enough either:
//!
//! ```
//! use std::path::{Path, PathBuf};
//! use npath::NormPathExt;
//!
//! assert_eq!(
//!     Path::new("/srv").join("foo/../../etc/passwd").normalized(),
//!     PathBuf::from("/etc/passwd") // /etc/passwd
//! );
//! ```
//!
//! If the user-provided path only needs to be a single path component, the programmer can forbid
//! any string containing paths separators and filter `..`. Otherwise, the inner `..` components
//! needs to be simplified, and the prefix `..` components eliminated. Normalization is at the core
//! of the following methods:
//!
//! - [`NormPathExt::is_inside`]: checks if a path is a descendant of another.
//! - [`NormPathExt::rooted_join`]: joins two paths, the result is restricted to the first one.
//!
//! # Limitations
//!
//! Lexical path processing, being limited to operations without interacting with the system, can
//! change the concrete object a path points to.
//!
//! ## Normalization
//!
//! If `/a/b` is a symlink to `/d/e`, then for `/a/b/../c`:
//!
//! - [`Path::canonicalize`] returns `/d/c` if it exists, an I/O error otherwise.
//! - [`NormPathExt::normalized`] returns `/a/c`.
//! - [`NormPathExt::resolved`] returns `/d/c`, regardless of whether it exists or not.
//!
//! ## Windows
//!
//! Common Windows filesystems are case-insensitive, where `foo.txt`, `FOO.TXT`, and `fOo.txT`
//! point to the same file. Additionally, the mapping from lowercase to uppercase letters in the
//! Unicode range is stored in the filesystem, and depends on the date it was created on. This
//! library performs case-insensitive comparisons only for the ASCII character set (the first 128
//! Unicode characters).
//!
//! # TODO
//!
//! - Special Windows prefixes.

use std::env;
use std::ffi::OsStr;
use std::io::{Error, ErrorKind, Result};
use std::path::{Component, Path, PathBuf, Prefix, PrefixComponent};

/// Extension trait for [`PathBuf`].
pub trait NormPathBufExt {
    /// Lexically appends `path` to `self`.
    ///
    /// See [`NormPathExt::lexical_join`].
    fn lexical_push<P: AsRef<Path>>(&mut self, path: P);
}

impl NormPathBufExt for PathBuf {
    fn lexical_push<P: AsRef<Path>>(&mut self, path: P) {
        *self = self.lexical_join(path)
    }
}

/// Extension trait for [`Path`].
pub trait NormPathExt {
    /// Returns the absolute equivalent of `self`.
    ///
    /// - If `self` is absolute, it it is returned as is.
    /// - If `self` is relative, it is lexically joined to [`std::env::current_dir`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::path::{Path, PathBuf};
    /// use npath::NormPathExt;
    ///
    /// # if cfg!(unix) {
    /// assert_eq!(Path::new("/usr").absolute().unwrap(), PathBuf::from("/usr"));
    ///
    /// if let Ok(cwd) = std::env::current_dir() {
    ///     assert_eq!(Path::new("lib").absolute().unwrap(), cwd.lexical_join("lib"));
    /// }
    /// # }
    /// ```
    fn absolute(&self) -> Result<PathBuf>;

    /// Returns the last path component of `self`.
    ///
    /// See [`basename(3)`](http://man7.org/linux/man-pages/man3/basename.3.html).
    ///
    /// # Differences with [`Path::file_name`]
    ///
    /// - Always returns a path (eventually `/`, `.`, or `..`, when [`Path::file_name`] returns
    ///   `None`).
    /// - Returns a [`Path`] instead of an [`OsStr`](std::ffi::OsStr).
    ///
    /// # Examples
    ///
    /// ```
    /// use std::path::Path;
    /// use npath::NormPathExt;
    ///
    /// assert_eq!(Path::new("/usr/lib").base(), Path::new("lib"));
    /// assert_eq!(Path::new("/usr/").base(),    Path::new("usr"));
    /// assert_eq!(Path::new("usr/.").base(),    Path::new("."));
    /// assert_eq!(Path::new("usr").base(),      Path::new("usr"));
    /// assert_eq!(Path::new("/").base(),        Path::new("/"));
    /// assert_eq!(Path::new(".").base(),        Path::new("."));
    /// assert_eq!(Path::new("..").base(),       Path::new(".."));
    /// ```
    fn base(&self) -> &Path;

    /// Returns `self` up to, but not including, the final component.
    ///
    /// See [`dirname(3)`](http://man7.org/linux/man-pages/man3/dirname.3.html).
    ///
    /// # Differences with [`Path::parent`]
    ///
    /// Always returns a path (`/` when [`Path::parent`] returns `None`).
    ///
    /// # Examples
    ///
    /// ```
    /// use std::path::Path;
    /// use npath::NormPathExt;
    ///
    /// assert_eq!(Path::new("/usr/lib").dir(), Path::new("/usr"));
    /// assert_eq!(Path::new("/usr/").dir(),    Path::new("/"));
    /// assert_eq!(Path::new("usr/.").dir(),    Path::new("usr"));
    /// assert_eq!(Path::new("usr").dir(),      Path::new("."));
    /// assert_eq!(Path::new("/").dir(),        Path::new("/"));
    /// assert_eq!(Path::new(".").dir(),        Path::new("."));
    /// assert_eq!(Path::new("..").dir(),       Path::new("."));
    /// ```
    fn dir(&self) -> &Path;

    /// Returns whether `self` is lexically inside `base`.
    ///
    /// `self` is considered "lexically inside" `base` (or a descendant of `base`) if and only if:
    ///
    /// - `self` and `base` are both relative, or both absolute.
    /// - `self` does not have any component outside of `base`.
    ///
    /// Both paths are normalized before being compared.
    ///
    /// # Limitations
    ///
    /// When processing relative paths, if it is necessary to know the absolute path of either
    /// `base` or `self`, this method returns `false`:
    ///
    /// - If `base` is absolute and `self` is relative, or the opposite, there is no way to know
    ///   where `base` points to relative to `self` without using the absolute path of the CWD.
    /// - If `base` and `self` are relative, and `base` is re-entrant (a parent component `..` is
    ///   followed by a normal component), it is not possible to know whether `base` re-enters the
    ///   directory it just left, or if it branches off to a sibling directory, without using the
    ///   absolute path of the CWD. (Note that `self` can be re-entrant as shown in the examples.)
    ///
    /// To circumvent these limitations, you can ensure both path are absolute using one of these
    /// methods:
    ///
    /// - [`NormPathExt::absolute`]: with the limitations of [`NormPathExt::normalized`].
    /// - [`Path::canonicalize`]: without the limitations of [`NormPathExt::normalized`], but both
    ///   paths must exist on the filesystem.
    ///
    /// # Windows
    ///
    /// Paths components are compared in a case-insensitive way only for the ASCII character set
    /// (first 128 Unicode characters). For paths containing characters outside of this range, this
    /// method could return `false` even though `self` is inside `base` on the filesystem.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::path::Path;
    /// use npath::NormPathExt;
    ///
    /// // Both absolute
    /// assert!(Path::new("/srv").is_inside("/"));
    /// assert!(Path::new("/srv").is_inside("/srv"));
    /// assert!(Path::new("/srv/file.txt").is_inside("/srv"));
    ///
    /// // Both relative
    /// assert!(Path::new("srv").is_inside("srv"));
    /// assert!(Path::new("srv").is_inside("."));
    /// assert!(Path::new("srv").is_inside(".."));
    /// assert!(Path::new("../srv").is_inside("..")); // self is re-entrent
    ///
    /// // One absolute, the other relative
    /// assert!(!Path::new("file.txt").is_inside("/srv"));
    /// assert!(!Path::new("/srv/file.txt").is_inside("srv"));
    ///
    /// // self exits base
    /// assert!(!Path::new("/srv/..").is_inside("/srv"));
    ///
    /// // base is re-entrent
    /// assert!(!Path::new("srv").is_inside("../foo"));
    /// ```
    fn is_inside<P: AsRef<Path>>(&self, base: P) -> bool;

    /// Returns the normalized equivalent of `self`.
    ///
    /// The returned path is the shortest equivalent, normalized by pure lexical processing with
    /// the following rules:
    ///
    /// 1. Replace repeated `/` with a single one.
    /// 2. Eliminate `.` path components (the current directory).
    /// 3. Simplify inner `..` path components (the parent directory), including components
    ///    preceded by a rooted path (replace `/..` by `/`).
    ///
    /// # Differences with [`Path::canonicalize`]
    ///
    /// This function **does not touch the filesystem, ever**:
    ///
    /// - It does not resolve symlinks.
    /// - It does not check if files/directories exist.
    /// - If the given path is relative, it returns a relative path.
    ///
    /// # Limitations
    ///
    /// If `/a/b` is a symlink to `/d/e`, then for `/a/b/../c`:
    ///
    /// - [`Path::canonicalize`] returns `/d/c`.
    /// - [`NormPathExt::normalized`] returns `/a/c`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::path::{Path, PathBuf};
    /// use npath::NormPathExt;
    ///
    /// assert_eq!(Path::new("usr/lib").normalized(),                 PathBuf::from("usr/lib"));
    /// assert_eq!(Path::new("usr//lib").normalized(),                PathBuf::from("usr/lib"));
    /// assert_eq!(Path::new("usr/lib/.").normalized(),               PathBuf::from("usr/lib"));
    /// assert_eq!(Path::new("usr/lib/gcc/..").normalized(),          PathBuf::from("usr/lib"));
    /// assert_eq!(Path::new("/../usr/lib").normalized(),             PathBuf::from("/usr/lib"));
    /// assert_eq!(Path::new("/../usr/bin/../././/lib").normalized(), PathBuf::from("/usr/lib"));
    /// ```
    fn normalized(&self) -> PathBuf;

    /// Returns `path` lexically joined to `self`.
    ///
    /// # Differences with [`Path::join`]
    ///
    /// If `path` is absolute, it does not replace `self`.
    ///
    /// # Limitations
    ///
    /// On Windows, this method can turn paths without UNC prefixes into paths that have one.
    ///
    /// ```
    /// use std::path::{Component, Path, PathBuf};
    /// use npath::NormPathExt;
    ///
    /// fn has_prefix(path: &Path) -> bool {
    ///     path.components().next().map(|c| matches!(c, Component::Prefix(_))).unwrap_or(false)
    /// }
    ///
    /// # if cfg!(windows) {
    /// assert_eq!(
    ///     Path::new(r"\\server").lexical_join(r"c$\file.txt"),
    ///     PathBuf::from(r"\\server\c$\file.txt"),
    /// );
    /// # }
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// use std::path::{Path, PathBuf};
    /// use npath::NormPathExt;
    ///
    /// assert_eq!(
    ///     Path::new("/usr")
    ///         .lexical_join("bin")   // relative
    ///         .lexical_join("/cat"), // absolute
    ///     PathBuf::from("/usr/bin/cat")
    /// );
    ///
    /// assert_eq!(Path::new("/usr").lexical_join(".."), PathBuf::from("/usr/.."));
    /// ```
    fn lexical_join<P: AsRef<Path>>(&self, path: P) -> PathBuf;

    /// Returns the normalized relative path from `base` to `self`.
    ///
    /// If `self` cannot be made relative to `base`, the method returns `None`. The returned path,
    /// if any, satisfies: `base.join(path) == self`. Both paths are normalized before being
    /// compared, and the returned path is also normalized.
    ///
    /// # Limitations
    ///
    /// The method returns `None` when it cannot determine the intermediate path components to
    /// reach `self` from `base`, or fetching the CWD is required:
    ///
    /// - One path is absolute, but the other is relative.
    /// - The paths are relative, `base` is above `self`, and they are both above the CWD (knowing
    ///   its intermediate components is necessary).
    ///
    /// To circumvent these limitations, you can ensure both path are absolute using one of these
    /// methods:
    ///
    /// - [`NormPathExt::absolute`]: with the limitations of [`NormPathExt::normalized`].
    /// - [`Path::canonicalize`]: without the limitations of [`NormPathExt::normalized`], but both
    ///   paths must exist on the filesystem.
    ///
    /// # Windows
    ///
    /// There is an inescapable limitation when the paths refer to different locations (different
    /// drives, or network shares): there is no relative path between them because they are not in
    /// the same namespace.
    ///
    /// Paths components are compared in a case-insensitive way only for the ASCII character set
    /// (first 128 Unicode characters). For paths containing characters outside of this range, this
    /// method could return `None` even though there is a relative path from `base` to `self` on
    /// the filesystem.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::path::{Path, PathBuf};
    /// use npath::NormPathExt;
    ///
    /// assert_eq!(Path::new("/usr/lib").relative_to("/usr"), Some(PathBuf::from("lib")));
    /// assert_eq!(Path::new("usr/bin").relative_to("var"),   Some(PathBuf::from("../usr/bin")));
    ///
    /// assert_eq!(Path::new("lib").relative_to("/usr"), None);
    /// assert_eq!(Path::new("/usr").relative_to("var"), None);
    ///
    /// assert_eq!(Path::new("foo").relative_to("/"),  None);
    /// assert_eq!(Path::new("foo").relative_to(".."), None);
    ///
    /// assert_eq!(Path::new("..").relative_to("."), Some(PathBuf::from("..")));
    /// assert_eq!(Path::new(".").relative_to(".."), None);
    /// ```
    fn relative_to<P: AsRef<Path>>(&self, base: P) -> Option<PathBuf>;

    /// Returns the normalized equivalent of `self`, with intermediate symlinks resolved.
    ///
    /// The longest prefix of `self` where each component exist on the filesystem is canonicalized,
    /// the remaining path is lexically adjoined, and the result is normalized.
    ///
    /// If `self` is relative and no prefix component exists in the CWD (no prefix can be
    /// canonicalized), then the result is relative (it is simply the normalized equivalent of
    /// `self`). Use [`NormPathExt::absolute`] to ensure this method returns an absolute path.
    ///
    /// # Differences with [`Path::canonicalize`]
    ///
    /// - This method works for paths that do not exist on the filesystem.
    /// - The path is normalized with the same limitations as [`NormPathExt::normalized`]. In
    ///   particular, a suffix might contain `..` components that can replace canonicalized
    ///   components.
    /// - The returned path can be relative.
    ///
    /// # Differences with [`NormPathExt::normalized`]
    ///
    /// - This method does not perform pure lexical processing, and returns a [`std::io::Result`].
    /// - The prefix that is canonicalized has its intermediate symlinks resolved, without the
    ///   limitations of [`NormPathExt::normalized`].
    ///
    /// # Limitations
    ///
    /// The prefix considered for canonicalization ends at the first component of `self` that does
    /// not exist. The only exception is if the whole path exists, then it is canonicalized in
    /// full.
    ///
    /// For example, assuming only `usr` and `usr/lib` exist, `usr/liz/../lib/rust` refers to
    /// `usr/lib/rust`, but only `usr` is canonicalized since neither `usr/lib/rust` nor `usr/liz`
    /// exist.
    ///
    /// [`NormPathExt::normalized`] limitations apply in most cases. If you need to get the true
    /// canonical path, use [`Path::canonicalize`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::path::{Path, PathBuf};
    /// use npath::NormPathExt;
    ///
    /// # if cfg!(unix) {
    /// assert_eq!(Path::new("usr/lib").resolved().unwrap(),                 PathBuf::from("usr/lib"));
    /// assert_eq!(Path::new("usr//lib").resolved().unwrap(),                PathBuf::from("usr/lib"));
    /// assert_eq!(Path::new("usr/lib/.").resolved().unwrap(),               PathBuf::from("usr/lib"));
    /// assert_eq!(Path::new("usr/lib/gcc/..").resolved().unwrap(),          PathBuf::from("usr/lib"));
    /// assert_eq!(Path::new("/usr/lib").resolved().unwrap(),                PathBuf::from("/usr/lib"));
    /// assert_eq!(Path::new("/../usr/lib").resolved().unwrap(),             PathBuf::from("/usr/lib"));
    /// assert_eq!(Path::new("/usr/bin/../././/lib").resolved().unwrap(),    PathBuf::from("/usr/lib"));
    /// # }
    /// ```
    fn resolved(&self) -> Result<PathBuf>;

    /// Returns `path` restricted to `self`.
    ///
    /// This methods works as if `self` was the root directory. The returned path is guaranteed to
    /// be lexically inside `self`.
    ///
    /// # Differences with [`NormPathExt::try_rooted_join`]
    ///
    /// It does not return an error since the returned path is always inside `self`.
    ///
    /// # Limitations
    ///
    /// - Same limitations as [`NormPathExt::normalized`].
    /// - The result can have a different meaning than what was intended since all the prefix `..`
    ///   components are stripped away.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::path::{Path, PathBuf};
    /// use npath::NormPathExt;
    ///
    /// assert_eq!(Path::new("/srv").rooted_join("file.txt"),           PathBuf::from("/srv/file.txt"));
    /// assert_eq!(Path::new("/srv").rooted_join("/file.txt"),          PathBuf::from("/srv/file.txt"));
    /// assert_eq!(Path::new("/srv").rooted_join("../file.txt"),        PathBuf::from("/srv/file.txt"));
    /// assert_eq!(Path::new("/srv").rooted_join("foo/../file.txt"),    PathBuf::from("/srv/file.txt"));
    /// assert_eq!(Path::new("/srv").rooted_join("foo/../../file.txt"), PathBuf::from("/srv/file.txt"));
    /// assert_eq!(
    ///     Path::new("/srv").rooted_join("../srv/file.txt"),
    ///     PathBuf::from("/srv/srv/file.txt")
    /// );
    /// ```
    fn rooted_join<P: AsRef<Path>>(&self, path: P) -> PathBuf;

    /// Returns `path` restricted to `self`.
    ///
    /// `self` and `path` are converted to absolute paths with [`NormPathExt::absolute`], they are
    /// joined with [`NormPathExt::lexical_join`], and the result is normalized with
    /// [`NormPathExt::normalized`].
    ///
    /// # Differences with [`NormPathExt::rooted_join`]
    ///
    /// If the result points to a location outside of `base`, this method returns an error.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::path::{Path, PathBuf};
    /// use npath::NormPathExt;
    ///
    /// assert_eq!(Path::new("/srv").try_rooted_join("file.txt").unwrap(),        PathBuf::from("/srv/file.txt"));
    /// assert_eq!(Path::new("/srv").try_rooted_join("/file.txt").unwrap(),       PathBuf::from("/srv/file.txt"));
    /// assert_eq!(Path::new("/srv").try_rooted_join("foo/../file.txt").unwrap(), PathBuf::from("/srv/file.txt"));
    /// assert_eq!(
    ///     Path::new("/srv").try_rooted_join("../srv/file.txt").unwrap(),
    ///     PathBuf::from("/srv/file.txt")
    /// );
    ///
    /// assert!(Path::new("/srv").try_rooted_join("../file.txt").is_err());
    /// assert!(Path::new("/srv").try_rooted_join("foo/../../file.txt").is_err());
    /// ```
    fn try_rooted_join<P: AsRef<Path>>(&self, path: P) -> Result<PathBuf>;
}

impl NormPathExt for Path {
    fn absolute(&self) -> Result<PathBuf> {
        if !self.has_root() {
            Ok(env::current_dir()?.join(self))
        } else {
            Ok(self.to_path_buf())
        }
    }

    fn base(&self) -> &Path {
        if sys::ends_with_sep_dot(self) {
            return Path::new(Component::CurDir.as_os_str());
        }

        self.components()
            .next_back()
            .and_then(|c| match c {
                Component::Prefix(_) => None,
                _ => Some(Path::new(c.as_os_str())),
            })
            .unwrap_or_else(|| Path::new(Component::CurDir.as_os_str()))
    }

    fn dir(&self) -> &Path {
        if sys::ends_with_sep_dot(self) {
            // HACK: Trims the final "///.".
            return self.components().as_path();
        }

        let mut comps = self.components();
        comps
            .next_back()
            .and_then(|c| match c {
                Component::Prefix(_) | Component::RootDir => Some(self.components().as_path()),
                Component::Normal(_) | Component::CurDir | Component::ParentDir => {
                    let p = comps.as_path();
                    if !p.as_os_str().is_empty() {
                        Some(p)
                    } else {
                        None
                    }
                }
            })
            .unwrap_or_else(|| Path::new(Component::CurDir.as_os_str()))
    }

    // TODO: Windows tests.
    fn is_inside<P: AsRef<Path>>(&self, base: P) -> bool {
        let base = base.as_ref().normalized();
        let path = self.normalized();

        let mut base_components = base.components();
        let mut path_components = path.components();

        let mut base_head = base_components.next();
        let mut path_head = path_components.next();

        loop {
            match (base_head, path_head) {
                (Some(Component::CurDir), _) => base_head = base_components.next(),
                (_, Some(Component::CurDir)) => path_head = path_components.next(),
                (Some(x), Some(y)) if are_equal(&x, &y) => {
                    base_head = base_components.next();
                    path_head = path_components.next();
                }
                (Some(Component::ParentDir), Some(Component::Normal(_))) => {
                    while base_head == Some(Component::ParentDir) {
                        base_head = base_components.next();
                    }
                    return base_head == None;
                }
                (None, _) => return true,
                _ => return false,
            }
        }
    }

    fn normalized(&self) -> PathBuf {
        let mut stack: Vec<Component> = vec![];

        for component in self.components() {
            match component {
                Component::CurDir => {}
                Component::ParentDir if !stack.is_empty() => match stack.last().unwrap() {
                    Component::Prefix(_) | Component::ParentDir => stack.push(component),
                    Component::Normal(_) => {
                        stack.pop();
                    }
                    _ => {}
                },
                _ => {
                    stack.push(component);
                }
            }
        }

        // Turn an empty path into "."
        if stack.is_empty() {
            return Component::CurDir.as_os_str().into();
        }

        let mut path = PathBuf::new();

        for component in stack {
            path.push(component.as_os_str());
        }

        path
    }

    fn lexical_join<P: AsRef<Path>>(&self, path: P) -> PathBuf {
        lexical_join(self, path.as_ref())
    }

    fn relative_to<P: AsRef<Path>>(&self, base: P) -> Option<PathBuf> {
        let base = base.as_ref().normalized();
        let path = self.normalized();

        if base.has_root() != path.has_root() {
            return None;
        }

        let mut base_components = base.components();
        let mut path_components = path.components();

        let mut base_head = base_components.next();
        let mut path_head = path_components.next();

        loop {
            match (base_head, path_head) {
                (Some(a @ Component::Prefix(_)), Some(b @ Component::Prefix(_)))
                    if !are_equal(&a, &b) =>
                {
                    return None;
                }
                (Some(x), Some(y)) if are_equal(&x, &y) => {
                    base_head = base_components.next();
                    path_head = path_components.next();
                }
                (None, None) => return Some(PathBuf::from(Component::CurDir.as_os_str())),
                _ => {
                    let mut p = PathBuf::new();

                    if let Some(Component::ParentDir) = base_head {
                        return None;
                    }

                    if base_head.is_some() && base_head != Some(Component::CurDir) {
                        p.push(Component::ParentDir.as_os_str());
                    }

                    for _ in base_components {
                        p.push(Component::ParentDir.as_os_str());
                    }

                    if let Some(c) = path_head {
                        p.push(c);
                        p.extend(path_components);
                    }

                    return Some(p);
                }
            }
        }
    }

    // TODO: I'm thinking that it is equally valid to start from the end and canonicalize the
    // longest prefix that exist instead. That's not what C++ `weakly_canonical` does but it feels
    // more correct.
    // TODO: Some form of tests.
    fn resolved(&self) -> Result<PathBuf> {
        if self.exists() {
            return self.canonicalize();
        }

        let mut path = PathBuf::new();
        let mut components = self.components();
        let mut last = None;

        for c in &mut components {
            if !path.lexical_join(c).exists() {
                last = Some(c);
                break;
            }

            path.lexical_push(c);
        }

        if let Some(c) = last {
            path.lexical_push(c);
        }

        path.lexical_push(components.as_path());

        Ok(path.normalized())
    }

    fn rooted_join<P: AsRef<Path>>(&self, path: P) -> PathBuf {
        self.lexical_join(normalize_rooted(path.as_ref()))
    }

    // TODO: Not case insensitive on Windows.
    // <https://github.com/django/django/blob/master/django/utils/_os.py>
    fn try_rooted_join<P: AsRef<Path>>(&self, path: P) -> Result<PathBuf> {
        // Make absolute and normalize all paths
        let base = self.absolute()?.normalized();
        let path = self.lexical_join(path).absolute()?.normalized();

        // For `path` to be located inside `base`, either:
        // - It starts with `base` + "/"
        // - It is equal to `base`
        // - It is the root directory "/"
        if !path.starts_with(&base) && path != base && base.file_name().is_some() {
            return Err(Error::new(
                ErrorKind::Other,
                "Path outside of base directory",
            ));
        }

        Ok(path)
    }
}

// External crates are not supposed to know how paths are represented internally. For the sake of
// not using unsafe, the operations that need raw access to the characters have to use u8 for Unix,
// and u16 for Windows. If implemented inside libstd, all of them can just process WTF-8 bytes.
fn lexical_join(base: &Path, path: &Path) -> PathBuf {
    let prefix = get_prefix(base);
    let prefix_is_disk = matches!(prefix.map(|p| p.kind()), Some(Prefix::Disk(_)));
    let prefix_len = prefix.map(|p| p.as_os_str().len());

    let mut base = sys::to_os_encoding(base).into_owned();

    let path = sys::to_os_encoding(path);
    let mut path = &path[..];

    while !path.is_empty() && sys::is_separator(path[0]) {
        path = &path[1..];
    }

    if !path.is_empty() {
        if !(base.is_empty()
            || sys::is_separator(*base.last().unwrap())
            || (prefix_is_disk && prefix_len == Some(base.len())))
        {
            base.push(sys::MAIN_SEPARATOR);
        }

        base.extend(path);
    }

    PathBuf::from(sys::to_os_string(base))
}

// TODO: Handle prefixes containing / (limited by the prefix parsing code, avoid comparing OsStr of
// the full prefix).
fn are_equal(a: &Component, b: &Component) -> bool {
    if cfg!(windows) {
        a.as_os_str().eq_ignore_ascii_case(b.as_os_str())
    } else {
        a == b
    }
}

fn get_prefix(path: &Path) -> Option<PrefixComponent> {
    path.components().next().and_then(|c| {
        if let Component::Prefix(p) = c {
            Some(p)
        } else {
            None
        }
    })
}

// Eliminates all ".." components
fn normalize_rooted(path: &Path) -> PathBuf {
    let mut stack: Vec<&OsStr> = vec![];

    for component in path.components() {
        match component {
            Component::Normal(_) => stack.push(component.as_os_str()),
            Component::ParentDir => {
                if !stack.is_empty() {
                    stack.pop();
                }
            }
            _ => {}
        }
    }

    let mut path = PathBuf::new();

    for component in &stack {
        path.lexical_push(component);
    }

    path
}

#[cfg(unix)]
mod sys {
    use std::borrow::Cow;
    use std::ffi::OsString;
    use std::os::unix::prelude::*;
    use std::path::{is_separator as is_sep, Path, MAIN_SEPARATOR as MAIN_SEP};

    pub const MAIN_SEPARATOR: u8 = MAIN_SEP as u8;

    pub fn to_os_encoding(path: &Path) -> Cow<[u8]> {
        Cow::from(path.as_os_str().as_bytes())
    }

    pub fn to_os_string<V: Into<Vec<u8>>>(path: V) -> OsString {
        OsString::from_vec(path.into())
    }

    pub fn is_separator(b: u8) -> bool {
        is_sep(b as char)
    }

    pub fn ends_with_sep_dot(path: &Path) -> bool {
        let path = to_os_encoding(path);
        let len = path.len();
        len >= 2 && path[len - 1] == b'.' && is_separator(path[len - 2])
    }
}

#[cfg(windows)]
mod sys {
    use std::borrow::Cow;
    use std::convert::TryFrom;
    use std::ffi::OsString;
    use std::os::windows::prelude::*;
    use std::path::{is_separator as is_sep, Path, MAIN_SEPARATOR as MAIN_SEP};

    pub const MAIN_SEPARATOR: u16 = MAIN_SEP as u16;

    pub fn to_os_encoding(path: &Path) -> Cow<[u16]> {
        Cow::from(path.as_os_str().encode_wide().collect::<Vec<_>>())
    }

    pub fn to_os_string<V: AsRef<[u16]>>(path: V) -> OsString {
        OsString::from_wide(path.as_ref())
    }

    pub fn is_separator(w: u16) -> bool {
        char::try_from(w as u32).map(is_sep).unwrap_or(false)
    }

    pub fn ends_with_sep_dot(path: &Path) -> bool {
        let path = to_os_encoding(path);
        let len = path.len();
        len >= 2 && path[len - 1] == b'.' as u16 && is_separator(path[len - 2])
    }
}

#[cfg(test)]
mod tests {
    use super::NormPathExt;
    use std::path::{Path, PathBuf};

    macro_rules! assert_eq_ok {
        ($left:expr, $right:expr) => {
            assert!($left.is_ok());
            assert_eq!($left.unwrap(), $right);
        };
    }

    macro_rules! assert_eq_some {
        ($left:expr, $right:expr) => {
            assert!($left.is_some());
            assert_eq!($left.unwrap(), $right);
        };
    }

    #[test]
    #[cfg(unix)]
    fn test_absolute() {
        use std::env::current_dir;
        use std::ffi::OsString;

        let path = Path::new("/usr").absolute();
        assert!(path.is_ok());
        assert_eq!(path.unwrap().as_os_str(), "/usr");

        if let Ok(dir) = current_dir() {
            let path = Path::new("lib").absolute();
            assert!(path.is_ok());

            let path = path.unwrap();
            assert!(path.is_absolute());

            let mut result = OsString::from(dir);
            result.push("/lib");
            assert_eq!(path.as_os_str(), result);
        }
    }

    #[test]
    #[cfg(windows)]
    fn test_absolute() {
        use std::env::current_dir;
        use std::ffi::OsString;

        let path = Path::new(r"\Windows").absolute();
        assert!(path.is_ok());
        assert_eq!(path.unwrap().as_os_str(), r"\Windows");

        if let Ok(dir) = current_dir() {
            let path = Path::new("Windows").absolute();
            assert!(path.is_ok());

            let path = path.unwrap();
            assert!(path.is_absolute());

            let mut result = OsString::from(dir);
            result.push(r"\Windows");
            assert_eq!(path.as_os_str(), result);
        }
    }

    macro_rules! base {
        ($a:literal) => {
            Path::new($a).base().as_os_str()
        };
    }

    #[test]
    #[cfg(unix)]
    fn test_base() {
        assert_eq!(base!(""), ".");
        assert_eq!(base!("."), ".");
        assert_eq!(base!("/."), ".");
        assert_eq!(base!("/"), "/");
        assert_eq!(base!("////"), "/");
        assert_eq!(base!("x/"), "x");
        assert_eq!(base!("abc"), "abc");
        assert_eq!(base!("abc/def"), "def");
        assert_eq!(base!("a/b/.x"), ".x");
        assert_eq!(base!("a/b/c."), "c.");
        assert_eq!(base!("a/b/c.x"), "c.x");
    }

    #[test]
    #[cfg(windows)]
    fn test_base() {
        assert_eq!(base!(r"c:\"), r"\");
        assert_eq!(base!(r"c:."), ".");
        assert_eq!(base!(r"c:\a\b"), "b");
        assert_eq!(base!(r"c:a\b"), "b");
        assert_eq!(base!(r"c:a\b\c"), "c");
        assert_eq!(base!(r"\\host\share\"), r"\");
        assert_eq!(base!(r"\\host\share\a"), "a");
        assert_eq!(base!(r"\\host\share\a\b"), "b");
    }

    macro_rules! dir {
        ($a:literal) => {
            Path::new($a).dir().as_os_str()
        };
    }

    #[test]
    #[cfg(unix)]
    fn test_dir() {
        assert_eq!(dir!(""), ".");
        assert_eq!(dir!("."), ".");
        assert_eq!(dir!(".."), ".");
        assert_eq!(dir!("/."), "/");
        assert_eq!(dir!("/"), "/");
        assert_eq!(dir!("////"), "/");
        assert_eq!(dir!("/foo"), "/");
        assert_eq!(dir!("x/"), "."); // Go: "x"
        assert_eq!(dir!("x///"), "."); // Go: "x"
        assert_eq!(dir!("abc"), ".");
        assert_eq!(dir!("abc/def"), "abc");
        assert_eq!(dir!("a/b/.x"), "a/b");
        assert_eq!(dir!("a/b/c."), "a/b");
        assert_eq!(dir!("a/b/c.x"), "a/b");

        assert_eq!(dir!("x/."), "x");

        // Unnormalized
        assert_eq!(dir!("/../x"), "/..");
    }

    #[test]
    #[cfg(windows)]
    fn test_dir() {
        assert_eq!(dir!(r"c:\"), r"c:\");
        assert_eq!(dir!(r"c:."), r"c:.");
        assert_eq!(dir!(r"c:\a\b"), r"c:\a");
        assert_eq!(dir!(r"c:a\b"), r"c:a");
        assert_eq!(dir!(r"c:a\b\c"), r"c:a\b");
        assert_eq!(dir!(r"\\host\share"), r"\\host\share");
        assert_eq!(dir!(r"\\host\share\"), r"\\host\share\");
        assert_eq!(dir!(r"\\host\share\a"), r"\\host\share\");
        assert_eq!(dir!(r"\\host\share\a\b"), r"\\host\share\a");
    }

    #[cfg(unix)]
    macro_rules! is_inside {
        ($a:literal, $b:literal) => {
            Path::new($a).is_inside($b)
        };
    }

    #[test]
    #[cfg(unix)]
    fn test_is_inside() {
        assert!(is_inside!("/", "/"));
        assert!(is_inside!(".", "."));

        assert!(is_inside!("/srv", "/"));
        assert!(is_inside!("/srv", "//"));
        assert!(is_inside!("/srv/", "/"));
        assert!(is_inside!("/srv/.", "/"));
        assert!(is_inside!("/srv/..", "/"));
        assert!(is_inside!("/srv/../", "/"));

        assert!(is_inside!("/srv", "/srv"));
        assert!(is_inside!("/srv/", "/srv"));
        assert!(is_inside!("/srv/.", "/srv"));

        assert!(is_inside!("/srv", "/srv/"));
        assert!(is_inside!("/srv/", "/srv/"));
        assert!(is_inside!("/srv/.", "/srv/"));

        assert!(is_inside!("/srv", "/srv/."));
        assert!(is_inside!("/srv/", "/srv/."));
        assert!(is_inside!("/srv/.", "/srv/."));

        assert!(is_inside!("/srv/file.txt", "/srv"));

        assert!(is_inside!("srv", "srv"));
        assert!(is_inside!("srv", "."));

        assert!(!is_inside!("file.txt", "/srv"));
        assert!(!is_inside!("srv/file.txt", "/srv"));

        assert!(!is_inside!("/srv/..", "/srv"));

        assert!(is_inside!("foo", ".."));
        assert!(!is_inside!("foo", "../bar"));
        assert!(!is_inside!("/foo", ".."));
    }

    macro_rules! normalize {
        ($a:literal) => {
            Path::new($a).normalized().as_os_str()
        };
    }

    #[test]
    #[cfg(unix)]
    fn test_normalized() {
        // Already clean
        assert_eq!(normalize!("abc"), "abc");
        assert_eq!(normalize!("abc/def"), "abc/def");
        assert_eq!(normalize!("a/b/c"), "a/b/c");
        assert_eq!(normalize!("."), ".");
        assert_eq!(normalize!(".."), "..");
        assert_eq!(normalize!("../.."), "../..");
        assert_eq!(normalize!("../../abc"), "../../abc");
        assert_eq!(normalize!("/abc"), "/abc");
        assert_eq!(normalize!("/"), "/");

        // Empty is current dir
        assert_eq!(normalize!(""), ".");

        // Remove trailing slash
        assert_eq!(normalize!("abc/"), "abc");
        assert_eq!(normalize!("abc/def/"), "abc/def");
        assert_eq!(normalize!("a/b/c/"), "a/b/c");
        assert_eq!(normalize!("./"), ".");
        assert_eq!(normalize!("../"), "..");
        assert_eq!(normalize!("../../"), "../..");
        assert_eq!(normalize!("/abc/"), "/abc");

        // Remove doubled slash
        assert_eq!(normalize!("abc//def//ghi"), "abc/def/ghi");
        assert_eq!(normalize!("//abc"), "/abc");
        assert_eq!(normalize!("///abc"), "/abc");
        assert_eq!(normalize!("//abc//"), "/abc");
        assert_eq!(normalize!("abc//"), "abc");

        // Remove . elements
        assert_eq!(normalize!("abc/./def"), "abc/def");
        assert_eq!(normalize!("/./abc/def"), "/abc/def");
        assert_eq!(normalize!("abc/."), "abc");

        // Remove .. elements
        assert_eq!(normalize!("abc/def/ghi/../jkl"), "abc/def/jkl");
        assert_eq!(normalize!("abc/def/../ghi/../jkl"), "abc/jkl");
        assert_eq!(normalize!("abc/def/.."), "abc");
        assert_eq!(normalize!("abc/def/../.."), ".");
        assert_eq!(normalize!("/abc/def/../.."), "/");
        assert_eq!(normalize!("abc/def/../../.."), "..");
        assert_eq!(normalize!("/abc/def/../../.."), "/");
        assert_eq!(
            normalize!("abc/def/../../../ghi/jkl/../../../mno"),
            "../../mno"
        );
        assert_eq!(normalize!("/../abc"), "/abc");

        // Combinations
        assert_eq!(normalize!("abc/./../def"), "def");
        assert_eq!(normalize!("abc//./../def"), "def");
        assert_eq!(normalize!("abc/../../././../def"), "../../def");
    }

    #[test]
    #[cfg(windows)]
    fn test_normalized() {
        assert_eq!(normalize!(r"c:"), r"c:"); // Go: "c:."
        assert_eq!(normalize!(r"c:\"), r"c:\");
        assert_eq!(normalize!(r"c:\abc"), r"c:\abc");
        assert_eq!(normalize!(r"c:abc\..\..\.\.\..\def"), r"c:..\..\def");
        assert_eq!(normalize!(r"c:\abc\def\..\.."), r"c:\");
        assert_eq!(normalize!(r"c:\..\abc"), r"c:\abc");
        assert_eq!(normalize!(r"c:..\abc"), r"c:..\abc");
        assert_eq!(normalize!(r"\"), r"\");
        assert_eq!(normalize!(r"/"), r"\");
        assert_eq!(normalize!(r"\\i\..\c$"), r"\\i\..\c$"); // Go: "\c$" (bogus)
        assert_eq!(normalize!(r"\\i\..\i\c$"), r"\\i\..\i\c$"); // Go: "\i\c$" (bogus)
        assert_eq!(normalize!(r"\\i\..\I\c$"), r"\\i\..\I\c$"); // Go: "\I\c$" (bogus)
        assert_eq!(normalize!(r"\\host\share\foo\..\bar"), r"\\host\share\bar");
        assert_eq!(normalize!(r"//host/share/foo/../baz"), r"\host\share\baz"); // GetFullPathName: "\\host\share\baz"
        assert_eq!(normalize!(r"\\a\b\..\c"), r"\\a\b\c");
        assert_eq!(normalize!(r"\\a\b"), r"\\a\b\"); // Go: "\\a\b"
        assert_eq!(normalize!(r"\\a\..\"), r"\\a\..\");

        // Issue with std::sys::path::parse_prefix (ignores UNC with empty server and share)
        assert_eq!(normalize!(r"\\\a\..\"), r"\"); // GetFullPathName: "\\\a\" (UNC prefix)
        assert_eq!(normalize!(r"\\\\a\.."), r"\"); // GetFullPathName: "\\\" (UNC prefix)

        // Issue with std::sys::path::parse_prefix (only considers "\\")
        assert_eq!(normalize!(r"//a\..\"), r"\");
    }

    macro_rules! lexical_join {
        ($l:literal) => {
            Path::new($l).as_os_str()
        };
        ($l:literal, $($a:literal),*) => {
            {
                let mut p = PathBuf::from($l);

                $(
                    p = p.lexical_join($a);
                )*

                p
            }.as_os_str()
        };
    }

    #[test]
    #[cfg(unix)]
    fn test_lexical_join() {
        assert_eq!(lexical_join!("a", "b"), "a/b");
        assert_eq!(lexical_join!("a", ""), "a");
        assert_eq!(lexical_join!("", "b"), "b");
        assert_eq!(lexical_join!("/", "a"), "/a");
        assert_eq!(lexical_join!("/", "a/b"), "/a/b");
        assert_eq!(lexical_join!("/", ""), "/");
        assert_eq!(lexical_join!("//", "a"), "//a"); // Go: "/a"
        assert_eq!(lexical_join!("/a", "b"), "/a/b");
        assert_eq!(lexical_join!("a/", "b"), "a/b");
        assert_eq!(lexical_join!("a/", ""), "a/"); // Go: "a"
        assert_eq!(lexical_join!("", ""), "");
        assert_eq!(lexical_join!("/", "a", "b"), "/a/b");

        // Dot
        assert_eq!(lexical_join!("a", "."), "a/.");
        assert_eq!(lexical_join!("a", ".."), "a/..");
        assert_eq!(lexical_join!("a", "./b"), "a/./b");
        assert_eq!(lexical_join!("a", "../b"), "a/../b");
        assert_eq!(lexical_join!("a", "b/."), "a/b/.");
        assert_eq!(lexical_join!("a", "b/.."), "a/b/..");
        assert_eq!(lexical_join!("a", "b/./c"), "a/b/./c");
        assert_eq!(lexical_join!("a", "b/../c"), "a/b/../c");

        // Redo the tests with a "/" before each component
        assert_eq!(lexical_join!("a", "/b"), "a/b");
        assert_eq!(lexical_join!("a", "/"), "a");
        assert_eq!(lexical_join!("", "/b"), "b");
        assert_eq!(lexical_join!("/", "/a"), "/a");
        assert_eq!(lexical_join!("/", "/a/b"), "/a/b");
        assert_eq!(lexical_join!("/", "/"), "/");
        assert_eq!(lexical_join!("//", "/a"), "//a"); // Go: "/a"
        assert_eq!(lexical_join!("/a", "/b"), "/a/b");
        assert_eq!(lexical_join!("a/", "/b"), "a/b");
        assert_eq!(lexical_join!("a/", "/"), "a/"); // Go: "a"
        assert_eq!(lexical_join!("", "/"), "");
        assert_eq!(lexical_join!("/", "/a", "/b"), "/a/b");

        // Dot
        assert_eq!(lexical_join!("a", "/."), "a/.");
        assert_eq!(lexical_join!("a", "/.."), "a/..");
        assert_eq!(lexical_join!("a", "/./b"), "a/./b");
        assert_eq!(lexical_join!("a", "/../b"), "a/../b");
        assert_eq!(lexical_join!("a", "/b/."), "a/b/.");
        assert_eq!(lexical_join!("a", "/b/.."), "a/b/..");
        assert_eq!(lexical_join!("a", "/b/./c"), "a/b/./c");
        assert_eq!(lexical_join!("a", "/b/../c"), "a/b/../c");
    }

    #[test]
    #[cfg(windows)]
    fn test_lexical_join() {
        assert_eq!(lexical_join!("directory", "file"), r"directory\file");
        assert_eq!(
            lexical_join!(r"C:\Windows\", "System32"),
            r"C:\Windows\System32"
        );
        assert_eq!(lexical_join!(r"C:\Windows\", ""), r"C:\Windows\"); // Go: "C:\Windows"
        assert_eq!(lexical_join!(r"C:\", "Windows"), r"C:\Windows");
        assert_eq!(lexical_join!(r"C:", "a"), "C:a");
        assert_eq!(lexical_join!(r"C:", r"a\b"), r"C:a\b");
        assert_eq!(lexical_join!(r"C:", "a", "b"), r"C:a\b");
        assert_eq!(lexical_join!(r"C:", "", "b"), "C:b");
        assert_eq!(lexical_join!(r"C:", "", "", "b"), "C:b");
        assert_eq!(lexical_join!(r"C:", ""), "C:"); // Go: "C:."
        assert_eq!(lexical_join!(r"C:", "", ""), "C:"); // Go: "C:."
        assert_eq!(lexical_join!(r"C:.", "a"), r"C:.\a"); // Go: "C:a"
        assert_eq!(lexical_join!(r"C:a", "b"), r"C:a\b");
        assert_eq!(lexical_join!(r"C:a", "b", "d"), r"C:a\b\d");
        assert_eq!(lexical_join!(r"\\host\share", "foo"), r"\\host\share\foo");
        assert_eq!(lexical_join!(r"\\host\share\foo"), r"\\host\share\foo");
        assert_eq!(
            lexical_join!(r"//host/share", "foo/bar"),
            r"//host/share\foo/bar"
        ); // Go: "\\host\share\foo\bar"
        assert_eq!(lexical_join!(r"\"), r"\");
        assert_eq!(lexical_join!(r"\", ""), r"\");
        assert_eq!(lexical_join!(r"\", "a"), r"\a");
        assert_eq!(lexical_join!(r"\\", "a"), r"\\a"); // Go: "\a"
        assert_eq!(lexical_join!(r"\", "a", "b"), r"\a\b");
        assert_eq!(lexical_join!(r"\\", "a", "b"), r"\\a\b"); // Go: "\a\b"
        assert_eq!(lexical_join!(r"\", r"\\a\b", "c"), r"\a\b\c");
        assert_eq!(lexical_join!(r"\\a", "b", "c"), r"\\a\b\c"); // Go: "\a\b\c"
        assert_eq!(lexical_join!(r"\\a\", "b", "c"), r"\\a\b\c"); // Go: "\a\b\c"

        // Redo the tests with a "\" before each component
        assert_eq!(lexical_join!("directory", r"\file"), r"directory\file");
        assert_eq!(
            lexical_join!(r"C:\Windows\", r"\System32"),
            r"C:\Windows\System32"
        );
        assert_eq!(lexical_join!(r"C:\Windows\", r"\"), r"C:\Windows\"); // Go: "C:\Windows"
        assert_eq!(lexical_join!(r"C:\", r"\Windows"), r"C:\Windows");
        assert_eq!(lexical_join!(r"C:", r"\a"), "C:a");
        assert_eq!(lexical_join!(r"C:", r"\a\b"), r"C:a\b");
        assert_eq!(lexical_join!(r"C:", r"\a", r"\b"), r"C:a\b");
        assert_eq!(lexical_join!(r"C:", r"\", r"\b"), "C:b");
        assert_eq!(lexical_join!(r"C:", r"\", r"\", r"\b"), "C:b");
        assert_eq!(lexical_join!(r"C:", r"\"), "C:"); // Go: "C:."
        assert_eq!(lexical_join!(r"C:", r"\", r"\"), "C:"); // Go: "C:."
        assert_eq!(lexical_join!(r"C:.", r"\a"), r"C:.\a"); // Go: "C:a"
        assert_eq!(lexical_join!(r"C:a", r"\b"), r"C:a\b");
        assert_eq!(lexical_join!(r"C:a", r"\b", r"\d"), r"C:a\b\d");
        assert_eq!(lexical_join!(r"\\host\share", r"\foo"), r"\\host\share\foo");
        assert_eq!(lexical_join!(r"\\host\share\foo"), r"\\host\share\foo");
        assert_eq!(
            lexical_join!(r"//host/share", r"\foo/bar"),
            r"//host/share\foo/bar"
        ); // Go: "\\host\share\foo\bar"
        assert_eq!(lexical_join!(r"\"), r"\");
        assert_eq!(lexical_join!(r"\", r"\"), r"\");
        assert_eq!(lexical_join!(r"\", r"\a"), r"\a");
        assert_eq!(lexical_join!(r"\\", r"\a"), r"\\a"); // Go: "\a"
        assert_eq!(lexical_join!(r"\", r"\a", r"\b"), r"\a\b");
        assert_eq!(lexical_join!(r"\\", r"\a", r"\b"), r"\\a\b"); // Go: "\a\b"
        assert_eq!(lexical_join!(r"\", r"\\\a\b", r"\c"), r"\a\b\c");
        assert_eq!(lexical_join!(r"\\a", r"\b", r"\c"), r"\\a\b\c"); // Go: "\a\b\c"
        assert_eq!(lexical_join!(r"\\a\", r"\b", r"\c"), r"\\a\b\c"); // Go: "\a\b\c"
    }

    macro_rules! relative {
        ($a:literal, $b:literal) => {
            Path::new($b).relative_to($a).map(|p| p.into_os_string())
        };
    }

    #[test]
    #[cfg(unix)]
    fn test_relative_to() {
        assert_eq_some!(relative!("a/b", "a/b"), ".");
        assert_eq_some!(relative!("a/b/.", "a/b"), ".");
        assert_eq_some!(relative!("a/b", "a/b/."), ".");
        assert_eq_some!(relative!("./a/b", "a/b"), ".");
        assert_eq_some!(relative!("a/b", "./a/b"), ".");
        assert_eq_some!(relative!("ab/cd", "ab/cde"), "../cde");
        assert_eq_some!(relative!("ab/cd", "ab/c"), "../c");
        assert_eq_some!(relative!("a/b", "a/b/c/d"), "c/d");
        assert_eq_some!(relative!("a/b", "a/b/../c"), "../c");
        assert_eq_some!(relative!("a/b/../c", "a/b"), "../b");
        assert_eq_some!(relative!("a/b/c", "a/c/d"), "../../c/d");
        assert_eq_some!(relative!("a/b", "c/d"), "../../c/d");
        assert_eq_some!(relative!("a/b/c/d", "a/b"), "../..");
        assert_eq_some!(relative!("a/b/c/d", "a/b/"), "../..");
        assert_eq_some!(relative!("a/b/c/d/", "a/b"), "../..");
        assert_eq_some!(relative!("a/b/c/d/", "a/b/"), "../..");
        assert_eq_some!(relative!("../../a/b", "../../a/b/c/d"), "c/d");
        assert_eq_some!(relative!("/a/b", "/a/b"), ".");
        assert_eq_some!(relative!("/a/b/.", "/a/b"), ".");
        assert_eq_some!(relative!("/a/b", "/a/b/."), ".");
        assert_eq_some!(relative!("/ab/cd", "/ab/cde"), "../cde");
        assert_eq_some!(relative!("/ab/cd", "/ab/c"), "../c");
        assert_eq_some!(relative!("/a/b", "/a/b/c/d"), "c/d");
        assert_eq_some!(relative!("/a/b", "/a/b/../c"), "../c");
        assert_eq_some!(relative!("/a/b/../c", "/a/b"), "../b");
        assert_eq_some!(relative!("/a/b/c", "/a/c/d"), "../../c/d");
        assert_eq_some!(relative!("/a/b", "/c/d"), "../../c/d");
        assert_eq_some!(relative!("/a/b/c/d", "/a/b"), "../..");
        assert_eq_some!(relative!("/a/b/c/d", "/a/b/"), "../..");
        assert_eq_some!(relative!("/a/b/c/d/", "/a/b"), "../..");
        assert_eq_some!(relative!("/a/b/c/d/", "/a/b/"), "../..");
        assert_eq_some!(relative!("/../../a/b", "/../../a/b/c/d"), "c/d");
        assert_eq_some!(relative!(".", "a/b"), "a/b");
        assert_eq_some!(relative!(".", ".."), "..");

        // Can't do purely lexically
        assert!(relative!("..", ".").is_none());
        assert!(relative!("..", "a").is_none());
        assert!(relative!("../..", "..").is_none());
        assert!(relative!("a", "/a").is_none());
        assert!(relative!("/a", "a").is_none());
    }

    #[test]
    #[cfg(windows)]
    fn test_relative_to() {
        assert_eq_some!(relative!(r"C:a\b\c", r"C:a/b/d"), r"..\d");
        assert_eq_some!(relative!(r"C:\Projects", r"c:\projects\src"), r"src");
        assert_eq_some!(relative!(r"C:\Projects", r"c:\projects"), r".");
        assert_eq_some!(relative!(r"C:\Projects\a\..", r"c:\projects"), r".");

        // Can't do purely lexically
        assert!(relative!("..", ".").is_none());
        assert!(relative!("..", "a").is_none());
        assert!(relative!(r"..\..", "..").is_none());
        assert!(relative!("a", r"\a").is_none());
        assert!(relative!(r"\a", "a").is_none());

        // There is no relative path
        assert!(relative!(r"C:\", r"D:\").is_none());
        assert!(relative!(r"C:", r"D:").is_none());
    }

    macro_rules! rooted_join {
        ($a:literal, $($b:literal),*) => {
            {
                let mut path = PathBuf::from($a);

                $(
                    path = path.rooted_join($b);
                )*

                path
            }.as_os_str()
        };
    }

    #[test]
    #[cfg(unix)]
    fn test_rooted_join() {
        assert_eq!(rooted_join!("/usr", "lib"), "/usr/lib");
        assert_eq!(rooted_join!("/usr", "/lib"), "/usr/lib");
        assert_eq!(rooted_join!("/usr", "lib/.."), "/usr");
        assert_eq!(rooted_join!("/", ".."), "/");

        assert_eq!(rooted_join!("/usr", "../etc/passwd"), "/usr/etc/passwd");
        assert_eq!(rooted_join!("/usr", "/../etc/passwd"), "/usr/etc/passwd");
        assert_eq!(
            rooted_join!("/usr", "lib/../../etc/passwd"),
            "/usr/etc/passwd"
        );
        assert_eq!(rooted_join!("/usr", "../usr-"), "/usr/usr-");
    }

    #[test]
    #[cfg(windows)]
    fn test_rooted_join() {
        assert_eq!(
            rooted_join!(r"C:\Windows", "System32"),
            r"C:\Windows\System32"
        );
        assert_eq!(
            rooted_join!(r"C:\Windows", "System32"),
            r"C:\Windows\System32"
        );
        assert_eq!(rooted_join!(r"C:\Windows", "System32/.."), r"C:\Windows");
        assert_eq!(rooted_join!(r"C:\", ".."), r"C:\");

        assert_eq!(
            rooted_join!(r"C:\Windows", r"..\System32"),
            r"C:\Windows\System32"
        );
        assert_eq!(
            rooted_join!(r"C:\Windows", r"\..\System32"),
            r"C:\Windows\System32"
        );
        assert_eq!(
            rooted_join!(r"C:\Windows", r"System\..\..\System32"),
            r"C:\Windows\System32"
        );
        assert_eq!(
            rooted_join!(r"C:\Windows", r"..\Windows-"),
            r"C:\Windows\Windows-"
        );
    }

    macro_rules! try_rooted_join {
        ($a:literal, $($b:literal),*) => {
            {
                let mut res = Ok(PathBuf::from($a));

                $(
                    res = res.and_then(|p| p.try_rooted_join($b));
                )*

                res
            }.map(|p| p.into_os_string())
        };
    }

    #[test]
    #[cfg(unix)]
    fn test_try_rooted_join() {
        assert_eq_ok!(try_rooted_join!("/usr", "lib"), "/usr/lib");
        assert_eq_ok!(try_rooted_join!("/usr", "/lib"), "/usr/lib");
        assert_eq_ok!(try_rooted_join!("/usr", "lib/.."), "/usr");
        assert_eq_ok!(try_rooted_join!("/", ".."), "/");

        assert!(try_rooted_join!("/usr", "../etc/passwd").is_err()); // /etc/passwd
        assert!(try_rooted_join!("/usr", "/../etc/passwd").is_err()); // /etc/passwd
        assert!(try_rooted_join!("/usr", "lib/../../etc/passwd").is_err()); // /etc/passwd
        assert!(try_rooted_join!("/usr", "../usr-").is_err()); // /usr-
    }

    #[test]
    #[cfg(windows)]
    fn test_try_rooted_join() {
        assert_eq_ok!(
            try_rooted_join!(r"C:\Windows", "System32"),
            r"C:\Windows\System32"
        );
        assert_eq_ok!(
            try_rooted_join!(r"C:\Windows", "System32"),
            r"C:\Windows\System32"
        );
        assert_eq_ok!(
            try_rooted_join!(r"C:\Windows", "System32/.."),
            r"C:\Windows"
        );
        assert_eq_ok!(try_rooted_join!(r"C:\", ".."), r"C:\");

        assert!(try_rooted_join!(r"C:\Windows", r"..\System32", r"C:\Windows\System32").is_err());
        assert!(try_rooted_join!(r"C:\Windows", r"\..\System32", r"C:\Windows\System32").is_err());
        assert!(try_rooted_join!(
            r"C:\Windows",
            r"System\..\..\System32",
            r"C:\Windows\System32"
        )
        .is_err());
        assert!(try_rooted_join!(r"C:\Windows", r"..\Windows-", r"C:\Windows\Windows-").is_err());
    }
}
