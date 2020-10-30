//! Normalized Unix Paths
//!
//! - Pure lexical processing path normalization.
//! - Concatenation of absolute paths.
//! - POSIX [`dirname(3)`] and [`basename(3)`] equivalents.
//!
//! # [`Path`]
//!
//! | std                    | npath                          |
//! |------------------------|--------------------------------|
//! | [`Path::file_name`]    | [`NormPathExt::base`]          |
//! | [`Path::parent`]       | [`NormPathExt::dir`]           |
//! | [`Path::canonicalize`] | [`NormPathExt::normalize`]     |
//! | [`Path::join`]         | [`NormPathExt::relative_join`] |
//!
//! # [`PathBuf`]
//!
//! | std                  | npath                             |
//! |----------------------|-----------------------------------|
//! | [`PathBuf::push`]    | [`NormPathBufExt::relative_push`] |
//!
//! [`dirname(3)`]: http://man7.org/linux/man-pages/man3/dirname.3.html
//! [`basename(3)`]: http://man7.org/linux/man-pages/man3/basename.3.html

use std::ffi::OsString;
use std::os::unix::prelude::*;
use std::path::{Component, Path, PathBuf};

const SEP: u8 = b'/';
const DOT: u8 = b'.';

/// Extension trait for [`PathBuf`].
pub trait NormPathBufExt {
    /// Appends `path` to `self`.
    ///
    /// # Differences with [`PathBuf::push`]
    ///
    /// If `path` is absolute, it does not replace the current path.
    ///
    /// # Example
    ///
    /// ```
    /// use std::path::PathBuf;
    /// use npath::NormPathBufExt;
    ///
    /// let mut path = PathBuf::from("/usr");
    ///
    /// path.relative_push("bin");  // relative
    /// path.relative_push("/cat"); // absolute
    ///
    /// assert_eq!(path, PathBuf::from("/usr/bin/cat"));
    /// ```
    fn relative_push<P: AsRef<Path>>(&mut self, path: P);
}

impl NormPathBufExt for PathBuf {
    fn relative_push<P: AsRef<Path>>(&mut self, path: P) {
        let base = unsafe { &mut *(self as *mut PathBuf as *mut Vec<u8>) };
        let path = path.as_ref();

        if path.as_os_str().is_empty() || path == Path::new("/") {
            return;
        }

        if !base.is_empty() && *base.last().unwrap() != SEP && !path.is_absolute() {
            base.push(SEP);
        }

        base.extend(path.as_os_str().as_bytes());
    }
}

/// Extension trait for [`Path`].
pub trait NormPathExt {
    /// Returns the last path component.
    ///
    /// See [`basename(3)`](http://man7.org/linux/man-pages/man3/basename.3.html).
    ///
    /// # Differences with [`Path::file_name`]
    ///
    /// - Always returns a path (`/`, `.`, or `..`, whereas [`Path::file_name`] returns `None`).
    /// - Returns a [`PathBuf`] instead of an [`OsStr`](std::ffi::OsStr).
    ///
    /// # Example
    ///
    /// ```
    /// use std::path::{Path, PathBuf};
    /// use npath::NormPathExt;
    ///
    /// assert_eq!(Path::new("/usr/lib").base(), PathBuf::from("lib"));
    /// assert_eq!(Path::new("/usr/").base(),    PathBuf::from("usr"));
    /// assert_eq!(Path::new("usr").base(),      PathBuf::from("usr"));
    /// assert_eq!(Path::new("/").base(),        PathBuf::from("/"));
    /// assert_eq!(Path::new(".").base(),        PathBuf::from("."));
    /// assert_eq!(Path::new("..").base(),       PathBuf::from(".."));
    /// ```
    fn base(&self) -> PathBuf;

    /// Returns the path up to, but not including, the final component.
    ///
    /// See [`dirname(3)`](http://man7.org/linux/man-pages/man3/dirname.3.html).
    ///
    /// # Differences with [`Path::parent`]
    ///
    /// - Always returns a path (`/` when [`Path::parent`] returns `None`).
    ///
    /// # Example
    ///
    /// ```
    /// use std::path::{Path, PathBuf};
    /// use npath::NormPathExt;
    ///
    /// assert_eq!(Path::new("/usr/lib").dir(), PathBuf::from("/usr"));
    /// assert_eq!(Path::new("/usr/").dir(),    PathBuf::from("/"));
    /// assert_eq!(Path::new("usr").dir(),      PathBuf::from("."));
    /// assert_eq!(Path::new("/").dir(),        PathBuf::from("/"));
    /// assert_eq!(Path::new(".").dir(),        PathBuf::from("."));
    /// assert_eq!(Path::new("..").dir(),       PathBuf::from("."));
    /// ```
    fn dir(&self) -> PathBuf;

    /// Returns the normalized equivalent of `self`.
    ///
    /// The returned path is the shortest equivalent path, normalized by pure lexical processing
    /// with the following rules:
    ///
    /// 1. Replace repeated `/` with a single one.
    /// 2. Eliminate `.` path components (the current directory).
    /// 3. Consume inner `..` path components (the parent directory), including components preceded
    ///    by a rooted path (replace `/..` by `/`).
    ///
    /// # Differences with [`std::fs::canonicalize`]
    ///
    /// This function **does not touch the filesystem, ever**:
    ///
    /// - It does not resolve symlinks.
    /// - It does not check if files/directories exists.
    /// - If the given path is relative, it returns a relative path.
    ///
    /// If `/a/b` is a symlink to `/d/e`, for `/a/b/../c`:
    ///
    /// - [`std::fs::canonicalize`] returns `/d/c`.
    /// - [`normalize`] returns `/a/c`.
    ///
    /// # Example
    ///
    /// ```
    /// use std::path::{Path, PathBuf};
    /// use npath::NormPathExt;
    ///
    /// assert_eq!(Path::new("usr/lib").normalize(),                 PathBuf::from("usr/lib"));
    /// assert_eq!(Path::new("usr//lib").normalize(),                PathBuf::from("usr/lib"));
    /// assert_eq!(Path::new("usr/lib/.").normalize(),               PathBuf::from("usr/lib"));
    /// assert_eq!(Path::new("usr/lib/gcc/..").normalize(),          PathBuf::from("usr/lib"));
    /// assert_eq!(Path::new("/../usr/lib").normalize(),             PathBuf::from("/usr/lib"));
    /// assert_eq!(Path::new("/../usr/bin/../././/lib").normalize(), PathBuf::from("/usr/lib"));
    /// ```
    fn normalize(&self) -> PathBuf;

    /// Returns `path` appended to `self`.
    ///
    /// See [`NormPathBufExt::relative_push`].
    fn relative_join<P: AsRef<Path>>(&self, path: P) -> PathBuf;
}

impl NormPathExt for Path {
    fn base(&self) -> PathBuf {
        PathBuf::from(OsString::from_vec(base_name_from_vec(
            self.as_os_str().as_bytes(),
        )))
    }

    fn dir(&self) -> PathBuf {
        PathBuf::from(OsString::from_vec(dir_name_from_vec(
            self.as_os_str().as_bytes(),
        )))
    }

    fn normalize(&self) -> PathBuf {
        let mut stack: Vec<Component> = vec![];

        for component in self.components() {
            match component {
                Component::CurDir => {}
                Component::ParentDir if !stack.is_empty() => match stack.last().unwrap() {
                    Component::ParentDir => stack.push(component),
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

    fn relative_join<P: AsRef<Path>>(&self, path: P) -> PathBuf {
        let mut b = self.to_path_buf();
        b.relative_push(path);
        b
    }
}

// See:
// - <https://golang.org/pkg/path/filepath/#Base>
// - <https://git.musl-libc.org/cgit/musl/tree/src/misc/basename.c>
fn base_name_from_vec(path: &[u8]) -> Vec<u8> {
    if path.is_empty() {
        return vec![DOT];
    }

    let mut j = path.len();

    // Strip trailing separators
    while j > 0 && path[j - 1] == SEP {
        j -= 1;
    }

    let mut i = j;

    // Include trailing characters after the last separator
    while i > 0 && path[i - 1] != SEP {
        i -= 1;
    }

    let base = &path[i..j];

    // The path has only separators
    if base.is_empty() {
        return vec![SEP];
    }

    base.to_vec()
}

// See:
// - <https://golang.org/pkg/path/filepath/#Dir>
// - <https://git.musl-libc.org/cgit/musl/tree/src/misc/dirname.c>
fn dir_name_from_vec(path: &[u8]) -> Vec<u8> {
    let mut i = path.len();

    // Strip trailing separators ("foo//bar//" -> "foo//bar")
    while i > 0 && path[i - 1] == SEP {
        i -= 1;
    }

    // Strip trailing component ("foo//bar" -> "foo//")
    while i > 0 && path[i - 1] != SEP {
        i -= 1;
    }

    // Strip trailing separators again ("foo//" -> "foo")
    while i > 0 && path[i - 1] == SEP {
        i -= 1;
    }

    // dirname of "///foo//" is "/"
    if i == 0 && path.first() == Some(&SEP) {
        return vec![SEP];
    }

    let dir = &path[..i];

    // dirname of "foo//" is "."
    if dir.is_empty() {
        return vec![DOT];
    }

    dir.to_vec()
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::NormPathExt;

    #[test]
    fn base_name_test() {
        let cases = vec![
            ("", "."),
            (".", "."),
            ("/.", "."),
            ("/", "/"),
            ("////", "/"),
            ("x/", "x"),
            ("abc", "abc"),
            ("abc/def", "def"),
            ("a/b/.x", ".x"),
            ("a/b/c.", "c."),
            ("a/b/c.x", "c.x"),
        ];

        for c in cases {
            assert_eq!(Path::new(c.0).base().as_os_str(), c.1);
        }
    }

    #[test]
    fn dir_name_test() {
        let cases = vec![
            ("", "."),
            (".", "."),
            ("..", "."),
            ("/.", "/"),
            ("/", "/"),
            ("////", "/"),
            ("/foo", "/"),
            ("x/", "."),   // Go's `filepath.Dir` returns "x"
            ("x///", "."), // Go's `filepath.Dir` returns "x"
            ("abc", "."),
            ("abc/def", "abc"),
            ("a/b/.x", "a/b"),
            ("a/b/c.", "a/b"),
            ("a/b/c.x", "a/b"),
            // Unnormalized
            ("/../x", "/.."),
        ];

        for c in cases {
            assert_eq!(Path::new(c.0).dir().as_os_str(), c.1);
        }
    }

    #[test]
    fn normalize_test() {
        let cases = vec![
            // Already clean
            ("abc", "abc"),
            ("abc/def", "abc/def"),
            ("a/b/c", "a/b/c"),
            (".", "."),
            ("..", ".."),
            ("../..", "../.."),
            ("../../abc", "../../abc"),
            ("/abc", "/abc"),
            ("/", "/"),
            // Empty is current dir
            ("", "."),
            // Remove trailing slash
            ("abc/", "abc"),
            ("abc/def/", "abc/def"),
            ("a/b/c/", "a/b/c"),
            ("./", "."),
            ("../", ".."),
            ("../../", "../.."),
            ("/abc/", "/abc"),
            // Remove doubled slash
            ("abc//def//ghi", "abc/def/ghi"),
            ("//abc", "/abc"),
            ("///abc", "/abc"),
            ("//abc//", "/abc"),
            ("abc//", "abc"),
            // Remove . elements
            ("abc/./def", "abc/def"),
            ("/./abc/def", "/abc/def"),
            ("abc/.", "abc"),
            // Remove .. elements
            ("abc/def/ghi/../jkl", "abc/def/jkl"),
            ("abc/def/../ghi/../jkl", "abc/jkl"),
            ("abc/def/..", "abc"),
            ("abc/def/../..", "."),
            ("/abc/def/../..", "/"),
            ("abc/def/../../..", ".."),
            ("/abc/def/../../..", "/"),
            ("abc/def/../../../ghi/jkl/../../../mno", "../../mno"),
            ("/../abc", "/abc"),
            // Combinations
            ("abc/./../def", "def"),
            ("abc//./../def", "def"),
            ("abc/../../././../def", "../../def"),
        ];

        for c in cases {
            assert_eq!(Path::new(c.0).normalize().as_os_str(), c.1);
        }
    }

    #[test]
    fn relative_join_test() {
        let cases = vec![
            (("a", "b"), "a/b"),
            (("a", ""), "a"),
            (("", "b"), "b"),
            (("/", "a"), "/a"),
            (("/", "a/b"), "/a/b"),
            (("/", ""), "/"),
            (("//", "a"), "//a"),
            (("/a", "b"), "/a/b"),
            (("a/", "b"), "a/b"),
            (("a/", ""), "a/"),
            (("", ""), ""),
        ];

        for c in cases {
            assert_eq!(Path::new((c.0).0).relative_join((c.0).1).as_os_str(), c.1);
        }
    }
}
