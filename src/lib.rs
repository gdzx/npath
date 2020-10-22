//! Normalized Unix Paths
//!
//! - Pure lexical processing path normalization.
//! - Concatenation of absolute paths.
//! - POSIX [`dirname(3)`] and [`basename(3)`] equivalents.
//!
//! # Functions
//!
//! | std                       | npath         |
//! |---------------------------|---------------|
//! | -                         | [`base_name`] |
//! | -                         | [`dir_name`]  |
//! | [`std::fs::canonicalize`] | [`normalize`] |
//!
//! # [`Path`]
//!
//! | std                    | npath                      |
//! |------------------------|----------------------------|
//! | [`Path::file_name`]    | [`NormPathExt::base_name`] |
//! | [`Path::join`]         | [`NormPathExt::concat`]    |
//! | [`Path::parent`]       | [`NormPathExt::dir_name`]  |
//! | [`Path::canonicalize`] | [`NormPathExt::normalize`] |
//!
//! # [`PathBuf`]
//!
//! | std                  | npath                      |
//! |----------------------|----------------------------|
//! | [`PathBuf::push`]    | [`NormPathBufExt::append`] |
//!
//! [`dirname(3)`]: http://man7.org/linux/man-pages/man3/dirname.3.html
//! [`basename(3)`]: http://man7.org/linux/man-pages/man3/basename.3.html

use std::ffi::OsString;
use std::os::unix::prelude::*;
use std::path::{Path, PathBuf};

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
    /// use std::path::{Path, PathBuf};
    /// use npath::NormPathBufExt;
    ///
    /// let mut path = PathBuf::from("/usr");
    ///
    /// path.append("bin");  // relative
    /// path.append("/cat"); // absolute
    ///
    /// assert_eq!(path, Path::new("/usr/bin/cat"));
    /// ```
    fn append<P: AsRef<Path>>(&mut self, path: P);
}

impl NormPathBufExt for PathBuf {
    fn append<P: AsRef<Path>>(&mut self, path: P) {
        let path = path.as_ref();
        let v = unsafe { &mut *(self as *mut PathBuf as *mut Vec<u8>) };

        if v.is_empty() && path.as_os_str().is_empty() {
            return;
        } else if !v.is_empty() {
            v.push(SEP);
        }

        v.extend(path.as_os_str().as_bytes());

        *v = normalize_vec(v);
    }
}

/// Extension trait for [`Path`].
pub trait NormPathExt {
    /// Returns the base name of `self`.
    ///
    /// See [`base_name`].
    fn base_name(&self) -> PathBuf;

    /// Returns `path` appended to `self`.
    ///
    /// See [`NormPathBufExt::append`].
    fn concat<P: AsRef<Path>>(&self, path: P) -> PathBuf;

    /// Returns the directory name of `self`.
    ///
    /// See [`dir_name`].
    fn dir_name(&self) -> PathBuf;

    /// Returns the normalized equivalent of `self`.
    ///
    /// See [`normalize`].
    fn normalize(&self) -> PathBuf;
}

impl NormPathExt for Path {
    fn base_name(&self) -> PathBuf {
        base_name(self)
    }

    fn concat<P: AsRef<Path>>(&self, path: P) -> PathBuf {
        let mut b = self.to_path_buf();
        b.append(path);
        b
    }

    fn dir_name(&self) -> PathBuf {
        dir_name(self)
    }

    fn normalize(&self) -> PathBuf {
        normalize(self)
    }
}

/// Returns the last path component, following the final `/`.
///
/// See [`basename(3)`](http://man7.org/linux/man-pages/man3/basename.3.html).
///
/// # Differences with [`Path::file_name`]
///
/// - Performs normalization on the input path.
/// - Always returns a name (`/`, `.`, or `..`, whereas [`Path::file_name`] returns `None`).
/// - Returns a [`PathBuf`] instead of an [`OsStr`](std::ffi::OsStr).
///
/// # Example
///
/// ```
/// use std::path::Path;
/// use npath::base_name;
///
/// assert_eq!(base_name("/usr/lib"), Path::new("lib"));
/// assert_eq!(base_name("/usr/"),    Path::new("usr"));
/// assert_eq!(base_name("usr"),      Path::new("usr"));
/// assert_eq!(base_name("/"),        Path::new("/"));
/// assert_eq!(base_name("."),        Path::new("."));
/// assert_eq!(base_name(".."),       Path::new(".."));
/// ```
pub fn base_name<P: AsRef<Path>>(path: P) -> PathBuf {
    PathBuf::from(OsString::from_vec(base_name_vec(
        path.as_ref().as_os_str().as_bytes(),
    )))
}

// See <https://golang.org/pkg/path/filepath/#Base>.
fn base_name_vec(mut inp: &[u8]) -> Vec<u8> {
    if inp.is_empty() {
        return vec![DOT];
    }

    while !inp.is_empty() && inp[inp.len() - 1] == SEP {
        inp = &inp[0..inp.len() - 1]
    }

    let mut i = inp.len() as isize - 1;
    while i >= 0 && inp[i as usize] != SEP {
        i -= 1;
    }
    if i >= 0 {
        inp = &inp[i as usize + 1..];
    }

    if inp.is_empty() {
        return vec![SEP];
    }

    inp.to_vec()
}

/// Returns the path up to, but not including, the final `/`.
///
/// See [`dirname(3)`](http://man7.org/linux/man-pages/man3/dirname.3.html).
///
/// # Differences with [`Path::parent`]
///
/// - Performs normalization on the input path.
/// - Always returns a path (`/` when [`Path::parent`] returns `None`).
///
/// # Example
///
/// ```
/// use std::path::Path;
/// use npath::dir_name;
///
/// assert_eq!(dir_name("/usr/lib"), Path::new("/usr"));
/// assert_eq!(dir_name("/usr/"),    Path::new("/"));
/// assert_eq!(dir_name("usr"),      Path::new("."));
/// assert_eq!(dir_name("/"),        Path::new("/"));
/// assert_eq!(dir_name("."),        Path::new("."));
/// assert_eq!(dir_name(".."),       Path::new("."));
/// ```
pub fn dir_name<P: AsRef<Path>>(path: P) -> PathBuf {
    PathBuf::from(OsString::from_vec(dir_name_vec(
        path.as_ref().as_os_str().as_bytes(),
    )))
}

// See <https://golang.org/pkg/path/filepath/#Dir>.
fn dir_name_vec(inp: &[u8]) -> Vec<u8> {
    let inp = normalize_vec(&inp);

    let mut i = inp.len() as isize - 1;

    while i >= 0 && inp[i as usize] != SEP {
        i -= 1;
    }

    if i > 0 && inp[i as usize] == SEP {
        i -= 1;
    }

    let dir = &inp[..(i + 1) as usize];
    if dir.is_empty() {
        return vec![DOT];
    }

    dir.to_vec()
}

/// Returns the shortest equivalent path by pure lexical processing.
///
/// It applies the following rules:
///
/// 1. Replace repeated `/` with a single one.
/// 2. Eliminate `.` path components (the current directory).
/// 3. Consume inner `..` path components (the parent directory), including components preceded by
///    a rooted path (replace `/..` by `/`).
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
/// use std::path::Path;
/// use npath::normalize;
///
/// assert_eq!(normalize("usr/lib"),                 Path::new("usr/lib"));
/// assert_eq!(normalize("usr//lib"),                Path::new("usr/lib"));
/// assert_eq!(normalize("usr/lib/."),               Path::new("usr/lib"));
/// assert_eq!(normalize("usr/lib/gcc/.."),          Path::new("usr/lib"));
/// assert_eq!(normalize("/../usr/lib"),             Path::new("/usr/lib"));
/// assert_eq!(normalize("/../usr/bin/../././/lib"), Path::new("/usr/lib"));
/// ```
pub fn normalize<P: AsRef<Path>>(path: P) -> PathBuf {
    PathBuf::from(OsString::from_vec(normalize_vec(
        path.as_ref().as_os_str().as_bytes(),
    )))
}

// See <https://golang.org/pkg/path/filepath/#Clean>.
fn normalize_vec(inp: &[u8]) -> Vec<u8> {
    let mut out = vec![];

    if inp.is_empty() {
        out.push(DOT);
        return out;
    }

    let rooted = inp[0] == SEP;

    let n = inp.len();

    let (mut r, mut dotdot) = if rooted {
        out.push(SEP);
        (1, 1)
    } else {
        (0, 0)
    };

    while r < inp.len() {
        if inp[r] == SEP || (inp[r] == DOT && (r + 1 == n || inp[r + 1] == SEP)) {
            r += 1;
        } else if inp[r] == DOT && inp[r + 1] == DOT && (r + 2 == n || inp[r + 2] == SEP) {
            r += 2;
            if out.len() > dotdot {
                let mut w = out.len() - 1;
                while w > dotdot && out[w] != SEP {
                    w -= 1;
                }
                out.truncate(w);
            } else if !rooted {
                if !out.is_empty() {
                    out.push(SEP);
                }
                out.push(DOT);
                out.push(DOT);
                dotdot = out.len();
            }
        } else {
            if rooted && out.len() != 1 || !rooted && !out.is_empty() {
                out.push(SEP);
            }

            while r < n && inp[r] != SEP {
                out.push(inp[r]);
                r += 1;
            }
        }
    }

    if out.is_empty() {
        out.push(DOT);
    }

    out
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
            assert_eq!(super::base_name(c.0).as_os_str(), c.1);
        }
    }

    #[test]
    fn concat_test() {
        let cases = vec![
            (("a", "b"), "a/b"),
            (("a", ""), "a"),
            (("", "b"), "b"),
            (("/", "a"), "/a"),
            (("/", "a/b"), "/a/b"),
            (("/", ""), "/"),
            (("//", "a"), "/a"),
            (("/a", "b"), "/a/b"),
            (("a/", "b"), "a/b"),
            (("a/", ""), "a"),
            (("", ""), ""),
        ];

        for c in cases {
            assert_eq!(Path::new((c.0).0).concat((c.0).1).as_os_str(), c.1);
        }
    }

    #[test]
    fn dir_name_test() {
        let cases = vec![
            ("", "."),
            (".", "."),
            ("/.", "/"),
            ("/", "/"),
            ("////", "/"),
            ("/foo", "/"),
            ("x/", "."), // different from Go's `filepath.Dir` buggy behavior ("x/" -> "x")
            ("x///", "."), // different from Go's `filepath.Dir` buggy behavior ("x///" -> "x")
            ("abc", "."),
            ("abc/def", "abc"),
            ("a/b/.x", "a/b"),
            ("a/b/c.", "a/b"),
            ("a/b/c.x", "a/b"),
        ];

        for c in cases {
            assert_eq!(super::dir_name(c.0).as_os_str(), c.1);
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
            assert_eq!(super::normalize(c.0).as_os_str(), c.1);
        }
    }
}
