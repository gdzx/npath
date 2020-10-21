//! Unix Path Handling Utilities
//!
//! This library provides:
//! * path normalization through pure lexical processing (alternative to [`fs::canonicalize`]),
//! * concatenation of absolute paths (alternative to [`Path::join`] and [`PathBuf::push`]),
//! * equivalents of POSIX [`dirname(3)`] and [`basename(3)`] functions.
//!
//! You might want to look at:
//! - functions [`dir_name`], [`base_name`] and [`normalize`],
//! - methods [`NormPathExt::concat`] and [`NormPathBufExt::append`].
//!
//! [`fs::canonicalize`]: https://doc.rust-lang.org/std/fs/fn.canonicalize.html
//!
//! [`Path::join`]: https://doc.rust-lang.org/src/std/struct.Path.html#method.join
//! [`Path::push`]: https://doc.rust-lang.org/src/std/struct.PathBuf.html#method.push
//!
//! [`dirname(3)`]: http://man7.org/linux/man-pages/man3/dirname.3.html
//! [`basename(3)`]: http://man7.org/linux/man-pages/man3/basename.3.html
//!
//! [`dir_name`]: ./fn.dir_name.html
//! [`base_name`]: ./fn.dir_name.html
//! [`normalize_name`]: ./fn.dir_name.html
//!
//! [`NormPathExt::concat`]: ./trait.NormPathExt.html#tymethod.concat
//! [`NormPathBufExt::append`]: ./trait.NormPathBufExt.html#tymethod.append

use std::ffi::OsString;
use std::os::unix::prelude::*;
use std::path::{Path, PathBuf};

const SEP: u8 = b'/';
const DOT: u8 = b'.';

/// Returns the path up to, but not including, the final `/`.
///
/// See [`dirname(3)`](http://man7.org/linux/man-pages/man3/dirname.3.html).
///
/// # Differences with [`Path::parent`]
///
/// This function:
/// - performs normalization on the input,
/// - always returns a path (`/` when [`Path::parent`] returns `None`).
///
/// [`Path::parent`]: https://doc.rust-lang.org/src/std/struct.Path.html#method.parent
///
/// # Example
///
/// ```
/// use std::path::Path;
/// use npath::dir_name;
///
/// fn main() {
///     assert_eq!(dir_name("/usr/lib"), Path::new("/usr"));
///     assert_eq!(dir_name("/usr/"), Path::new("/"));
///     assert_eq!(dir_name("usr"), Path::new("."));
///     assert_eq!(dir_name("/"), Path::new("/"));
///     assert_eq!(dir_name("."), Path::new("."));
///     assert_eq!(dir_name(".."), Path::new("."));
/// }
/// ```
pub fn dir_name<P: AsRef<Path>>(path: P) -> PathBuf {
    PathBuf::from(OsString::from_vec(dir_name_vec(
        path.as_ref().as_os_str().as_bytes(),
    )))
}

/// Returns the last path component, following the final `/`.
///
/// See [`basename(3)`](http://man7.org/linux/man-pages/man3/basename.3.html).
///
/// # Differences with [`Path::file_name`]
///
/// This function:
/// - performs normalization on the input,
/// - always returns a name (`/`, `.` or `..` where [`Path::file_name`] returns `None`).
///
/// [`Path::file_name`]: https://doc.rust-lang.org/src/std/struct.Path.html#method.file_name
///
/// # Example
///
/// ```
/// use std::path::Path;
/// use npath::base_name;
///
/// fn main() {
///     assert_eq!(base_name("/usr/lib"), Path::new("lib"));
///     assert_eq!(base_name("/usr/"), Path::new("usr"));
///     assert_eq!(base_name("usr"), Path::new("usr"));
///     assert_eq!(base_name("/"), Path::new("/"));
///     assert_eq!(base_name("."), Path::new("."));
///     assert_eq!(base_name(".."), Path::new(".."));
/// }
/// ```
pub fn base_name<P: AsRef<Path>>(path: P) -> PathBuf {
    PathBuf::from(OsString::from_vec(base_name_vec(
        path.as_ref().as_os_str().as_bytes(),
    )))
}

/// Returns the shortest equivalent path by pure lexical processing.
///
/// It applies the following rules:
/// 1. replaces multiple `/` with a single one,
/// 2. eliminates each `.` path name element (the current directory),
/// 3. eliminates each inner `..` path name element (the parent directory) along
///    with the non-`..` element that precedes it,
/// 4. eliminates `..` elements that begin a rooted path,
///    that is, replace `/..` by `/` at the beginning of a path
///
/// # Differences with [`fs::canonicalize`]
///
/// This function **does not touch the filesystem, ever**:
/// - it does not resolve symlinks,
/// - it does not check if files/directories exists,
/// - if the given path is relative, it returns a relative path, etc.
///
/// If `/a/b` is a symlink to `/d/e`, then `/a/b/../c` is `/d/c` (and not `/a/c` that this
/// function will return).
///
/// [`fs::canonicalize`]: https://doc.rust-lang.org/std/fs/fn.canonicalize.html
///
/// # Example
///
/// ```
/// use std::path::Path;
/// use npath::normalize;
///
/// fn main() {
///     assert_eq!(normalize("usr/lib"), Path::new("usr/lib"));
///     assert_eq!(normalize("usr//lib"), Path::new("usr/lib"));
///     assert_eq!(normalize("usr/lib/."), Path::new("usr/lib"));
///     assert_eq!(normalize("usr/lib/gcc/.."), Path::new("usr/lib"));
///     assert_eq!(normalize("/../usr/lib"), Path::new("/usr/lib"));
///     assert_eq!(normalize("/../usr/bin/../././/lib"), Path::new("/usr/lib"));
/// }
/// ```
pub fn normalize<P: AsRef<Path>>(path: P) -> PathBuf {
    PathBuf::from(OsString::from_vec(normalize_vec(
        path.as_ref().as_os_str().as_bytes(),
    )))
}

/// Extension trait for [`PathBuf`].
///
/// [`PathBuf`]: https://doc.rust-lang.org/src/std/struct.PathBuf.html
pub trait NormPathBufExt {
    /// Appends `path` to `self`.
    ///
    /// # Differences with [`PathBuf::push`]
    ///
    /// If `path` is absolute, it doesn't replace the current path.
    ///
    /// [`PathBuf::push`]: https://doc.rust-lang.org/src/std/path/struct.PathBuf.html#method.push
    ///
    /// # Examples
    ///
    /// ```
    /// use std::path::{Path, PathBuf};
    /// use npath::NormPathBufExt;
    ///
    /// fn main() {
    ///     let mut path = PathBuf::from("/usr");
    ///     path.append("bin");   // relative
    ///     path.append("/cat");  // absolute
    ///
    ///     assert_eq!(path, Path::new("/usr/bin/cat"));
    /// }
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
///
/// [`Path`]: https://doc.rust-lang.org/src/std/struct.Path.html
pub trait NormPathExt {
    /// Returns the base name of `self`.
    ///
    /// See [`base_name`](./fn.base_name.html).
    fn base_name(&self) -> PathBuf;

    /// Returns the directory name of `self`.
    ///
    /// See [`dir_name`](./fn.dir_name.html).
    fn dir_name(&self) -> PathBuf;

    /// Creates an owned [`PathBuf`] with `path` appended to `self`.
    ///
    /// See [`NormPathBufExt::append`].
    ///
    /// [`PathBuf`]: https://doc.rust-lang.org/src/std/struct.PathBuf.html
    /// [`NormPathBufExt::append`]: ./trait.NormPathBufExt.html#tymethod.append
    fn concat<P: AsRef<Path>>(&self, path: P) -> PathBuf;

    /// Creates a normalized owned [`PathBuf`] of `self`.
    ///
    /// See [`normalize`](./fn.normalize.html).
    ///
    /// [`PathBuf`]: https://doc.rust-lang.org/src/std/struct.PathBuf.html
    fn normalize(&self) -> PathBuf;
}

impl NormPathExt for Path {
    fn base_name(&self) -> PathBuf {
        base_name(self)
    }

    fn dir_name(&self) -> PathBuf {
        dir_name(self)
    }

    fn concat<P: AsRef<Path>>(&self, path: P) -> PathBuf {
        let mut b = self.to_path_buf();
        b.append(path);
        b
    }

    fn normalize(&self) -> PathBuf {
        normalize(self)
    }
}

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
    fn base_test() {
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
    fn dir_test() {
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
