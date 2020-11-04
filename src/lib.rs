#![feature(const_str_from_utf8_unchecked)]

//! Normalized Unix Paths
//!
//! - Pure lexical processing path normalization.
//! - Concatenation of absolute paths.
//! - POSIX [`dirname(3)`] and [`basename(3)`] equivalents.
//!
//! # [`Path`]
//!
//! | std                    | npath                            |
//! |------------------------|----------------------------------|
//! | [`Path::file_name`]    | [`NormPathExt::base`]            |
//! | [`Path::parent`]       | [`NormPathExt::dir`]             |
//! | [`Path::join`]         | [`NormPathExt::lexical_join`]    |
//! | [`Path::canonicalize`] | [`NormPathExt::normalize`]       |
//! |                        | [`NormPathExt::relative_to`]     |
//! |                        | [`NormPathExt::try_relative_to`] |
//!
//! # [`PathBuf`]
//!
//! | std                  | npath                             |
//! |----------------------|-----------------------------------|
//! | [`PathBuf::push`]    | [`NormPathBufExt::lexical_push`] |
//!
//! [`dirname(3)`]: http://man7.org/linux/man-pages/man3/dirname.3.html
//! [`basename(3)`]: http://man7.org/linux/man-pages/man3/basename.3.html

use std::env;
use std::io::Result;
use std::path::{Component, Path, PathBuf, MAIN_SEPARATOR};

const MAIN_SEPARATOR_STR: &'static str =
    unsafe { std::str::from_utf8_unchecked(&[MAIN_SEPARATOR as u8]) };

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
    /// path.lexical_push("bin");  // relative
    /// path.lexical_push("/cat"); // absolute
    ///
    /// assert_eq!(path, PathBuf::from("/usr/bin/cat"));
    /// ```
    fn lexical_push<P: AsRef<Path>>(&mut self, path: P);
}

impl NormPathBufExt for PathBuf {
    fn lexical_push<P: AsRef<Path>>(&mut self, path: P) {
        self.extend(
            path.as_ref()
                .components()
                .filter(|c| match c {
                    Component::ParentDir | Component::Normal(_) => true,
                    _ => false,
                })
                .map(|c| c.as_os_str()),
        )
    }
}

/// Extension trait for [`Path`].
pub trait NormPathExt {
    /// Returns the absolute path.
    ///
    /// - If the path is absolute, it returns the normalized equivalent.
    /// - If the path is relative, it is appended to [`std::env::current_dir`].
    ///
    /// # Example
    ///
    /// ```
    /// use std::path::{Path, PathBuf};
    /// use npath::NormPathExt;
    ///
    /// assert_eq!(Path::new("/usr").absolute().unwrap(), PathBuf::from("/usr"));
    ///
    /// if let Ok(cwd) = std::env::current_dir() {
    ///     assert_eq!(Path::new("lib").absolute().unwrap(), cwd.lexical_join("lib"));
    /// }
    /// ```
    fn absolute(&self) -> Result<PathBuf>;

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
    /// use std::path::Path;
    /// use npath::NormPathExt;
    ///
    /// assert_eq!(Path::new("/usr/lib").base(), Path::new("lib"));
    /// assert_eq!(Path::new("/usr/").base(),    Path::new("usr"));
    /// assert_eq!(Path::new("usr").base(),      Path::new("usr"));
    /// assert_eq!(Path::new("/").base(),        Path::new("/"));
    /// assert_eq!(Path::new(".").base(),        Path::new("."));
    /// assert_eq!(Path::new("..").base(),       Path::new(".."));
    /// ```
    fn base(&self) -> &Path;

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
    /// use std::path::Path;
    /// use npath::NormPathExt;
    ///
    /// assert_eq!(Path::new("/usr/lib").dir(), Path::new("/usr"));
    /// assert_eq!(Path::new("/usr/").dir(),    Path::new("/"));
    /// assert_eq!(Path::new("usr").dir(),      Path::new("."));
    /// assert_eq!(Path::new("/").dir(),        Path::new("/"));
    /// assert_eq!(Path::new(".").dir(),        Path::new("."));
    /// assert_eq!(Path::new("..").dir(),       Path::new("."));
    /// ```
    fn dir(&self) -> &Path;

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
    /// # Differences with [`Path::canonicalize`]
    ///
    /// This function **does not touch the filesystem, ever**:
    ///
    /// - It does not resolve symlinks.
    /// - It does not check if files/directories exists.
    /// - If the given path is relative, it returns a relative path.
    ///
    /// If `/a/b` is a symlink to `/d/e`, for `/a/b/../c`:
    ///
    /// - [`Path::canonicalize`] returns `/d/c`.
    /// - [`NormPathExt::normalize`] returns `/a/c`.
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
    /// See [`NormPathBufExt::lexical_push`].
    fn lexical_join<P: AsRef<Path>>(&self, path: P) -> PathBuf;

    /// Returns the relative path from `base` to `self`.
    ///
    /// The path is such that: `base.join(path) == self`.
    ///
    /// # Differences with [`NormPathExt::try_relative_to`]
    ///
    /// Only lexical operations are performed. If `self` can't be made relative to `base`, it
    /// returns `None` (fetching the current directory is required).
    ///
    /// # Example
    ///
    /// ```
    /// use std::path::{Path, PathBuf};
    /// use npath::NormPathExt;
    ///
    /// assert_eq!(Path::new("/usr/lib").relative_to("/usr"), Some(PathBuf::from("lib")));
    /// assert_eq!(Path::new("usr/bin").relative_to("var"),   Some(PathBuf::from("../usr/bin")));
    /// assert_eq!(Path::new("foo").relative_to("/"),         None);
    /// assert_eq!(Path::new("foo").relative_to(".."),        None);
    /// ```
    fn relative_to<P: AsRef<Path>>(&self, base: P) -> Option<PathBuf>;

    /// Returns the relative path from `base` to `self`.
    ///
    /// The path is such that: `base.join(path) == self`.
    ///
    /// # Differences with [`NormPathExt::relative_to`]
    ///
    /// A system call to determine the current working directory is required if one of `self` or
    /// `base` is relative.
    ///
    /// # Example
    ///
    /// ```
    /// use std::env;
    /// use std::path::{Path, PathBuf};
    /// use npath::NormPathExt;
    ///
    /// assert_eq!(Path::new("/usr/lib").try_relative_to("/usr").unwrap(), PathBuf::from("lib"));
    /// assert_eq!(Path::new("usr/bin").try_relative_to("var").unwrap(),   PathBuf::from("../usr/bin"));
    ///
    /// if let Ok(cwd) = env::current_dir() {
    ///     assert_eq!(Path::new("foo").try_relative_to("..").unwrap(), cwd.base().join("foo"));
    /// }
    /// ```
    fn try_relative_to<P: AsRef<Path>>(&self, base: P) -> Result<PathBuf>;
}

impl NormPathExt for Path {
    fn absolute(&self) -> Result<PathBuf> {
        if self.is_relative() {
            return Ok(env::current_dir()?.join(self));
        }

        Ok(self.to_path_buf())
    }

    fn base(&self) -> &Path {
        self.components()
            .next_back()
            .and_then(|c| match c {
                Component::Normal(p) => Some(Path::new(p)),
                Component::RootDir => Some(Path::new(MAIN_SEPARATOR_STR)),
                Component::CurDir => Some(Path::new(".")),
                Component::ParentDir => Some(Path::new("..")),
                _ => None,
            })
            .unwrap_or_else(|| Path::new("."))
    }

    fn dir(&self) -> &Path {
        let mut comps = self.components();
        comps
            .next_back()
            .and_then(|c| match c {
                Component::RootDir => Some(Path::new(MAIN_SEPARATOR_STR)),
                Component::Normal(_) | Component::CurDir | Component::ParentDir => {
                    let p = comps.as_path();
                    if p.as_os_str().is_empty() {
                        None
                    } else {
                        Some(p)
                    }
                }
                _ => None,
            })
            .unwrap_or_else(|| Path::new("."))
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

    fn lexical_join<P: AsRef<Path>>(&self, path: P) -> PathBuf {
        let mut p = self.to_path_buf();
        p.lexical_push(path);
        p
    }

    fn relative_to<P: AsRef<Path>>(&self, base: P) -> Option<PathBuf> {
        let base = base.as_ref().normalize();
        let path = self.normalize();

        if base.has_root() != path.has_root() {
            return None;
        }

        let mut base_components = base.components();
        let mut path_components = path.components();

        let mut base_head = base_components.next();
        let mut path_head = path_components.next();

        loop {
            match (base_head, path_head) {
                (Some(Component::Prefix(a)), Some(Component::Prefix(b))) if a != b => {
                    return None;
                }
                (Some(x), Some(y)) if x == y => {
                    base_head = base_components.next();
                    path_head = path_components.next();
                }
                (None, None) => return Some(PathBuf::from(".")),
                _ => {
                    let mut p = PathBuf::new();

                    if let Some(Component::ParentDir) = base_head {
                        return None;
                    }

                    if base_head.is_some() && base_head != Some(Component::CurDir) {
                        p.push("..");
                    }

                    while let Some(_) = base_components.next() {
                        p.push("..");
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

    fn try_relative_to<P: AsRef<Path>>(&self, base: P) -> Result<PathBuf> {
        let base = base.as_ref().absolute()?.normalize();
        let path = self.absolute()?.normalize();

        let mut base_components = base.components();
        let mut path_components = path.components();

        let mut base_head = base_components.next();
        let mut path_head = path_components.next();

        loop {
            match (base_head, path_head) {
                (Some(x), Some(y)) if x == y => {
                    base_head = base_components.next();
                    path_head = path_components.next();
                }
                (None, None) => return Ok(PathBuf::from(".")),
                _ => {
                    let mut p = PathBuf::new();

                    if base_head.is_some() {
                        p.push("..");
                    }

                    while let Some(_) = base_components.next() {
                        p.push("..");
                    }

                    if let Some(c) = path_head {
                        p.push(c);
                        p.extend(path_components);
                    }

                    return Ok(p);
                }
            }
        }
    }
}
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::NormPathExt;

    #[test]
    fn absolute_test() {
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
    fn base_name_test() {
        let cases = &[
            ("", "."),
            (".", "."),
            ("/.", "/"), // POSIX: "."
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
        let cases = &[
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
        let cases = &[
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
    fn lexical_join_test() {
        let cases = &[
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
            // Dot
            (("a", "."), "a"),
            (("a", ".."), "a/.."),
            (("a", "./b"), "a/b"),
            (("a", "../b"), "a/../b"),
            (("a", "b/."), "a/b"),
            (("a", "b/.."), "a/b/.."),
            (("a", "b/./c"), "a/b/c"),
            (("a", "b/../c"), "a/b/../c"),
        ];

        for c in cases {
            assert_eq!(Path::new((c.0).0).lexical_join((c.0).1).as_os_str(), c.1);
            // Absolute
            assert_eq!(
                Path::new((c.0).0)
                    .lexical_join(String::from("/") + (c.0).1)
                    .as_os_str(),
                c.1
            );
        }
    }

    #[test]
    fn relative_to_test() {
        let cases = &[
            ("a/b", "a/b", "."),
            ("a/b/.", "a/b", "."),
            ("a/b", "a/b/.", "."),
            ("./a/b", "a/b", "."),
            ("a/b", "./a/b", "."),
            ("ab/cd", "ab/cde", "../cde"),
            ("ab/cd", "ab/c", "../c"),
            ("a/b", "a/b/c/d", "c/d"),
            ("a/b", "a/b/../c", "../c"),
            ("a/b/../c", "a/b", "../b"),
            ("a/b/c", "a/c/d", "../../c/d"),
            ("a/b", "c/d", "../../c/d"),
            ("a/b/c/d", "a/b", "../.."),
            ("a/b/c/d", "a/b/", "../.."),
            ("a/b/c/d/", "a/b", "../.."),
            ("a/b/c/d/", "a/b/", "../.."),
            ("../../a/b", "../../a/b/c/d", "c/d"),
            ("/a/b", "/a/b", "."),
            ("/a/b/.", "/a/b", "."),
            ("/a/b", "/a/b/.", "."),
            ("/ab/cd", "/ab/cde", "../cde"),
            ("/ab/cd", "/ab/c", "../c"),
            ("/a/b", "/a/b/c/d", "c/d"),
            ("/a/b", "/a/b/../c", "../c"),
            ("/a/b/../c", "/a/b", "../b"),
            ("/a/b/c", "/a/c/d", "../../c/d"),
            ("/a/b", "/c/d", "../../c/d"),
            ("/a/b/c/d", "/a/b", "../.."),
            ("/a/b/c/d", "/a/b/", "../.."),
            ("/a/b/c/d/", "/a/b", "../.."),
            ("/a/b/c/d/", "/a/b/", "../.."),
            ("/../../a/b", "/../../a/b/c/d", "c/d"),
            (".", "a/b", "a/b"),
            (".", "..", ".."),
        ];

        for c in cases {
            let p = Path::new(c.1).relative_to(c.0);
            assert!(p.is_some());
            assert_eq!(p.unwrap().as_os_str(), c.2);
        }

        // Can't do purely lexically
        let cases = &[
            ("..", "."),
            ("..", "a"),
            ("../..", ".."),
            ("a", "/a"),
            ("/a", "a"),
        ];

        for c in cases {
            assert!(Path::new(c.1).relative_to(c.0).is_none());
        }
    }

    #[test]
    fn try_relative_to_test() {
        use std::env;

        let cases = &[
            ("a/b", "a/b", "."),
            ("a/b/.", "a/b", "."),
            ("a/b", "a/b/.", "."),
            ("./a/b", "a/b", "."),
            ("a/b", "./a/b", "."),
            ("ab/cd", "ab/cde", "../cde"),
            ("ab/cd", "ab/c", "../c"),
            ("a/b", "a/b/c/d", "c/d"),
            ("a/b", "a/b/../c", "../c"),
            ("a/b/../c", "a/b", "../b"),
            ("a/b/c", "a/c/d", "../../c/d"),
            ("a/b", "c/d", "../../c/d"),
            ("a/b/c/d", "a/b", "../.."),
            ("a/b/c/d", "a/b/", "../.."),
            ("a/b/c/d/", "a/b", "../.."),
            ("a/b/c/d/", "a/b/", "../.."),
            ("../../a/b", "../../a/b/c/d", "c/d"),
            ("/a/b", "/a/b", "."),
            ("/a/b/.", "/a/b", "."),
            ("/a/b", "/a/b/.", "."),
            ("/ab/cd", "/ab/cde", "../cde"),
            ("/ab/cd", "/ab/c", "../c"),
            ("/a/b", "/a/b/c/d", "c/d"),
            ("/a/b", "/a/b/../c", "../c"),
            ("/a/b/../c", "/a/b", "../b"),
            ("/a/b/c", "/a/c/d", "../../c/d"),
            ("/a/b", "/c/d", "../../c/d"),
            ("/a/b/c/d", "/a/b", "../.."),
            ("/a/b/c/d", "/a/b/", "../.."),
            ("/a/b/c/d/", "/a/b", "../.."),
            ("/a/b/c/d/", "/a/b/", "../.."),
            ("/../../a/b", "/../../a/b/c/d", "c/d"),
            (".", "a/b", "a/b"),
            (".", "..", ".."),
        ];

        for c in cases {
            let p = Path::new(c.1).try_relative_to(c.0);
            assert!(p.is_ok());
            assert_eq!(p.unwrap().as_os_str(), c.2);
        }

        // The result depends on the current directory
        if let Ok(c) = env::current_dir() {
            let mut root = std::path::PathBuf::new();

            for _ in 0..c.components().count() {
                root.push("..");
            }

            let cases = &[
                ("..", ".", c.base().to_path_buf()),
                ("..", "a", c.base().join("a")),
                ("../..", "..", c.dir().base().to_path_buf()),
                ("a", "/a", root.join("a")),
                ("/a", "a", Path::new("..").lexical_join(c).join("a")),
            ];

            for c in cases {
                let p = Path::new(c.1).try_relative_to(c.0);
                assert!(p.is_ok());
                assert_eq!(p.unwrap().as_os_str(), c.2);
            }
        }
    }
}
