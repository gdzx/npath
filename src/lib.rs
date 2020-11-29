#![feature(const_str_from_utf8_unchecked)]
#![feature(osstring_ascii)]

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
//! | -                      | [`NormPathExt::is_inside`]       |
//! | -                      | [`NormPathExt::relative_to`]     |
//! | -                      | [`NormPathExt::try_relative_to`] |
//! | -                      | [`NormPathExt::rooted_join`]     |
//! | -                      | [`NormPathExt::try_rooted_join`] |
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
use std::ffi::{OsStr, OsString};
use std::io::{Error, ErrorKind, Result};
use std::path::{is_separator, Component, Path, PathBuf, Prefix, PrefixComponent, MAIN_SEPARATOR};

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
        let prefix = get_prefix(self.as_path());
        let prefix_is_disk = matches!(prefix.map(|p| p.kind()), Some(Prefix::Disk(_)));
        let prefix_len = prefix.map(|p| p.as_os_str().len());

        let base = unsafe { &mut *(self as *mut PathBuf as *mut Vec<u8>) };
        let mut path = unsafe { &*(path.as_ref() as *const Path as *const [u8]) };

        while !path.is_empty() && is_separator(path[0] as char) {
            path = &path[1..];
        }

        if path.is_empty() {
            return;
        }

        if !base.is_empty()
            && !is_separator(*base.last().unwrap() as char)
            && !(prefix_is_disk && Some(base.len()) == prefix_len)
        {
            base.push(MAIN_SEPARATOR as u8);
        }

        base.extend(path);
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
    /// # if cfg!(unix) {
    /// assert_eq!(Path::new("/usr").absolute().unwrap(), PathBuf::from("/usr"));
    ///
    /// if let Ok(cwd) = std::env::current_dir() {
    ///     assert_eq!(Path::new("lib").absolute().unwrap(), cwd.lexical_join("lib"));
    /// }
    /// # }
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

    /// Returns whether `self` is lexically inside of `base`.
    ///
    /// `self` is considered "lexically inside" `base` if and only if:
    ///
    /// - `self` and `base` are both relative, or both absolute.
    /// - `self` does not have any component outside of `base`.
    ///
    /// When `base` is relative, it returns false if it is necessary to know the absolute path
    /// (when it contains ".." followed by a normal component, there is no way to know whether it
    /// is re-entering a previous directory or if it branches off). To avoid this edge case, ensure
    /// both path are absolute with one of these methods:
    ///
    /// - [`NormPathExt::absolute`].
    /// - [`Path::canonicalize`].
    ///
    /// # Example
    ///
    /// ```
    /// use std::path::Path;
    /// use npath::NormPathExt;
    ///
    /// assert!(Path::new("/srv").is_inside("/"));
    /// assert!(Path::new("/srv").is_inside("/srv"));
    /// assert!(Path::new("/srv/file.txt").is_inside("/srv"));
    ///
    /// assert!(Path::new("srv").is_inside("srv"));
    /// assert!(Path::new("srv").is_inside("."));
    /// assert!(Path::new("srv").is_inside(".."));
    /// assert!(Path::new("../srv").is_inside(".."));
    ///
    /// assert!(!Path::new("srv").is_inside("../foo"));
    /// assert!(!Path::new("/srv/..").is_inside("/srv"));
    /// assert!(!Path::new("file.txt").is_inside("/srv"));
    /// ```
    fn is_inside<P: AsRef<Path>>(&self, base: P) -> bool;

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
    /// returns `None` (fetching the current directory is required, one path is absolute while the
    /// other is relative, or the path have differents prefixes).
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

    /// Returns `path` restricted to `self`.
    ///
    /// This methods works as if `base` was the root directory. The returned path is guaranteed to
    /// be lexically inside `base`.
    ///
    /// # Example
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
    /// See [`NormPathExt::rooted_join2`].
    fn rooted_join2<P: AsRef<Path>>(&self, path: P) -> PathBuf;

    /// Returns `path` restricted to `self`.
    ///
    /// `self` and `path` are converted to absolute path with [`NormPathExt::absolute`], they are
    /// joined with [`NormPathExt::lexical_join`], and the result is normalized with
    /// [`NormPathExt::normalize`].
    ///
    /// # Differences with [`NormPathExt::rooted_join`]
    ///
    /// If `path` points to a location outside of `base`, it returns an error.
    ///
    /// # Example
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
            .unwrap_or_else(|| Path::new("."))
    }

    fn is_inside<P: AsRef<Path>>(&self, base: P) -> bool {
        let base = base.as_ref().normalize();
        let path = self.normalize();

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

    fn normalize(&self) -> PathBuf {
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
                (Some(a @ Component::Prefix(_)), Some(b @ Component::Prefix(_)))
                    if !are_equal(&a, &b) =>
                {
                    return None;
                }
                (Some(x), Some(y)) if are_equal(&x, &y) => {
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
                (Some(x), Some(y)) if are_equal(&x, &y) => {
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

    fn rooted_join<P: AsRef<Path>>(&self, path: P) -> PathBuf {
        self.lexical_join(normalize_rooted(path.as_ref()))
    }

    fn rooted_join2<P: AsRef<Path>>(&self, path: P) -> PathBuf {
        let path = path.as_ref();

        // Ensure path is absolute so normalize can eliminate all ".." components
        let path = if path.is_relative() {
            Path::new("/").join(path).normalize()
        } else {
            path.normalize()
        };

        self.lexical_join(path)
    }

    // <https://github.com/django/django/blob/master/django/utils/_os.py>
    fn try_rooted_join<P: AsRef<Path>>(&self, path: P) -> Result<PathBuf> {
        // Make absolute and normalize all paths
        let base = self.absolute()?.normalize();
        let path = self.lexical_join(path).absolute()?.normalize();

        // For `path` to be located inside `base`, either:
        // - It starts with `base` + "/"
        // - It is equal to `base`
        // - It is the root directory "/"
        if !path.starts_with(join_os_str(&base, "/")) && path != base && base.file_name().is_some()
        {
            return Err(Error::new(
                ErrorKind::Other,
                "Path outside of base directory",
            ));
        }

        Ok(path)
    }
}

// TODO: Handle prefixes containing / (limited by the prefix parsing code, avoid comparing OsStr of
// the full prefix).
fn are_equal(a: &Component, b: &Component) -> bool {
    if cfg!(windows) {
        return a.as_os_str().to_ascii_lowercase() == b.as_os_str().to_ascii_lowercase();
    }
    return a == b;
}

fn get_prefix(path: &Path) -> Option<PrefixComponent> {
    path.components().next().and_then(|c| {
        if let Component::Prefix(p) = c {
            return Some(p);
        } else {
            None
        }
    })
}

fn join_os_str<S1: AsRef<OsStr>, S2: AsRef<OsStr>>(a: S1, b: S2) -> OsString {
    let mut res = a.as_ref().to_os_string();
    res.push(b);
    res
}

// Eliminate all ".." components
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

#[cfg(test)]
mod tests {
    use super::{NormPathBufExt, NormPathExt};
    use std::path::{Path, PathBuf};

    #[test]
    #[cfg(unix)]
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
    #[cfg(windows)]
    fn absolute_test() {
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

    #[test]
    #[cfg(unix)]
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
    #[cfg(windows)]
    fn base_name_test() {
        let cases = &[
            (r"c:\", r"\"),
            (r"c:.", "."),
            (r"c:\a\b", "b"),
            (r"c:a\b", "b"),
            (r"c:a\b\c", "c"),
            (r"\\host\share\", r"\"),
            (r"\\host\share\a", "a"),
            (r"\\host\share\a\b", "b"),
        ];

        for c in cases {
            assert_eq!(Path::new(c.0).base().as_os_str(), c.1);
        }
    }

    #[test]
    #[cfg(unix)]
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
    #[cfg(windows)]
    fn dir_name_test() {
        let cases = &[
            (r"c:\", r"c:\"),
            (r"c:.", r"c:."),
            (r"c:\a\b", r"c:\a"),
            (r"c:a\b", r"c:a"),
            (r"c:a\b\c", r"c:a\b"),
            (r"\\host\share", r"\\host\share"),
            (r"\\host\share\", r"\\host\share\"),
            (r"\\host\share\a", r"\\host\share\"),
            (r"\\host\share\a\b", r"\\host\share\a"),
        ];

        for c in cases {
            assert_eq!(Path::new(c.0).dir().as_os_str(), c.1);
        }
    }

    #[test]
    #[cfg(unix)]
    fn is_inside_test() {
        assert!(Path::new("/").is_inside("/"));
        assert!(Path::new(".").is_inside("."));

        assert!(Path::new("/srv").is_inside("/"));
        assert!(Path::new("/srv").is_inside("//"));
        assert!(Path::new("/srv/").is_inside("/"));
        assert!(Path::new("/srv/.").is_inside("/"));
        assert!(Path::new("/srv/..").is_inside("/"));
        assert!(Path::new("/srv/../").is_inside("/"));

        assert!(Path::new("/srv").is_inside("/srv"));
        assert!(Path::new("/srv/").is_inside("/srv"));
        assert!(Path::new("/srv/.").is_inside("/srv"));

        assert!(Path::new("/srv").is_inside("/srv/"));
        assert!(Path::new("/srv/").is_inside("/srv/"));
        assert!(Path::new("/srv/.").is_inside("/srv/"));

        assert!(Path::new("/srv").is_inside("/srv/."));
        assert!(Path::new("/srv/").is_inside("/srv/."));
        assert!(Path::new("/srv/.").is_inside("/srv/."));

        assert!(Path::new("/srv/file.txt").is_inside("/srv"));

        assert!(Path::new("srv").is_inside("srv"));
        assert!(Path::new("srv").is_inside("."));

        assert!(!Path::new("file.txt").is_inside("/srv"));
        assert!(!Path::new("srv/file.txt").is_inside("/srv"));

        assert!(!Path::new("/srv/..").is_inside("/srv"));

        assert!(Path::new("foo").is_inside(".."));
        assert!(!Path::new("foo").is_inside("../bar"));
        assert!(!Path::new("/foo").is_inside(".."));
    }

    #[test]
    #[cfg(unix)]
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
    #[cfg(windows)]
    fn normalize_test() {
        let cases = &[
            (r"c:", r"c:"), // Go: "c:."
            (r"c:\", r"c:\"),
            (r"c:\abc", r"c:\abc"),
            (r"c:abc\..\..\.\.\..\def", r"c:..\..\def"),
            (r"c:\abc\def\..\..", r"c:\"),
            (r"c:\..\abc", r"c:\abc"),
            (r"c:..\abc", r"c:..\abc"),
            (r"\", r"\"),
            (r"/", r"\"),
            (r"\\i\..\c$", r"\\i\..\c$"),     // Go: "\c$" (bogus)
            (r"\\i\..\i\c$", r"\\i\..\i\c$"), // Go: "\i\c$" (bogus)
            (r"\\i\..\I\c$", r"\\i\..\I\c$"), // Go: "\I\c$" (bogus)
            (r"\\host\share\foo\..\bar", r"\\host\share\bar"),
            (r"//host/share/foo/../baz", r"\host\share\baz"), // GetFullPathName: "\\host\share\baz"
            (r"\\a\b\..\c", r"\\a\b\c"),
            (r"\\a\b", r"\\a\b\"), // Go: "\\a\b"
            (r"\\a\..\", r"\\a\..\"),
            // Issue with std::sys::path::parse_prefix (ignores UNC with empty server and share)
            (r"\\\a\..\", r"\"), // GetFullPathName: "\\\a\" (UNC prefix)
            (r"\\\\a\..", r"\"), // GetFullPathName: "\\\" (UNC prefix)
            // Issue with std::sys::path::parse_prefix (only considers "\\")
            (r"//a\..\", r"\"),
        ];

        for c in cases {
            assert_eq!(Path::new(c.0).normalize().as_os_str(), c.1);
        }
    }

    #[test]
    #[cfg(unix)]
    fn lexical_join_test() {
        let cases = &[
            (vec!["a", "b"], "a/b"),
            (vec!["a", ""], "a"),
            (vec!["", "b"], "b"),
            (vec!["/", "a"], "/a"),
            (vec!["/", "a/b"], "/a/b"),
            (vec!["/", ""], "/"),
            (vec!["//", "a"], "//a"), // Go: "/a"
            (vec!["/a", "b"], "/a/b"),
            (vec!["a/", "b"], "a/b"),
            (vec!["a/", ""], "a/"), // Go: "a"
            (vec!["", ""], ""),
            (vec!["/", "a", "b"], "/a/b"),
            // Dot
            (vec!["a", "."], "a/."),
            (vec!["a", ".."], "a/.."),
            (vec!["a", "./b"], "a/./b"),
            (vec!["a", "../b"], "a/../b"),
            (vec!["a", "b/."], "a/b/."),
            (vec!["a", "b/.."], "a/b/.."),
            (vec!["a", "b/./c"], "a/b/./c"),
            (vec!["a", "b/../c"], "a/b/../c"),
        ];

        for c in cases {
            let mut p = PathBuf::from(c.0[0]);

            for s in &c.0[1..] {
                p.lexical_push(s);
            }

            assert_eq!(p.as_os_str(), c.1);
        }

        // Redo the tests with a "/" before each component
        for c in cases {
            let mut p = PathBuf::from(c.0[0]);

            for s in &c.0[1..] {
                p.lexical_push(String::from("/") + s);
            }

            assert_eq!(p.as_os_str(), c.1);
        }
    }

    #[test]
    #[cfg(windows)]
    fn lexical_join_test() {
        let cases = &[
            (vec!["directory", "file"], r"directory\file"),
            (vec![r"C:\Windows\", "System32"], r"C:\Windows\System32"),
            (vec![r"C:\Windows\", ""], r"C:\Windows\"), // Go: "C:\Windows"
            (vec![r"C:\", "Windows"], r"C:\Windows"),
            (vec![r"C:", "a"], "C:a"),
            (vec![r"C:", r"a\b"], r"C:a\b"),
            (vec![r"C:", "a", "b"], r"C:a\b"),
            (vec![r"C:", "", "b"], "C:b"),
            (vec![r"C:", "", "", "b"], "C:b"),
            (vec![r"C:", ""], "C:"),       // Go: "C:."
            (vec![r"C:", "", ""], "C:"),   // Go: "C:."
            (vec![r"C:.", "a"], r"C:.\a"), // Go: "C:a"
            (vec![r"C:a", "b"], r"C:a\b"),
            (vec![r"C:a", "b", "d"], r"C:a\b\d"),
            (vec![r"\\host\share", "foo"], r"\\host\share\foo"),
            (vec![r"\\host\share\foo"], r"\\host\share\foo"),
            (vec![r"//host/share", "foo/bar"], r"//host/share\foo/bar"), // Go: "\\host\share\foo\bar"
            (vec![r"\"], r"\"),
            (vec![r"\", ""], r"\"),
            (vec![r"\", "a"], r"\a"),
            (vec![r"\\", "a"], r"\\a"), // Go: "\a"
            (vec![r"\", "a", "b"], r"\a\b"),
            (vec![r"\\", "a", "b"], r"\\a\b"), // Go: "\a\b"
            (vec![r"\", r"\\a\b", "c"], r"\a\b\c"),
            (vec![r"\\a", "b", "c"], r"\\a\b\c"), // Go: "\a\b\c"
            (vec![r"\\a\", "b", "c"], r"\\a\b\c"), // Go: "\a\b\c"
        ];

        for c in cases {
            let mut p = PathBuf::from(c.0[0]);

            for s in &c.0[1..] {
                p.lexical_push(s);
            }

            assert_eq!(p.as_os_str(), c.1);
        }

        // Redo the tests with a "\" before each component
        for c in cases {
            let mut p = PathBuf::from(c.0[0]);

            for s in &c.0[1..] {
                p.lexical_push(String::from(r"\") + s);
            }

            assert_eq!(p.as_os_str(), c.1);
        }
    }

    #[test]
    #[cfg(unix)]
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
    #[cfg(windows)]
    fn relative_to_test() {
        let cases = &[
            (r"C:a\b\c", r"C:a/b/d", r"..\d"),
            (r"C:\Projects", r"c:\projects\src", r"src"),
            (r"C:\Projects", r"c:\projects", r"."),
            (r"C:\Projects\a\..", r"c:\projects", r"."),
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
            (r"..\..", ".."),
            ("a", r"\a"),
            (r"\a", "a"),
        ];

        for c in cases {
            assert!(Path::new(c.1).relative_to(c.0).is_none());
        }

        // There is no relative path
        let cases = &[(r"C:\", r"D:\"), (r"C:", r"D:")];

        for c in cases {
            assert!(Path::new(c.1).relative_to(c.0).is_none());
        }
    }

    #[test]
    #[cfg(unix)]
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

    #[test]
    #[cfg(windows)]
    fn try_relative_to_test() {
        let cases = &[
            (r"C:a\b\c", r"C:a/b/d", r"..\d"),
            (r"C:\Projects", r"c:\projects\src", r"src"),
            (r"C:\Projects", r"c:\projects", r"."),
            (r"C:\Projects\a\..", r"c:\projects", r"."),
        ];

        for c in cases {
            let p = Path::new(c.1).try_relative_to(c.0);
            assert!(p.is_ok());
            assert_eq!(p.unwrap().as_os_str(), c.2);
        }

        // TODO: there are some cases where there is no relative paths. Need to change the return
        // type of try_relative_to.
        //let cases = &[(r"C:\", r"D:\"), (r"C:", r"D:")];

        //for c in cases {
        //    assert!(Path::new(c.1).try_relative_to(c.0).is_none());
        //}
    }

    #[test]
    #[cfg(unix)]
    fn rooted_join_test() {
        let cases = &[
            ("/usr", "lib", "/usr/lib"),
            ("/usr", "/lib", "/usr/lib"),
            ("/usr", "lib/..", "/usr"),
            ("/", "..", "/"),
        ];

        for c in cases {
            assert_eq!(Path::new(c.0).rooted_join(c.1).as_os_str(), c.2);
        }

        let cases = &[
            ("/usr", "../etc/passwd", "/usr/etc/passwd"),
            ("/usr", "/../etc/passwd", "/usr/etc/passwd"),
            ("/usr", "lib/../../etc/passwd", "/usr/etc/passwd"),
            ("/usr", "../usr-", "/usr/usr-"),
        ];

        for c in cases {
            assert_eq!(Path::new(c.0).rooted_join(c.1).as_os_str(), c.2);
        }
    }

    #[test]
    #[cfg(windows)]
    fn rooted_join_test() {
        let cases = &[
            (r"C:\Windows", "System32", r"C:\Windows\System32"),
            (r"C:\Windows", "System32", r"C:\Windows\System32"),
            (r"C:\Windows", "System32/..", r"C:\Windows"),
            (r"C:\", "..", r"C:\"),
        ];

        for c in cases {
            assert_eq!(Path::new(c.0).rooted_join(c.1).as_os_str(), c.2);
        }

        let cases = &[
            (r"C:\Windows", r"..\System32", r"C:\Windows\System32"),
            (r"C:\Windows", r"\..\System32", r"C:\Windows\System32"),
            (
                r"C:\Windows",
                r"System\..\..\System32",
                r"C:\Windows\System32",
            ),
            (r"C:\Windows", r"..\Windows-", r"C:\Windows\Windows-"),
        ];

        for c in cases {
            assert_eq!(Path::new(c.0).rooted_join(c.1).as_os_str(), c.2);
        }
    }

    #[test]
    #[cfg(unix)]
    fn try_rooted_join_test() {
        let cases = &[
            ("/usr", "lib", "/usr/lib"),
            ("/usr", "/lib", "/usr/lib"),
            ("/usr", "lib/..", "/usr"),
            ("/", "..", "/"),
        ];

        for c in cases {
            let path = Path::new(c.0).try_rooted_join(c.1);
            assert!(path.is_ok());
            assert_eq!(path.unwrap().as_os_str(), c.2);
        }

        let cases = &[
            ("/usr", "../etc/passwd"),        // /etc/passwd
            ("/usr", "/../etc/passwd"),       // /etc/passwd
            ("/usr", "lib/../../etc/passwd"), // /etc/passwd
            ("/usr", "../usr-"),              // /usr-
        ];

        for c in cases {
            assert!(Path::new(c.0).try_rooted_join(c.1).is_err());
        }
    }

    #[test]
    #[cfg(windows)]
    fn try_rooted_join_test() {
        let cases = &[
            (r"C:\Windows", "System32", r"C:\Windows\System32"),
            (r"C:\Windows", "System32", r"C:\Windows\System32"),
            (r"C:\Windows", "System32/..", r"C:\Windows"),
            (r"C:\", "..", r"C:\"),
        ];

        for c in cases {
            let path = Path::new(c.0).try_rooted_join(c.1);
            assert!(path.is_ok());
            assert_eq!(path.unwrap().as_os_str(), c.2);
        }

        let cases = &[
            (r"C:\Windows", r"..\System32", r"C:\Windows\System32"),
            (r"C:\Windows", r"\..\System32", r"C:\Windows\System32"),
            (
                r"C:\Windows",
                r"System\..\..\System32",
                r"C:\Windows\System32",
            ),
            (r"C:\Windows", r"..\Windows-", r"C:\Windows\Windows-"),
        ];

        for c in cases {
            assert!(Path::new(c.0).try_rooted_join(c.1).is_err());
        }
    }
}
