#![feature(const_str_from_utf8_unchecked)]
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
//! ```rust
//! use npath::{NormPathExt, NormPathBufExt};
//! ```

use std::env;
use std::ffi::{OsStr, OsString};
use std::io::{Error, ErrorKind, Result};
use std::path::{is_separator, Component, Path, PathBuf, Prefix, PrefixComponent, MAIN_SEPARATOR};

const MAIN_SEPARATOR_STR: &str = unsafe { std::str::from_utf8_unchecked(&[MAIN_SEPARATOR as u8]) };

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

        if !(base.is_empty()
            || is_separator(*base.last().unwrap() as char)
            || (prefix_is_disk && Some(base.len()) == prefix_len))
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
    /// - [`NormPathExt::normalized`] returns `/a/c`.
    ///
    /// # Example
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

    /// Returns the normalized equivalent of `self` with intermediate symlinks resolved.
    ///
    /// The longest prefix of `self` such that each component exist on the filesystem is
    /// canonicalized, the remaining path is appended, and the result is normalized.
    ///
    /// # Limitations
    ///
    /// The prefix considered for canonicalization ends at the first component of `self` that does
    /// not exist. The only exception is if the whole path exists, then it is canonicalized.
    ///
    /// For example, assuming only `/usr` and `/usr/lib` exist, `/usr/liz/../lib/rust` refers to
    /// `/usr/lib/rust`, but only `/usr` is canonicalized since neither `/usr/lib/rust` nor
    /// `/usr/liz` exist.
    ///
    /// [`NormPathExt::normalized`] limitations also apply in most cases. Use [`Path::canonicalize`]
    /// if you need to get the true canonical path.
    ///
    /// # Differences with [`Path::canonicalize`]
    ///
    /// - This method works for path do not exist on the filesystem.
    /// - The path is normalized with the same limitations as [`NormPathExt::normalized`]. In
    ///   particular, the suffix that does not exist might contain ".." components that can replace
    ///   canonicalized components.
    /// - If `self` is relative and no prefix can be canonicalized (does not exist in the CWD),
    ///   then the result is relative.
    ///
    /// # Differences with [`NormPathExt::normalized`]
    ///
    /// - This method does not perform pure lexical processing, and returns a [`std::io::Result`].
    /// - The prefix that is canonicalized has its intermediate symlinks resolved, without the
    ///   limitations of [`NormPathExt::normalized`].
    ///
    /// # Example
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
    /// [`NormPathExt::normalized`].
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
        let mut p = self.to_path_buf();
        p.lexical_push(path);
        p
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
                (None, None) => return Some(PathBuf::from(".")),
                _ => {
                    let mut p = PathBuf::new();

                    if let Some(Component::ParentDir) = base_head {
                        return None;
                    }

                    if base_head.is_some() && base_head != Some(Component::CurDir) {
                        p.push("..");
                    }

                    for _ in base_components {
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
        let base = base.as_ref().absolute()?.normalized();
        let path = self.absolute()?.normalized();

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

                    for _ in base_components {
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

    fn rooted_join2<P: AsRef<Path>>(&self, path: P) -> PathBuf {
        let path = path.as_ref();

        // Ensure path is absolute so normalization can eliminate all ".." components
        let path = if path.is_relative() {
            Path::new("/").join(path).normalized()
        } else {
            path.normalized()
        };

        self.lexical_join(path)
    }

    // <https://github.com/django/django/blob/master/django/utils/_os.py>
    fn try_rooted_join<P: AsRef<Path>>(&self, path: P) -> Result<PathBuf> {
        // Make absolute and normalize all paths
        let base = self.absolute()?.normalized();
        let path = self.lexical_join(path).absolute()?.normalized();

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
    a == b
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

    macro_rules! base {
        ($a:literal) => {
            Path::new($a).base().as_os_str()
        };
    }

    #[test]
    #[cfg(unix)]
    fn base_name_test() {
        assert_eq!(base!(""), ".");
        assert_eq!(base!("."), ".");
        assert_eq!(base!("/."), "/"); // POSIX: "."
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
    fn base_name_test() {
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
    fn dir_name_test() {
        assert_eq!(dir!(""), ".");
        assert_eq!(dir!("."), ".");
        assert_eq!(dir!(".."), ".");
        assert_eq!(dir!("/."), "/");
        assert_eq!(dir!("/"), "/");
        assert_eq!(dir!("////"), "/");
        assert_eq!(dir!("/foo"), "/");
        assert_eq!(dir!("x/"), "."); // Go's `filepath.Dir` returns "x"
        assert_eq!(dir!("x///"), "."); // Go's `filepath.Dir` returns "x"
        assert_eq!(dir!("abc"), ".");
        assert_eq!(dir!("abc/def"), "abc");
        assert_eq!(dir!("a/b/.x"), "a/b");
        assert_eq!(dir!("a/b/c."), "a/b");
        assert_eq!(dir!("a/b/c.x"), "a/b");

        // Unnormalized
        assert_eq!(dir!("/../x"), "/..");
    }

    #[test]
    #[cfg(windows)]
    fn dir_name_test() {
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

    macro_rules! is_inside {
        ($a:literal, $b:literal) => {
            Path::new($a).is_inside($b)
        };
    }

    // TODO: Windows
    #[test]
    #[cfg(unix)]
    fn is_inside_test() {
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
    fn normalized_test() {
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
    fn normalized_test() {
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
                    p.lexical_push($a);
                )*

                p
            }.as_os_str()
        };
    }

    #[test]
    #[cfg(unix)]
    fn lexical_join_test() {
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
    fn lexical_join_test() {
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
    fn relative_to_test() {
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
    fn relative_to_test() {
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

    macro_rules! try_relative {
        ($a:literal, $b:literal) => {
            Path::new($b)
                .try_relative_to($a)
                .map(|p| p.into_os_string())
        };
    }

    #[test]
    #[cfg(unix)]
    fn try_relative_to_test() {
        use std::env;

        assert_eq_ok!(try_relative!("a/b", "a/b"), ".");
        assert_eq_ok!(try_relative!("a/b/.", "a/b"), ".");
        assert_eq_ok!(try_relative!("a/b", "a/b/."), ".");
        assert_eq_ok!(try_relative!("./a/b", "a/b"), ".");
        assert_eq_ok!(try_relative!("a/b", "./a/b"), ".");
        assert_eq_ok!(try_relative!("ab/cd", "ab/cde"), "../cde");
        assert_eq_ok!(try_relative!("ab/cd", "ab/c"), "../c");
        assert_eq_ok!(try_relative!("a/b", "a/b/c/d"), "c/d");
        assert_eq_ok!(try_relative!("a/b", "a/b/../c"), "../c");
        assert_eq_ok!(try_relative!("a/b/../c", "a/b"), "../b");
        assert_eq_ok!(try_relative!("a/b/c", "a/c/d"), "../../c/d");
        assert_eq_ok!(try_relative!("a/b", "c/d"), "../../c/d");
        assert_eq_ok!(try_relative!("a/b/c/d", "a/b"), "../..");
        assert_eq_ok!(try_relative!("a/b/c/d", "a/b/"), "../..");
        assert_eq_ok!(try_relative!("a/b/c/d/", "a/b"), "../..");
        assert_eq_ok!(try_relative!("a/b/c/d/", "a/b/"), "../..");
        assert_eq_ok!(try_relative!("../../a/b", "../../a/b/c/d"), "c/d");
        assert_eq_ok!(try_relative!("/a/b", "/a/b"), ".");
        assert_eq_ok!(try_relative!("/a/b/.", "/a/b"), ".");
        assert_eq_ok!(try_relative!("/a/b", "/a/b/."), ".");
        assert_eq_ok!(try_relative!("/ab/cd", "/ab/cde"), "../cde");
        assert_eq_ok!(try_relative!("/ab/cd", "/ab/c"), "../c");
        assert_eq_ok!(try_relative!("/a/b", "/a/b/c/d"), "c/d");
        assert_eq_ok!(try_relative!("/a/b", "/a/b/../c"), "../c");
        assert_eq_ok!(try_relative!("/a/b/../c", "/a/b"), "../b");
        assert_eq_ok!(try_relative!("/a/b/c", "/a/c/d"), "../../c/d");
        assert_eq_ok!(try_relative!("/a/b", "/c/d"), "../../c/d");
        assert_eq_ok!(try_relative!("/a/b/c/d", "/a/b"), "../..");
        assert_eq_ok!(try_relative!("/a/b/c/d", "/a/b/"), "../..");
        assert_eq_ok!(try_relative!("/a/b/c/d/", "/a/b"), "../..");
        assert_eq_ok!(try_relative!("/a/b/c/d/", "/a/b/"), "../..");
        assert_eq_ok!(try_relative!("/../../a/b", "/../../a/b/c/d"), "c/d");
        assert_eq_ok!(try_relative!(".", "a/b"), "a/b");
        assert_eq_ok!(try_relative!(".", ".."), "..");

        // The result depends on the current directory
        if let Ok(c) = env::current_dir() {
            let mut root = std::path::PathBuf::new();

            for _ in 0..c.components().count() {
                root.push("..");
            }

            assert_eq_ok!(try_relative!("..", "."), c.base().to_path_buf());
            assert_eq_ok!(try_relative!("..", "a"), c.base().join("a"));
            assert_eq_ok!(try_relative!("../..", ".."), c.dir().base().to_path_buf());
            assert_eq_ok!(try_relative!("a", "/a"), root.join("a"));
            assert_eq_ok!(
                try_relative!("/a", "a"),
                Path::new("..").lexical_join(c).join("a")
            );
        }
    }

    #[test]
    #[cfg(windows)]
    fn try_relative_to_test() {
        assert_eq_ok!(try_relative!(r"C:a\b\c", r"C:a/b/d"), r"..\d");
        assert_eq_ok!(try_relative!(r"C:\Projects", r"c:\projects\src"), r"src");
        assert_eq_ok!(try_relative!(r"C:\Projects", r"c:\projects"), r".");
        assert_eq_ok!(try_relative!(r"C:\Projects\a\..", r"c:\projects"), r".");

        // TODO: there are some cases where there is no relative paths. Need to change the return
        // type of try_relative_to.
        //let cases = &[(r"C:\", r"D:\"), (r"C:", r"D:")];

        //for c in cases {
        //    assert!(Path::new(c.1).try_relative_to(c.0).is_none());
        //}
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
    fn rooted_join_test() {
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
    fn rooted_join_test() {
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
    fn try_rooted_join_test() {
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
    fn try_rooted_join_test() {
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
