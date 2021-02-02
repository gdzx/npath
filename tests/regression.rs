use std::path::Path;

use npath::NormPathExt;
use npath_prev::NormPathExt as NormPathPrevExt;

const LENGTH: usize = 10;
const CHARS: &[char] = &['/', '.', 'a'];

macro_rules! assert_eq_option {
    ($left:expr, $right:expr) => {
        assert_eq!($left.is_some(), $right.is_some());
        if $left.is_some() {
            assert_eq!($left.unwrap(), $right.unwrap());
        }
    };
}

macro_rules! assert_eq_result {
    ($left:expr, $right:expr) => {
        assert_eq!($left.is_ok(), $right.is_ok());
        if $left.is_ok() {
            assert_eq!($left.unwrap(), $right.unwrap());
        }
    };
}

#[test]
fn test_absolute() {
    for a in AllStrings::new(LENGTH, CHARS) {
        assert_eq_result!(
            NormPathExt::absolute(Path::new(&a)),
            NormPathPrevExt::absolute(Path::new(&a))
        );
    }
}

#[test]
fn test_base() {
    for a in AllStrings::new(LENGTH, CHARS) {
        assert_eq!(
            NormPathExt::base(Path::new(&a)),
            NormPathPrevExt::base(Path::new(&a))
        );
    }
}

#[test]
fn test_dir() {
    for a in AllStrings::new(LENGTH, CHARS) {
        assert_eq!(
            NormPathExt::dir(Path::new(&a)),
            NormPathPrevExt::dir(Path::new(&a))
        );
    }
}

#[test]
fn test_is_inside() {
    for a in AllStrings::new(LENGTH / 2, CHARS) {
        for b in AllStrings::new(LENGTH / 2, CHARS) {
            assert_eq!(
                NormPathExt::is_inside(Path::new(&a), &b),
                NormPathPrevExt::is_inside(Path::new(&a), &b)
            );
        }
    }
}

#[test]
fn test_normalized() {
    for a in AllStrings::new(LENGTH, CHARS) {
        assert_eq!(
            NormPathExt::normalized(Path::new(&a)),
            NormPathPrevExt::normalized(Path::new(&a))
        );
    }
}

#[test]
fn test_lexical_join() {
    for a in AllStrings::new(LENGTH / 2, CHARS) {
        for b in AllStrings::new(LENGTH / 2, CHARS) {
            assert_eq!(
                NormPathExt::lexical_join(Path::new(&a), &b),
                NormPathPrevExt::lexical_join(Path::new(&a), &b)
            );
        }
    }
}

#[test]
fn test_relative_to() {
    for a in AllStrings::new(LENGTH / 2, CHARS) {
        for b in AllStrings::new(LENGTH / 2, CHARS) {
            assert_eq_option!(
                NormPathExt::relative_to(Path::new(&a), &b),
                NormPathPrevExt::relative_to(Path::new(&a), &b)
            );
        }
    }
}

#[test]
fn test_try_relative_to() {
    for a in AllStrings::new(LENGTH / 2, CHARS) {
        for b in AllStrings::new(LENGTH / 2, CHARS) {
            assert_eq_result!(
                NormPathExt::try_relative_to(Path::new(&a), &b),
                NormPathPrevExt::try_relative_to(Path::new(&a), &b)
            );
        }
    }
}

#[test]
fn test_resolved() {
    for a in AllStrings::new(LENGTH, CHARS) {
        assert_eq_result!(
            NormPathExt::resolved(Path::new(&a)),
            NormPathPrevExt::resolved(Path::new(&a))
        );
    }
}

#[test]
fn test_rooted_join() {
    for a in AllStrings::new(LENGTH / 2, CHARS) {
        for b in AllStrings::new(LENGTH / 2, CHARS) {
            assert_eq!(
                NormPathExt::rooted_join(Path::new(&a), &b),
                NormPathPrevExt::rooted_join(Path::new(&a), &b)
            );
        }
    }
}

#[test]
fn test_rooted_join2() {
    for a in AllStrings::new(LENGTH / 2, CHARS) {
        for b in AllStrings::new(LENGTH / 2, CHARS) {
            assert_eq!(
                NormPathExt::rooted_join2(Path::new(&a), &b),
                NormPathPrevExt::rooted_join2(Path::new(&a), &b)
            );
        }
    }
}

#[test]
fn test_try_rooted_join() {
    for a in AllStrings::new(LENGTH / 2, CHARS) {
        for b in AllStrings::new(LENGTH / 2, CHARS) {
            assert_eq_result!(
                NormPathExt::try_rooted_join(Path::new(&a), &b),
                NormPathPrevExt::try_rooted_join(Path::new(&a), &b)
            );
        }
    }
}

struct AllStrings<'a> {
    len: usize,
    chars: &'a [char],
    stack: Vec<usize>,
    string: String,
    return_empty: bool,
}

impl<'a> AllStrings<'a> {
    fn new(len: usize, chars: &'a [char]) -> Self {
        AllStrings {
            len,
            chars,
            stack: vec![],
            string: String::new(),
            return_empty: true,
        }
    }
}

impl<'a> Iterator for AllStrings<'a> {
    type Item = String;

    fn next(&mut self) -> Option<String> {
        if self.return_empty {
            self.return_empty = false;
            return Some(String::new());
        }

        while self.stack.len() < self.len {
            self.stack.push(0);
            self.string.push(self.chars[0]);
            return Some(self.string.clone());
        }

        while !self.stack.is_empty() && *self.stack.last().unwrap() == self.chars.len() - 1 {
            self.stack.pop();
            self.string.pop();
        }

        if self.stack.is_empty() {
            return None;
        }

        *self.stack.last_mut().unwrap() += 1;
        self.string.pop();
        self.string.push(self.chars[*self.stack.last().unwrap()]);

        Some(self.string.clone())
    }
}
