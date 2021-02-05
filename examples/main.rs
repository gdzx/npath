use std::env;
use std::ffi::{OsStr, OsString};
use std::fmt;
use std::io::{self, BufRead};
use std::path::{Path, PathBuf};

use npath::NormPathExt;

enum Answer {
    Bool(bool),
    OsString(OsString),
    PathBuf(PathBuf),
    String(String),
}

fn absolute(s: &str) -> Answer {
    Path::new(s).absolute().unwrap().normalized().into()
}

fn basename(s: &str) -> Answer {
    Path::new(s).base().into()
}

fn dirname(s: &str) -> Answer {
    Path::new(s).dir().normalized().into()
}

fn extension(s: &str) -> Answer {
    if let Some(e) = Path::new(s).extension() {
        e.into()
    } else {
        "None".into()
    }
}

fn is_absolute(s: &str) -> Answer {
    Path::new(s).is_absolute().into()
}

fn join(s: &str) -> Answer {
    let v: Vec<_> = s.splitn(2, " ").collect();
    Path::new(v[0]).join(v[1]).into()
}

fn lexical_join(s: &str) -> Answer {
    let v: Vec<_> = s.splitn(2, " ").collect();
    Path::new(v[0]).lexical_join(v[1]).normalized().into()
}

fn normalize(s: &str) -> Answer {
    Path::new(s).normalized().into()
}

fn relative_to(s: &str) -> Answer {
    let v: Vec<_> = s.splitn(2, " ").collect();
    match Path::new(v[1]).relative_to(v[0]) {
        Some(p) => p.into(),
        None => "None".into(),
    }
}

fn main() {
    let args = env::args();

    if args.len() < 1 {
        eprintln!("Missing argument");
        std::process::exit(2);
    }

    let f: fn(&str) -> Answer = match env::args().nth(1).unwrap().as_ref() {
        "absolute" => absolute,
        "basename" => basename,
        "dirname" => dirname,
        "extension" => extension,
        "is_absolute" => is_absolute,
        "join" => join,
        "lexical_join" => lexical_join,
        "normalize" => normalize,
        "relative_to" => relative_to,
        _ => {
            eprintln!("Unsupported");
            std::process::exit(1);
        }
    };

    for line in io::stdin().lock().lines() {
        println!("{}", f(line.unwrap().as_ref()));
    }
}

impl From<bool> for Answer {
    fn from(b: bool) -> Self {
        Self::Bool(b)
    }
}

impl From<String> for Answer {
    fn from(s: String) -> Self {
        Self::String(s)
    }
}

impl From<&str> for Answer {
    fn from(s: &str) -> Self {
        s.to_string().into()
    }
}

impl From<OsString> for Answer {
    fn from(s: OsString) -> Self {
        Self::OsString(s)
    }
}

impl From<&OsStr> for Answer {
    fn from(s: &OsStr) -> Self {
        s.to_os_string().into()
    }
}

impl From<PathBuf> for Answer {
    fn from(p: PathBuf) -> Answer {
        Answer::PathBuf(p)
    }
}

impl From<&Path> for Answer {
    fn from(p: &Path) -> Answer {
        p.to_path_buf().into()
    }
}

impl fmt::Display for Answer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool(b) => write!(f, "{}", b),
            Self::OsString(s) => write!(f, "{}", s.to_str().unwrap()),
            Self::PathBuf(p) => write!(f, "{}", p.display()),
            Self::String(s) => write!(f, "{}", s),
        }
    }
}
