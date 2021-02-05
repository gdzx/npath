use std::env;
use std::path::{Path, PathBuf};

use npath::NormPathExt;

fn rooted_join(base: &Path, path: &Path) -> PathBuf {
    // Ensure path starts with / so normalization can eliminate all ".." components
    let path = if path.is_relative() {
        Path::new("/").join(path).normalized()
    } else {
        path.normalized()
    };

    base.lexical_join(path)
}

fn main() {
    let args: Vec<_> = env::args().collect();

    if args.len() < 3 {
        eprintln!("Usage: rooted_join PATH PATH");
        std::process::exit(1);
    }

    println!(
        "{}",
        rooted_join(Path::new(&args[1]), Path::new(&args[2])).display()
    );
}
