# Normalized Unix Paths

[![Build Status](https://travis-ci.org/gdzx/npath.svg?branch=master)](https://travis-ci.org/gdzx/npath)

Part of this API is the subject of an issue in the CLI working group:
[Cross-platform File System Abstractions] and a pre-RFC: [Additional Path
Handling Utilities].

[Cross-platform File System Abstractions]: https://github.com/rust-lang-nursery/cli-wg/issues/10#issuecomment-407809608
[Additional Path Handling Utilities]: https://internals.rust-lang.org/t/pre-rfc-additional-path-handling-utilities/8405

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
npath = { git = "https://github.com/gdzx/npath" }
```

For `Path` and `PathBuf` extension methods, import the following traits:

```rust
use npath::{NormPathExt, NormPathBufExt};
```

## Acknowledgement

Algorithms are straight ports from Go's [`path/filepath`] standard library
(with slight fix to [`filepath.Dir`] for proper POSIX compatiblity with
[`dirname(3)`], and without Windows path support).

Normalization routines use Rob Pike's [Lexical File Names in Plan 9 or Getting
Dot-Dot Right] algorithm.

[`dirname(3)`]: http://man7.org/linux/man-pages/man3/dirname.3.html

[`path/filepath`]: https://golang.org/pkg/path/filepath/
[`filepath.Dir`]: https://golang.org/pkg/path/filepath/#Dir

[Lexical File Names in Plan 9 or Getting Dot-Dot Right]: https://9p.io/sys/doc/lexnames.html

## License

This project is licensed under the MIT license ([LICENSE](LICENSE) or
http://opensource.org/licenses/MIT).
