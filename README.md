# Normalized Paths

[Documentation](https://gdzx.github.io/npath/npath/)

`npath` is a Rust library providing methods for cross-platform lexical path
processing and normalization. These methods are implemented in extension traits
to `Path` and `PathBuf`.

## Usage

Add `npath` to your `Cargo.toml`:

```toml
[dependencies]
npath = { git = "https://github.com/gdzx/npath" }
```

Import the following traits:

```rust
use npath::{NormPathExt, NormPathBufExt};
```

## License

This project is licensed under the MIT license ([LICENSE](LICENSE) or
http://opensource.org/licenses/MIT).
