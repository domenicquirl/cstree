<div align=center>
  <h1><code>cstree</code></h1>
  <p>
    <strong>A library for generic lossless syntax trees</strong>
  </p>

  <p>
    <a href="https://github.com/domenicquirl/cstree/actions?query=workflow%3ACI"> <img src="https://github.com/domenicquirl/cstree/workflows/CI/badge.svg" alt="build status" /></a>
  </p>
</div>

`cstree` is a library for creating and working with concrete syntax trees (CSTs).
The concept of CSTs is inspired in part by Swift's [libsyntax](https://github.com/apple/swift/tree/5e2c815edfd758f9b1309ce07bfc01c4bc20ec23/lib/Syntax).

The `cstree` implementation is a fork of the excellent [`rowan`](https://github.com/rust-analyzer/rowan/), developed by the authors of [rust-analyzer](https://github.com/rust-analyzer/rust-analyzer/).
While we are building our own documentation, a conceptual overview of their implementation is available in the [rust-analyzer repo](https://github.com/rust-analyzer/rust-analyzer/blob/master/docs/dev/syntax.md#trees).

Notable differences of `cstree` compared to `rowan`:
  - Syntax trees (red trees) are created lazily, but are persistent. Once a node has been created, it will remain allocated, while `rowan` re-creates the red layer on the fly. Apart from the trade-off discussed [here](https://github.com/rust-analyzer/rust-analyzer/blob/master/docs/dev/syntax.md#memoized-rednodes), this helps to achieve good tree traversal speed while providing the next points:
  - Syntax (red) nodes are `Send` and `Sync`, allowing to share realized trees across threads. This is achieved by atomically reference counting syntax trees as a whole, which also gets rid of the need to reference count individual nodes (helping with the point above).
  - Syntax nodes can hold custom data.
  - `cstree` trees are trees over interned strings. This means `cstree` will deduplicate the text of tokens such as identifiers with the same name. In this position, `rowan` stores each string, with a small string optimization (see [`SmolStr`](https://crates.io/crates/smol_str)).
  - Performance optimizations for tree creation: only allocate new nodes on the heap if they are not in cache, avoid recursively hashing subtrees

See `examples/s_expressions` for a tutorial.
## License

`cstree` is primarily distributed under the terms of both the MIT license and the Apache License (Version 2.0).

See `LICENSE-APACHE` and `LICENSE-MIT` for details.
