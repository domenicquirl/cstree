# Changelog

## `v0.12.0`

 * Documentation has been improved in most areas, together with a switch to a more principled module structure that allows explicitly documenting submodules.
 * The `Language` trait has been deprecated in favour of a new `Syntax` trait. `Syntax` provides the same methods that `Language` did before, but is implemented directly on the syntax kind enum instead of an additional type representing the language.
   * The supertrait requirements on `PartialOrd`, `Ord`, and `Hash` have been dropped.
 * TODO: this allows to optionally provide derive. To enable, add feature flag
 * The `interning` module has been rewritten. It now provides fuctions for obtaining a default interner (`new_interner` and `new_threaded_interner`) and provides a small, dependency-free interner implementation.
   * Compatibility with other interners can be enable via feature flags. 
   * **Note** that compatibilty with `lasso` is not enabled by default. Use the `lasso_compat` feature to match the previous default.
 * Introduced `Syntax::static_text` to optimize tokens that always appear with the same text (estimated 10-15% faster tree building when used, depending on the ratio of static to dynamic tokens).
   * Since `cstree`s are lossless, `GreenNodeBuilder::token` must still be passed the source text even for static tokens. 
 * Internal performance improvements for up to 10% faster tree building by avoiding unnecessary duplication of elements.
 * Use `NonNull` for the internal representation of `SyntaxNode`, meaning it now benefits from niche optimizations (`Option<SyntaxNode>` is now the same size as `SyntaxNode` itself: the size of a pointer).
 * `SyntaxKind` has been renamed to `RawSyntaxKind` to no longer conflict with user-defined `SyntaxKind` enumerations.
   * `RawSyntaxKind` has been changed to use a 32-bit index internally, which means existing `Language` implementations and syntax kind `enum`s need to be adjusted to `#[repr(u32)]` and the corresponding conversions.
 * The crate's export module structure has been reorganized to give different groups of definitions their own submodules. A `cstree::prelude` module is available, containing the most commonly needed types that were previously accessible via `use cstree::*`. Otherwise, the module structure is now as follows:
   * `cstree`
     * `Syntax`
     * `RawSyntaxKind`
     * `build`
       * `GreenNodeBuilder`
       * `NodeCache`
       * `Checkpoint`
     * `green`
       * `GreenNode`
       * `GreenToken`
       * `GreenNodeChildren`
     * `syntax`
       * `{Syntax,Resolved}Node`
       * `{Syntax,Resolved}Token`
       * `{Syntax,Resolved}Element`
       * `{Syntax,Resolved}ElementRef`
       * `SyntaxNodeChildren`
       * `SyntaxElementChildren`
       * `SyntaxText`
     * `interning`
       * `TokenKey` and the `InternKey` trait
       * `Interner` and `Resolver` traits
       * `new_interner` and `TokenInterner`
       * `new_threaded_interner` and `MultiThreadedTokenInterner` (with the `multi_threaded_interning` feature enabled)
       * compatibility implementations for interning crates depending on selected feature flags
     * `text`
       * `TextSize`
       * `TextRange`
       * `SyntaxText` (re-export)
     * `traversal`
       * `Direction`
       * `WalkEvent`
     * `util`
       * `NodeOrToken`
       * `TokenAtOffset`
     * `sync`
       * `Arc`
     * `prelude`
       * re-exports of the most-used items