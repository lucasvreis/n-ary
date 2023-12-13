# `n-ary-labeled`

This library defines a small class hierarchy of n-ary (covariant) functors,
foldables and traversables (generalizing Bifunctors, Bifoldables and
Bitraversables). It also supports "labelling" the type arguments so that it's a
bit easier to write maps that apply to many types at once. It uses the
[kind-apply](https://hackage.haskell.org/package/kind-apply) and
[kind-generics](https://hackage.haskell.org/package/kind-generics) packages for
automatically deriving instances for the classes.

You can find some example usage in the [test file](test/Main.hs).
