# Reducible Maps

This library aims to provide computable representations of the `Finsupp`, `Multiset`, `Finset`, `MvPolynomial`, and `Polynomial` types in Mathlib by implementing a type of lightweight, kernel-reducible ordered maps. Our framework can even automate proof of symbolic goals, manipulating expressions with free variables and applying external hypotheses.

This project is the next iteration of [Automate Polynomial](https://github.com/LiamSchilling/AutomatePolynomial).

### Useful links

- Documentation pages: [here](https://liamschilling.github.io/ReducibleMaps/docs/)
- Discussion of automation tactics and kernel-reducibility: [ReducibleMaps\Basic.lean](https://liamschilling.github.io/ReducibleMaps/docs/ReducibleMaps/Basic.html)

## Installation

### To use as a dependency

Add the following to your project's `lakefile.toml`:

```
[[require]]
name = "ReducibleMaps"
git = "https://github.com/LiamSchilling/ReducibleMaps"
```

Or the following to your project's `lakefile.lean`:

```
require ReducibleMaps from git
  "https://github.com/LiamSchilling/ReducibleMaps" @ "master"
```

### To build locally

Navigate to an empty project directory and run:

```
git clone "https://github.com/LiamSchilling/ReducibleMaps"
```

To build the project with all tests:

```
lake build
```

Alternatively, navigate to `Test.lean` and `Main.lean` to inspect the tests and demonstrations directly.

## Main definitions

- `OrdCFinsupp`: a representation of `Finsupp`, implemented as an ordered map.
- `OrdCMultiset`: a representation of `Multiset`, implemented as a map from domain members to their multiplicity.
- `OrdCFinset`: a representation of `Finset`, implemented as a multiset with a no-duplicates invariant.
- `OrdCMvPolynomial`: a representation of `MvPolynomial`, implemented as a map from monomials to their coefficients.
- `OrdCPolynomial`: a representation of `Polynomial`, implemented as a multivariate polynomial with one variable.

## Organization of the repository

### Current

- [`Main.lean`](https://github.com/LiamSchilling/ReducibleMaps/blob/master/Main.lean): demonstrates the proof-automation capabilities of the library.
- [`Test.lean`](https://github.com/LiamSchilling/ReducibleMaps/blob/master/Test.lean): contains unit tests of the proof-automation capabilities of the library.
- [`ReducibleMaps\Init.lean`](https://liamschilling.github.io/ReducibleMaps/docs/ReducibleMaps/Init.html): registers the custom simp sets for `simp` proof automation.
- [`ReducibleMaps\BinTree.lean`](https://liamschilling.github.io/ReducibleMaps/docs/ReducibleMaps/BinTree.html): defines the type of binary trees.
- [`ReducibleMaps\Simp.lean`](https://liamschilling.github.io/ReducibleMaps/docs/ReducibleMaps/Simp.html): adds basic lemmas to the custom simp sets for `simp` proof automation.

### Roadmap

- `ReducibleMaps\OrdTree.lean`: defines the type of ordered binary trees, otherwise known as binary search trees.
- `ReducibleMaps\OrdCFinsupp.lean`: defines `OrdCFinsupp`, a representation of `Finsupp`.
- `ReducibleMaps\OrdCMultiset.lean`: defines `OrdCMultiset`, a representation of `Multiset`.
- `ReducibleMaps\OrdCFinset.lean`: defines `OrdCFinset`, a representation of `Finset`.
- `ReducibleMaps\OrdCMvPolynomial.lean`: defines `OrdCMvPolynomial`, a representation of `MvPolynomial`.
- `ReducibleMaps\OrdCPolynomial.lean`: defines `OrdCPolynomial`, a representation of `Polynomial`.
