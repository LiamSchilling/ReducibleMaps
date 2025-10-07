# Reducible Maps

This library aims to provide computable representations of the `Finsupp`, `Multiset`, `Finset`, `MvPolynomial`, and `Polynomial` types in Mathlib by implementing a type of lightweight, kernel-reducible ordered maps. Our framework can even automate proof of symbolic goals, manipulating expressions with free variables and applying external hypotheses.

This project is the next iteration of [Automate Polynomial](https://github.com/LiamSchilling/AutomatePolynomial).

## Useful links

- Documentation pages: [here](https://liamschilling.github.io/ReducibleMaps/docs/)
- Discussion of automation tactics and kernel-reducibility: [ReducibleMaps\Basic.lean](https://liamschilling.github.io/ReducibleMaps/docs/ReducibleMaps/Basic.html)

## Organization of the repository

- [`Main.lean`](https://github.com/LiamSchilling/ReducibleMaps/blob/master/Main.lean): demonstrates the proof-automation capabilities of the library.
- [`Test.lean`](https://github.com/LiamSchilling/ReducibleMaps/blob/master/Test.lean): contains unit tests of the proof-automation capabilities of the library.
- [`ReducibleMaps\Init.lean`](https://liamschilling.github.io/ReducibleMaps/docs/ReducibleMaps/Init.html): registers the custom simp sets for `simp` proof automation
- [`ReducibleMaps\BinTree.lean`](https://liamschilling.github.io/ReducibleMaps/docs/ReducibleMaps/BinTree.html): defines the type of binary trees
- [`ReducibleMaps\Simp.lean`](https://liamschilling.github.io/ReducibleMaps/docs/ReducibleMaps/Simp.html): adds basic lemmas to the custom simp sets such as lemmas for propositional logic and inequalities
