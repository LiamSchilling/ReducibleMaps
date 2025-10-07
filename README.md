# Reducible Maps

This library aims to provide more computable representations of the `Finsupp`, `Multiset`, `Finset`, `MvPolynomial`, and `Polynomial` types in Mathlib by implementing a type of lightweight, kernel-reducible ordered maps. Our framework can even automate proof of symbolic goals, manipulating expressions with free variables and applying external hypotheses.

This project is the next iteration of [Automate Polynomial](https://github.com/LiamSchilling/AutomatePolynomial).

## Organization of the repository

- `Main.lean`: demonstrates the proof-automation capabilities of the library.
- `Test.lean`: contains unit tests of the proof-automation capabilities of the library.
- `ReducibleMaps\Init`: registers the custom simp sets intended to automate proofs
- `ReducibleMaps\BinTree`: defines the type of binary trees
- `ReducibleMaps\Simp`: adds basic lemmas such as lemmas for propositional logic and inequalities to the custom simp sets
