import ReducibleMaps.BinTree
import ReducibleMaps.Simp

/-!
# Reducible Maps

This library implements a type of lightweight, kernel-reducible ordered maps. By kernel-reducible,
we mean that tactics like `decide` and especially `simp` can effectively reason about statements
containing ordered maps. Below is an explanation of what that means for each tactic.

## `decide`

The `decide` tactic infers an instance of `Decidable` for the statement, which provides an
executable program for deciding its truth. This approach is generally faster than `simp` although
it is limited in that it requires the statement to be explicit, containing no free variables and
requiring no external hypotheses.

When the statement is in fact false, `decide` will fail and conveniently display "Tactic `decide`
proved that the proposition `...` is false".

## `simp`

The `simp` tactic constructs a proof of the statement by repeatedly applying some provided lemmas.
Each application takes the form of a rewrite step called a reduction, where the rewritten statement
is ideally simpler than the original statement. For a discussion of what "simpler" means, see
[simp normal forms]
(https://lean-lang.org/doc/reference/4.20.0//The-Simplifier/Simp-Normal-Forms/#simp-normal-forms).
We provide the necessary lemmas for reducing statements about relevant structures using a custom
[simp set](ReducibleMaps/Init.html) for each structure.

When provided the appropriate lemmas, this approach is much more general than `decide` since it can
reduce statements containing free variables and even process additional hypotheses. For instance,
`simp` can show that a binary tree with with an explicit structure is ordered given the necessary
comparison hypotheses between its elements, even when those elements are not explicit themselves.

When the statement is in fact false, `simp` will conveniently reduce the statement to `False`.

## Useful links

The Lean Language Reference for `simp`:
[here](https://lean-lang.org/doc/reference/4.20.0//The-Simplifier/#the-simplifier)
-/
