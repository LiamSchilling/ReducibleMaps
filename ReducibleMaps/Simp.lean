import ReducibleMaps.Init
import Mathlib.Order.WithBot

/-!
# Custom Simp Sets

This file adds basic lemmas to the custom simp sets for `simp` proof automation. Lemmas about
propositional logic and inequalities are commonly necessary for instance.

For further discussion of simp sets, see [ReducibleMaps/Init.lean](ReducibleMaps/Init.html).

## Useful links

The Lean Language Reference for `simp`:
[here](https://lean-lang.org/doc/reference/4.20.0//The-Simplifier/#the-simplifier)

The Lean Language Reference for simp sets:
[here](https://lean-lang.org/doc/reference/latest/The-Simplifier/Simp-sets/)
-/

attribute [
    simp_edgeLt, simp_pathLt, simp_pathMem, simp_elemMem, simp_contains,
    simp_infThenSupThenOrdered, simp_ordered,
    simp_keyValueLt]
  not_false_eq_true

attribute [
    simp_pathMem, simp_contains,
    simp_infThenSupThenOrdered, simp_ordered]
  Bool.false_eq_true

attribute [
    simp_elemMem, simp_contains]
  or_true true_or or_false false_or

attribute [
    simp_inf, simp_infThenSupThenOrdered, simp_ordered]
  le_top inf_of_le_left inf_of_le_right

attribute [
    simp_sup, simp_infThenSupThenOrdered, simp_ordered]
  bot_le sup_of_le_left sup_of_le_right

attribute [
    simp_infThenSupThenOrdered, simp_ordered]
  decide_true decide_false
  Bool.and_true Bool.true_and Bool.and_false Bool.false_and
  WithTop.coe_lt_top WithBot.bot_lt_coe WithTop.coe_lt_coe WithBot.coe_lt_coe

attribute [
    simp_infThenSupThenOrdered, simp_ordered,
    simp_keyValueLt]
  lt_irrefl
