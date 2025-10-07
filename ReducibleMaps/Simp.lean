import ReducibleMaps.Init
import Mathlib.Order.WithBot

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
