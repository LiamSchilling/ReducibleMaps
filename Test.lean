import ReducibleMaps

/-!
# Unit Tests for "Reducible Maps"

This file tests the proof-automation capabilities of this library. Each `section` in this file
tests the `decide` and `simp` tactics when relevant for proving statements about the named
structure.

For further discussion of these tactics, see [ReducibleMaps/Basic.lean](ReducibleMaps/Basic.html).
-/

namespace CMaps

namespace BinTree

section edgeEq

example : Edge.left = Edge.left := by decide
example : ¬Edge.left = Edge.right := by decide
example : ¬Edge.right = Edge.left := by decide
example : Edge.right = Edge.right := by decide

end edgeEq

section edgeLt

example : ¬Edge.left < Edge.left := by decide
example : Edge.left < Edge.right := by decide
example : ¬Edge.right < Edge.left := by decide
example : ¬Edge.right < Edge.right := by decide

example : ¬Edge.left < Edge.left := by simp only [simp_edgeLt]
example : Edge.left < Edge.right := by simp only [simp_edgeLt]
example : ¬Edge.right < Edge.left := by simp only [simp_edgeLt]
example : ¬Edge.right < Edge.right := by simp only [simp_edgeLt]

end edgeLt

section pathLt

example : ¬([] : Path) < ([] : Path) := by decide
example : ([Edge.left] : Path) < ([] : Path) := by decide
example : ¬([Edge.right] : Path) < ([] : Path) := by decide
example : ¬([] : Path) < ([Edge.left] : Path) := by decide
example : ([] : Path) < ([Edge.right] : Path) := by decide
example : ¬([Edge.left] : Path) < ([Edge.left] : Path) := by decide
example : ([Edge.left] : Path) < ([Edge.right] : Path) := by decide
example : ¬([Edge.right] : Path) < ([Edge.left] : Path) := by decide
example : ¬([Edge.right] : Path) < ([Edge.right] : Path) := by decide

example : ¬([] : Path) < ([] : Path) := by simp only [simp_pathLt]
example : ([Edge.left] : Path) < ([] : Path) := by simp only [simp_pathLt]
example : ¬([Edge.right] : Path) < ([] : Path) := by simp only [simp_pathLt]
example : ¬([] : Path) < ([Edge.left] : Path) := by simp only [simp_pathLt]
example : ([] : Path) < ([Edge.right] : Path) := by simp only [simp_pathLt]
example : ¬([Edge.left] : Path) < ([Edge.left] : Path) := by simp only [simp_pathLt]
example : ([Edge.left] : Path) < ([Edge.right] : Path) := by simp only [simp_pathLt]
example : ¬([Edge.right] : Path) < ([Edge.left] : Path) := by simp only [simp_pathLt]
example : ¬([Edge.right] : Path) < ([Edge.right] : Path) := by simp only [simp_pathLt]

end pathLt

section pathMem

example : ¬[] ∈ᵢ (nil : BinTree Nat) := by decide
example : ¬[Edge.left] ∈ᵢ (nil : BinTree Nat) := by decide
example : ¬[Edge.right] ∈ᵢ (nil : BinTree Nat) := by decide
example : [] ∈ᵢ single 0 := by decide
example : ¬[Edge.left] ∈ᵢ single 0 := by decide
example : ¬[Edge.right] ∈ᵢ single 0 := by decide

example : ¬[] ∈ᵢ (nil : BinTree Nat) := by simp only [simp_pathMem]
example : ¬[Edge.left] ∈ᵢ (nil : BinTree Nat) := by simp only [simp_pathMem]
example : ¬[Edge.right] ∈ᵢ (nil : BinTree Nat) := by simp only [simp_pathMem]
example : [] ∈ᵢ single 0 := by simp only [simp_pathMem]
example : ¬[Edge.left] ∈ᵢ single 0 := by simp only [simp_pathMem]
example : ¬[Edge.right] ∈ᵢ single 0 := by simp only [simp_pathMem]

end pathMem

section getElem

variable (a₁ a₂ a₃ : α) (_ : a₁ ≠ a₂) (_ : a₂ ≠ a₃) (_ : a₃ ≠ a₁)

example : (single 1)[([] : Path)] = 1 := by decide
example : (cons 1 (single 2) (single 3))[([] : Path)] = 1 := by decide
example : (cons 1 (single 2) (single 3))[[Edge.left]] = 2 := by decide
example : (cons 1 (single 2) (single 3))[[Edge.right]] = 3 := by decide

example : (single a₁)[([] : Path)] = a₁ := by simp
example : (cons a₁ (single a₂) (single a₃))[([] : Path)] = a₁ := by simp only [simp_getElem]
example : (cons a₁ (single a₂) (single a₃))[[Edge.left]] = a₂ := by simp only [simp_getElem]
example : (cons a₁ (single a₂) (single a₃))[[Edge.right]] = a₃ := by simp only [simp_getElem]

end getElem

section elemMem

variable (a₁ a₂ a₃ : α) (h₁ : a₁ ≠ a₂) (h₂ : a₂ ≠ a₃) (h₃ : a₃ ≠ a₁)

example : ¬1 ∈ nil := by decide
example : 1 ∈ single 1 := by decide
example : ¬2 ∈ single 1 := by decide
example : 1 ∈ cons 1 (single 2) (single 3) := by decide
example : 2 ∈ cons 1 (single 2) (single 3) := by decide
example : 3 ∈ cons 1 (single 2) (single 3) := by decide
example : ¬3 ∈ cons 1 (single 2) (single 2) := by decide

example : ¬a₁ ∈ nil := by simp only [simp_elemMem]
example : a₁ ∈ single a₁ := by simp only [simp_elemMem]
example : ¬a₂ ∈ single a₁ := by simp only [simp_elemMem, h₁.symm]
example : a₁ ∈ cons a₁ (single a₂) (single a₃) := by simp only [simp_elemMem]
example : a₂ ∈ cons a₁ (single a₂) (single a₃) := by simp only [simp_elemMem]
example : a₃ ∈ cons a₁ (single a₂) (single a₃) := by simp only [simp_elemMem]
example : ¬a₃ ∈ cons a₁ (single a₂) (single a₂) := by simp only [simp_elemMem, h₂.symm, h₃]

end elemMem

section contains

variable [DecidableEq α]
variable (a₁ a₂ a₃ : α) (h₁ : a₁ ≠ a₂) (h₂ : a₂ ≠ a₃) (h₃ : a₃ ≠ a₁)

example : ¬nil.contains 1 := by decide
example : (single 1).contains 1 := by decide
example : ¬(single 1).contains 2 := by decide
example : (cons 1 (single 2) (single 3)).contains 1 := by decide
example : (cons 1 (single 2) (single 3)).contains 2 := by decide
example : (cons 1 (single 2) (single 3)).contains 3 := by decide
example : ¬(cons 1 (single 2) (single 2)).contains 3 := by decide

example : ¬nil.contains a₁ := by simp only [simp_contains]
example : (single a₁).contains a₁ := by simp only [simp_contains]
example : ¬(single a₁).contains a₂ := by simp only [simp_contains, h₁.symm]
example : (cons a₁ (single a₂) (single a₃)).contains a₁ := by simp only [simp_contains]
example : (cons a₁ (single a₂) (single a₃)).contains a₂ := by simp only [simp_contains]
example : (cons a₁ (single a₂) (single a₃)).contains a₃ := by simp only [simp_contains]
example : ¬(cons a₁ (single a₂) (single a₂)).contains a₃ := by simp only [simp_contains, h₂.symm, h₃]

end contains

section inf

variable [SemilatticeInf α]
variable (a₁ a₂ a₃ : α) (h₁ : a₁ ≤ a₂) (h₂ : a₂ ≤ a₃)

example : (nil : BinTree ℕ).inf = ⊤ := by decide
example : (single 1).inf = some 1 := by decide
example : (cons 1 (single 2) (single 3)).inf = some 1 := by decide
example : (cons 3 (single 1) (single 2)).inf = some 1 := by decide
example : (cons 2 (single 3) (single 1)).inf = some 1 := by decide

example : (nil : BinTree α).inf = ⊤ := by simp only [simp_inf]
example : (single a₁).inf = a₁ := by simp only [simp_inf]
example : (cons a₁ (single a₂) (single a₃)).inf = a₁ := by simp [simp_inf, h₁, le_trans h₁ h₂]
example : (cons a₃ (single a₁) (single a₂)).inf = a₁ := by simp [simp_inf, h₁, le_trans h₁ h₂]
example : (cons a₂ (single a₃) (single a₁)).inf = a₁ := by simp [simp_inf, h₁, le_trans h₁ h₂]

end inf

section sup

variable [SemilatticeSup α]
variable (a₁ a₂ a₃ : α) (h₁ : a₁ ≤ a₂) (h₂ : a₂ ≤ a₃)

example : (nil : BinTree ℕ).sup = ⊥ := by decide
example : (single 1).sup = some 1 := by decide
example : (cons 1 (single 2) (single 3)).sup = some 3 := by decide
example : (cons 3 (single 1) (single 2)).sup = some 3 := by decide
example : (cons 2 (single 3) (single 1)).sup = some 3 := by decide

example : (nil : BinTree α).sup = ⊥ := by simp only [simp_sup]
example : (single a₁).sup = a₁ := by simp only [simp_sup]
example : (cons a₁ (single a₂) (single a₃)).sup = a₃ := by simp [simp_sup, h₁, h₂]
example : (cons a₃ (single a₁) (single a₂)).sup = a₃ := by simp [simp_sup, h₂, le_trans h₁ h₂]
example : (cons a₂ (single a₃) (single a₁)).sup = a₃ := by simp [simp_sup, h₂, le_trans h₁ h₂]

end sup

section infSupOrdEq

example : InfSupOrdered.mk (some 0) ⊥ true = InfSupOrdered.mk (some 0) ⊥ true := by decide
example : ¬InfSupOrdered.mk (some 0) ⊥ true = InfSupOrdered.mk ⊤ ⊥ true := by decide

end infSupOrdEq

section ordered

variable [Lattice α] [DecidableLT α]
variable (a₁ a₂ a₃ : α) (h₁ : a₁ < a₂) (h₂ : a₂ < a₃)

example : (nil : BinTree ℕ).ordered := by decide
example : (single 1).ordered := by decide
example : ¬(cons 1 (single 2) (single 3)).ordered := by decide
example : ¬(cons 3 (single 1) (single 2)).ordered := by decide
example : ¬(cons 2 (single 3) (single 1)).ordered := by decide
example : ¬(cons 1 (single 3) (single 2)).ordered := by decide
example : (cons 2 (single 1) (single 3)).ordered := by decide
example : ¬(cons 3 (single 2) (single 1)).ordered := by decide

example : (nil : BinTree ℕ).ordered := by simp only [simp_ordered]
example : (single a₁).ordered := by simp only [simp_ordered]
example : ¬(cons a₁ (single a₂) (single a₃)).ordered := by simp only [simp_ordered, lt_asymm h₁]
example : ¬(cons a₃ (single a₁) (single a₂)).ordered := by simp only [simp_ordered, lt_asymm h₂]
example : ¬(cons a₂ (single a₃) (single a₁)).ordered := by simp only [simp_ordered, lt_asymm h₂]
example : ¬(cons a₁ (single a₃) (single a₂)).ordered := by simp only [simp_ordered, lt_asymm (lt_trans h₁ h₂)]
example : (cons a₂ (single a₁) (single a₃)).ordered := by simp only [simp_ordered, h₁, h₂]
example : ¬(cons a₃ (single a₂) (single a₁)).ordered := by simp only [simp_ordered, lt_asymm (lt_trans h₁ h₂)]

end ordered

end BinTree

end CMaps
