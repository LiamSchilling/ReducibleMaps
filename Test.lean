import ReducibleMaps

/-!
# Unit Tests for "Reducible Maps"

This file tests the proof-automation capabilities of this library. Each `section` in this file
tests the `decide` and `simp` tactics when relevant for proving statements about the named
structure.
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
example : [] ∈ᵢ cons 0 nil nil := by decide
example : ¬[Edge.left] ∈ᵢ cons 0 nil nil := by decide
example : ¬[Edge.right] ∈ᵢ cons 0 nil nil := by decide

example : ¬[] ∈ᵢ (nil : BinTree Nat) := by simp only [simp_pathMem]
example : ¬[Edge.left] ∈ᵢ (nil : BinTree Nat) := by simp only [simp_pathMem]
example : ¬[Edge.right] ∈ᵢ (nil : BinTree Nat) := by simp only [simp_pathMem]
example : [] ∈ᵢ cons 0 nil nil := by simp only [simp_pathMem]
example : ¬[Edge.left] ∈ᵢ cons 0 nil nil := by simp only [simp_pathMem]
example : ¬[Edge.right] ∈ᵢ cons 0 nil nil := by simp only [simp_pathMem]

end pathMem

section getElem

variable (a₁ a₂ a₃ : α) (_ : a₁ ≠ a₂) (_ : a₂ ≠ a₃) (_ : a₃ ≠ a₁)

example : (cons 1 nil nil)[([] : Path)] = 1 := by decide
example : (cons 1 (cons 2 nil nil) (cons 3 nil nil))[([] : Path)] = 1 := by decide
example : (cons 1 (cons 2 nil nil) (cons 3 nil nil))[[Edge.left]] = 2 := by decide
example : (cons 1 (cons 2 nil nil) (cons 3 nil nil))[[Edge.right]] = 3 := by decide

example : (cons a₁ nil nil)[([] : Path)] = a₁ := by simp
example : (cons a₁ (cons a₂ nil nil) (cons a₃ nil nil))[([] : Path)] = a₁ := by simp only [simp_getElem]
example : (cons a₁ (cons a₂ nil nil) (cons a₃ nil nil))[[Edge.left]] = a₂ := by simp only [simp_getElem]
example : (cons a₁ (cons a₂ nil nil) (cons a₃ nil nil))[[Edge.right]] = a₃ := by simp only [simp_getElem]

end getElem

section elemMem

variable (a₁ a₂ a₃ : α) (h₁ : a₁ ≠ a₂) (h₂ : a₂ ≠ a₃) (h₃ : a₃ ≠ a₁)

example : ¬1 ∈ nil := by decide
example : 1 ∈ cons 1 nil nil := by decide
example : ¬2 ∈ cons 1 nil nil := by decide
example : 1 ∈ cons 1 (cons 2 nil nil) (cons 3 nil nil) := by decide
example : 2 ∈ cons 1 (cons 2 nil nil) (cons 3 nil nil) := by decide
example : 3 ∈ cons 1 (cons 2 nil nil) (cons 3 nil nil) := by decide
example : ¬3 ∈ cons 1 (cons 2 nil nil) (cons 2 nil nil) := by decide

example : ¬a₁ ∈ nil := by simp only [simp_elemMem]
example : a₁ ∈ cons a₁ nil nil := by simp only [simp_elemMem]
example : ¬a₂ ∈ cons a₁ nil nil := by simp only [simp_elemMem, h₁.symm]
example : a₁ ∈ cons a₁ (cons a₂ nil nil) (cons a₃ nil nil) := by simp only [simp_elemMem]
example : a₂ ∈ cons a₁ (cons a₂ nil nil) (cons a₃ nil nil) := by simp only [simp_elemMem]
example : a₃ ∈ cons a₁ (cons a₂ nil nil) (cons a₃ nil nil) := by simp only [simp_elemMem]
example : ¬a₃ ∈ cons a₁ (cons a₂ nil nil) (cons a₂ nil nil) := by simp only [simp_elemMem, h₂.symm, h₃]

end elemMem

section contains

variable [DecidableEq α]
variable (a₁ a₂ a₃ : α) (h₁ : a₁ ≠ a₂) (h₂ : a₂ ≠ a₃) (h₃ : a₃ ≠ a₁)

example : ¬nil.contains 1 := by decide
example : (cons 1 nil nil).contains 1 := by decide
example : ¬(cons 1 nil nil).contains 2 := by decide
example : (cons 1 (cons 2 nil nil) (cons 3 nil nil)).contains 1 := by decide
example : (cons 1 (cons 2 nil nil) (cons 3 nil nil)).contains 2 := by decide
example : (cons 1 (cons 2 nil nil) (cons 3 nil nil)).contains 3 := by decide
example : ¬(cons 1 (cons 2 nil nil) (cons 2 nil nil)).contains 3 := by decide

example : ¬nil.contains a₁ := by simp only [simp_contains]
example : (cons a₁ nil nil).contains a₁ := by simp only [simp_contains]
example : ¬(cons a₁ nil nil).contains a₂ := by simp only [simp_contains, h₁.symm]
example : (cons a₁ (cons a₂ nil nil) (cons a₃ nil nil)).contains a₁ := by simp only [simp_contains]
example : (cons a₁ (cons a₂ nil nil) (cons a₃ nil nil)).contains a₂ := by simp only [simp_contains]
example : (cons a₁ (cons a₂ nil nil) (cons a₃ nil nil)).contains a₃ := by simp only [simp_contains]
example : ¬(cons a₁ (cons a₂ nil nil) (cons a₂ nil nil)).contains a₃ := by simp only [simp_contains, h₂.symm, h₃]

end contains

section inf

variable [SemilatticeInf α]
variable (a₁ a₂ a₃ : α) (h₁ : a₁ ≤ a₂) (h₂ : a₂ ≤ a₃)

example : (nil : BinTree ℕ).inf = ⊤ := by decide
example : (cons 1 nil nil).inf = some 1 := by decide
example : (cons 1 (cons 2 nil nil) (cons 3 nil nil)).inf = some 1 := by decide
example : (cons 3 (cons 1 nil nil) (cons 2 nil nil)).inf = some 1 := by decide
example : (cons 2 (cons 3 nil nil) (cons 1 nil nil)).inf = some 1 := by decide

example : (nil : BinTree α).inf = ⊤ := by simp only [simp_inf]
example : (cons a₁ nil nil).inf = a₁ := by simp only [simp_inf]
example : (cons a₁ (cons a₂ nil nil) (cons a₃ nil nil)).inf = a₁ := by simp [simp_inf, h₁, le_trans h₁ h₂]
example : (cons a₃ (cons a₁ nil nil) (cons a₂ nil nil)).inf = a₁ := by simp [simp_inf, h₁, le_trans h₁ h₂]
example : (cons a₂ (cons a₃ nil nil) (cons a₁ nil nil)).inf = a₁ := by simp [simp_inf, h₁, le_trans h₁ h₂]

end inf

section sup

variable [SemilatticeSup α]
variable (a₁ a₂ a₃ : α) (h₁ : a₁ ≤ a₂) (h₂ : a₂ ≤ a₃)

example : (nil : BinTree ℕ).sup = ⊥ := by decide
example : (cons 1 nil nil).sup = some 1 := by decide
example : (cons 1 (cons 2 nil nil) (cons 3 nil nil)).sup = some 3 := by decide
example : (cons 3 (cons 1 nil nil) (cons 2 nil nil)).sup = some 3 := by decide
example : (cons 2 (cons 3 nil nil) (cons 1 nil nil)).sup = some 3 := by decide

example : (nil : BinTree α).sup = ⊥ := by simp only [simp_sup]
example : (cons a₁ nil nil).sup = a₁ := by simp only [simp_sup]
example : (cons a₁ (cons a₂ nil nil) (cons a₃ nil nil)).sup = a₃ := by simp [simp_sup, h₁, h₂]
example : (cons a₃ (cons a₁ nil nil) (cons a₂ nil nil)).sup = a₃ := by simp [simp_sup, h₂, le_trans h₁ h₂]
example : (cons a₂ (cons a₃ nil nil) (cons a₁ nil nil)).sup = a₃ := by simp [simp_sup, h₂, le_trans h₁ h₂]

end sup

section infSupOrdEq

example : InfSupOrdered.mk (some 0) ⊥ true = InfSupOrdered.mk (some 0) ⊥ true := by decide
example : ¬InfSupOrdered.mk (some 0) ⊥ true = InfSupOrdered.mk ⊤ ⊥ true := by decide

end infSupOrdEq

section ordered

variable [Lattice α] [DecidableLT α]
variable (a₁ a₂ a₃ : α) (h₁ : a₁ < a₂) (h₂ : a₂ < a₃)

example : (nil : BinTree ℕ).ordered := by decide
example : (cons 1 nil nil).ordered := by decide
example : ¬(cons 1 (cons 2 nil nil) (cons 3 nil nil)).ordered := by decide
example : ¬(cons 3 (cons 1 nil nil) (cons 2 nil nil)).ordered := by decide
example : ¬(cons 2 (cons 3 nil nil) (cons 1 nil nil)).ordered := by decide
example : ¬(cons 1 (cons 3 nil nil) (cons 2 nil nil)).ordered := by decide
example : (cons 2 (cons 1 nil nil) (cons 3 nil nil)).ordered := by decide
example : ¬(cons 3 (cons 2 nil nil) (cons 1 nil nil)).ordered := by decide

example : (nil : BinTree ℕ).ordered := by simp only [simp_ordered]
example : (cons a₁ nil nil).ordered := by simp only [simp_ordered]
example : ¬(cons a₁ (cons a₂ nil nil) (cons a₃ nil nil)).ordered := by simp only [simp_ordered, lt_asymm h₁]
example : ¬(cons a₃ (cons a₁ nil nil) (cons a₂ nil nil)).ordered := by simp only [simp_ordered, lt_asymm h₂]
example : ¬(cons a₂ (cons a₃ nil nil) (cons a₁ nil nil)).ordered := by simp only [simp_ordered, lt_asymm h₂]
example : ¬(cons a₁ (cons a₃ nil nil) (cons a₂ nil nil)).ordered := by simp only [simp_ordered, lt_asymm (lt_trans h₁ h₂)]
example : (cons a₂ (cons a₁ nil nil) (cons a₃ nil nil)).ordered := by simp only [simp_ordered, h₁, h₂]
example : ¬(cons a₃ (cons a₂ nil nil) (cons a₁ nil nil)).ordered := by simp only [simp_ordered, lt_asymm (lt_trans h₁ h₂)]

end ordered

end BinTree

end CMaps
