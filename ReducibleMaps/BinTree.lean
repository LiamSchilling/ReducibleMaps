import ReducibleMaps.Init
import Mathlib.Order.WithBot

/-!
# Binary Trees

Defines the type of binary trees with a value at each node.

## Main definitions

- `BinTree α`: the type of binary trees containing members of `α`.
- `Path`: the type of node indices, implemented as a list of directions `Edge.left` or
  `Edge.right`.
- `I ∈ᵢ T`: the path `I` is a valid index to a node in the tree `T`.
- `T[I]`: the value of type `α` at index `I` in the tree `T`, requiring `I ∈ᵢ T` as a precondition.
- `a ∈ T`: the value `a` of type `α` is contained at some node in the tree `T`.
- `T.ordered`: the left-to-right traversal of the tree `T` is strictly increasingly ordered.

## Main [simp sets](ReducibleMaps/Init.html)

- `simp_elemMem`: reduces `a ∈ T`, requiring judgments of equality between `a` and elements in `T`.
- `simp_ordered`: reduces `T.ordered` by first rewriting it as `T.infThenSupThenOrdered.ordered`,
  requiring judgments of comparison between `a` and elements in `T`.
-/

namespace CMaps

/-- The type of binary trees with a value at each node. -/
inductive BinTree (α : Type*) where
  | nil : BinTree α
  | cons : α → BinTree α → BinTree α → BinTree α

namespace BinTree

/-- The type of outgoing edges from a node in a binary tree. Namely, `left` and `right`. -/
inductive Edge where
  | left
  | right

instance : DecidableEq Edge := by
  intro i j
  cases i <;> cases j
  all_goals first
  | apply isTrue; rfl
  | apply isFalse; simp

/-- The strict ordering where `left < right`.

Accessed by notation `i < j`. -/
def edgeLt : Edge → Edge → Bool
  | .left, .right => true
  | _, _ => false

instance : LT Edge where
  lt i j := edgeLt i j

/-- Notational equality lemma. -/
lemma edgeLt_eq (i j : Edge) : edgeLt i j ↔ i < j := by
  rfl

instance : DecidableLT Edge :=
  fun i j => decidable_of_decidable_of_iff <| edgeLt_eq i j

/-- The primary judgment of the ordering. Namely, `left < right`. -/
@[simp, simp_edgeLt]
lemma edgeLt_true : Edge.left < Edge.right :=
  rfl

/-- Nothing is greater than `right`. -/
@[simp, simp_edgeLt]
lemma edgeLt_right (i : Edge) : ¬.right < i := by
  cases i <;> trivial

/-- Nothing is less than `left`. -/
@[simp, simp_edgeLt]
lemma edgeLt_left (i : Edge) : ¬i < .left := by
  cases i <;> trivial

/-- The order is irreflexive. -/
@[simp, simp_edgeLt]
lemma edgeLt_self (i : Edge) : ¬i < i := by
  cases i <;> trivial

/-- The type of node indices in a binary tree, implemented as a list of outgoing edges that forms
a path from the root. Consequently, `nil` is the path to the root node. -/
abbrev Path :=
  List Edge

/-- The lexicographic order of paths, where `I < J` when `I` comes before `J` in the
left-to-right traversal of a tree.

Accessed by notation `I < J`. -/
def pathLt : Path → Path → Bool
  | [], [] => false
  | i :: _, [] => i = .left
  | [], j :: _ => j = .right
  | i :: I, j :: J => if i = j then pathLt I J else i < j

instance : LT Path where
  lt I J := pathLt I J

/-- Notational equality lemma. -/
lemma pathLt_eq (I J : Path) : pathLt I J ↔ I < J := by
  rfl

instance : DecidableLT Path :=
  fun I J => decidable_of_decidable_of_iff <| pathLt_eq I J

/-- A path that goes to the left immediately is less than `nil`. -/
@[simp, simp_pathLt]
lemma pathLt_left_nil (I : Path) : .left :: I < [] := by
  simp [LT.lt, pathLt]

/-- A path that goes to the right immediately is not less than `nil`. -/
@[simp, simp_pathLt]
lemma pathLt_right_nil (I : Path) : ¬.right :: I < [] := by
  simp [LT.lt, pathLt]

/-- A path that goes to the left immediately is not greater than `nil`. -/
@[simp, simp_pathLt]
lemma pathLt_nil_left (J : Path) : ¬[] < .left :: J := by
  simp [LT.lt, pathLt]

/-- A path that goes to the right immediately is greater than `nil`. -/
@[simp, simp_pathLt]
lemma pathLt_nil_right (J : Path) : [] < .right :: J := by
  simp [LT.lt, pathLt]

/-- Paths that go in the same direction immediately compare the same as their child paths. This
traverses the paths by one element during simplification. -/
@[simp, simp_pathLt]
lemma pathLt_cons_same (I J : Path) : i :: I < i :: J ↔ I < J := by
  simp [LT.lt, pathLt]

/-- A path that goes to the left immediately is less than a path that goes to the right
immediately. -/
@[simp, simp_pathLt]
lemma pathLt_cons_true (I J : Path) : .left :: I < .right :: J := by
  dsimp only [LT.lt]; simp [pathLt]

/-- A path that goes to the right immediately is not less than a path that goes to the left
immediately. -/
@[simp, simp_pathLt]
lemma pathLt_cons_false (I J : Path) : ¬.right :: I < .left :: J := by
  dsimp only [LT.lt]; simp [pathLt]

/-- The order is irreflexive. -/
@[simp, simp_pathLt]
lemma pathLt_self (I : Path) : ¬I < I := by
  induction I with
  | nil => trivial
  | cons _ _ _ => simpa

/-- Decides whether a path is a valid index to a node in a tree. This will serve as a precondition
for accessing from a tree by index.

Accessed by the notation `I ∈ᵢ T`. -/
def pathMem : BinTree α → Path → Bool
  | nil, _ => false
  | cons _ _ _, [] => true
  | cons _ L _, .left :: I => L.pathMem I
  | cons _ _ R, .right :: I => R.pathMem I

notation:50 I:50 " ∈ᵢ " T:50 => pathMem T I

/-- `nil` has no valid indices. -/
@[simp, simp_pathMem]
lemma pathMem_nil (I : Path) : ¬I ∈ᵢ (nil : BinTree α) := by
  simp [pathMem]

/-- Any `cons` has the root index as a valid index. -/
@[simp, simp_pathMem]
lemma pathMem_cons_nil (a : α) (L R : BinTree α) : [] ∈ᵢ cons a L R :=
  rfl

/-- This is left traversal of the tree during simplification. -/
@[simp, simp_pathMem]
lemma pathMem_cons_left (L : BinTree α) (I : Path) : .left :: I ∈ᵢ cons a L R ↔ I ∈ᵢ L := by
  rfl

/-- This is right traversal of the tree during simplification. -/
@[simp, simp_pathMem]
lemma pathMem_cons_right (R : BinTree α) (I : Path) : .right :: I ∈ᵢ cons a L R ↔ I ∈ᵢ R := by
  rfl

/-- Accesses an element from a tree by index, requiring that the index is valid as a
precondition.

Accessed by the notation `T[I]`. -/
def getElem : ∀ (T : BinTree α) I, I ∈ᵢ T → α
  | nil, _, _ => by contradiction
  | cons a _ _, [], _ => a
  | cons _ L _, .left :: I, h => L.getElem I h
  | cons _ _ R, .right :: I, h => R.getElem I h

instance : GetElem (BinTree α) Path α (fun T I => I ∈ᵢ T) where
  getElem T I h := T.getElem I h

/-- The element at the root index it exactly the value at the root node. -/
@[simp, simp_getElem]
lemma getElem_cons_nil (a : α) : (cons a L R)[([] : Path)] = a :=
  rfl

/-- This is left traversal of the tree during simplification. -/
@[simp, simp_getElem]
lemma getElem_cons_left (L : BinTree α) (_ : .left :: I ∈ᵢ cons a L R) :
    (cons a L R)[.left :: I] = L[I] :=
  rfl

/-- This is right traversal of the tree during simplification. -/
@[simp, simp_getElem]
lemma getElem_cons_right (L : BinTree α) (_ : .right :: I ∈ᵢ cons a L R) :
    (cons a L R)[.right :: I] = R[I] :=
  rfl

/-- Folds the values in a tree from the leaves to the root.

For example:
`fold f b (cons a₂ (cons a₁ nil nil) (cons a₃ nil nil)) = f a₂ (f a₁ b b) (f a₃ b b)` -/
def fold (f : α → β → β → β) (b : β) : BinTree α → β
  | nil => b
  | cons a L R => f a (L.fold f b) (R.fold f b)

/-- Folds the values in a tree over its left-to-right traversal.

For example:
`fold f b (cons a₂ (cons a₁ nil nil) (cons a₃ nil nil)) = f (f (f b a₁) a₂) a₃` -/
def foldFlat (f : β → α → β) (b : β) : BinTree α → β
  | nil => b
  | cons a L R => foldFlat f (f (foldFlat f b L) a) R

/-- Folds the values in a tree over its right-to-left traversal.

For example:
`fold f b (cons a₂ (cons a₁ nil nil) (cons a₃ nil nil)) = f a₁ (f a₂ (f a₃ b))` -/
def foldFlatRev (f : α → β → β) (b : β) : BinTree α → β
  | nil => b
  | cons a L R => foldFlatRev f (f a (foldFlatRev f b R)) L

/-- Maps each value `a` in a tree to `f a` in a the resulting tree. -/
def map (f : α → β) : BinTree α → BinTree β :=
  fold (fun a L R => cons (f a) L R) nil

/-- Returns the left-to-right traversal of a tree with each value `a` mapped to `f a`. -/
def mapFlat (f : α → β) : BinTree α → List β :=
  foldFlatRev (fun a L => f a :: L) []

/-- Returns the right-to-left traversal of a tree with each value `a` mapped to `f a`. -/
def mapFlatRev (f : α → β) : BinTree α → List β :=
  foldFlat (fun L a => f a :: L) []

/-- Asserts that a value is contained at some node in a tree.

Accessed by the notation `a ∈ T`. -/
def elemMem (T : BinTree α) (a : α) :=
  ∃ I, ∃ (_ : I ∈ᵢ T), T[I] = a

instance : Membership α (BinTree α) where
  mem T a := T.elemMem a

/-- If some access of a tree is `a` then `a` is in the tree. -/
lemma elemMem_of_getElem (a : α) (T : BinTree α) (_ : I ∈ᵢ T) : T[I] = a → a ∈ T := by
  intro
  apply Exists.intro; apply Exists.intro
  assumption

/-- `nil` contains no elements. -/
@[simp, simp_elemMem]
lemma elemMem_nil (a : α) : ¬a ∈ nil := by
  intro ⟨_, _, _⟩; contradiction

/-- A tree contains the element at its root. -/
@[simp, simp_elemMem]
lemma elemMem_cons (a : α) : a ∈ cons a L R := by
  apply Exists.intro []; apply Exists.intro <;> simp

/-- If the left subtree contains `a` then the tree contains `a`. -/
@[simp]
lemma elemMem_cons_left (a₀ a : α) (L : BinTree α) : a₀ ∈ L → a₀ ∈ cons a L R := by
  intro ⟨I, _, _⟩
  apply Exists.intro <| .left :: I; apply Exists.intro
  simpa

/-- If the right subtree contains `a` then the tree contains `a`. -/
@[simp]
lemma elemMem_cons_right (a₀ a : α) (L : BinTree α) : a₀ ∈ R → a₀ ∈ cons a L R := by
  intro ⟨I, _, _⟩
  apply Exists.intro <| .right :: I; apply Exists.intro
  simpa

/-- A tree contains `a` if and only if the root or either subtree contains `a`. This is traversal
to the next layer of the tree during simplification.

For general applications, applying this lemma does not result in a simpler statement, so we do not
mark it as `simp` generally. This lemma does result in a simpler statement when the goal is to
traverse the tree searching for `a`, so we give it to our solving simp set `simp_elemMem`. -/
@[simp_elemMem]
lemma elemMem_cons_or (a₀ a : α) (L R : BinTree α) :
    a₀ ∈ cons a L R ↔ a₀ = a ∨ a₀ ∈ L ∨ a₀ ∈ R := by
  constructor
  . intro ⟨I, _, _⟩
    cases I
    . apply Or.inl
      symm; assumption
    . rename_i i _ _ _
      apply Or.inr
      cases i
      . apply Or.inl
        apply elemMem_of_getElem
        assumption
      . apply Or.inr
        apply elemMem_of_getElem
        assumption
  . grind [elemMem_cons, elemMem_cons_left, elemMem_cons_right]

/-- Decides whether a value is contained at some node in a tree. This will be a decision procedure
for `a ∈ T`. -/
def contains [DecidableEq α] (T : BinTree α) (a₀ : α) : Bool :=
  T.fold (a₀ = · || · || ·) false

/-- `nil` contains no elements. -/
@[simp, simp_contains]
lemma contains_nil [DecidableEq α] (a : α) : ¬nil.contains a := by
  simp [contains, fold]

/-- A tree contains the element at its root. -/
@[simp, simp_contains]
lemma contains_cons [DecidableEq α] (a : α) : (cons a L R).contains a := by
  simp [contains, fold]

/-- If the left subtree contains `a` then the tree contains `a`. -/
@[simp]
lemma contains_cons_left [DecidableEq α] (a₀ a : α) (L : BinTree α) :
    L.contains a₀ → (cons a L R).contains a₀ := by
  intro h
  simp only [contains, fold, Bool.or_eq_true]
  apply Or.inl; apply Or.inr
  assumption

/-- If the right subtree contains `a` then the tree contains `a`. -/
@[simp]
lemma contains_cons_right [DecidableEq α] (a₀ a : α) (L : BinTree α) :
    R.contains a₀ → (cons a L R).contains a₀ := by
  intro
  simp only [contains, fold, Bool.or_eq_true]
  apply Or.inr
  assumption

/-- A tree contains `a` if and only if the root or either subtree contains `a`. This is traversal
to the next layer of the tree during simplification.

For general applications, applying this lemma does not result in a simpler statement, so we do not
mark it as `simp` generally. This lemma does result in a simpler statement when the goal is to
traverse the tree searching for `a`, so we give it to our solving simp set `simp_contains`. -/
@[simp_contains]
lemma contains_cons_or [DecidableEq α] (a₀ a : α) (L R : BinTree α) :
    (cons a L R).contains a₀ ↔ a₀ = a ∨ L.contains a₀ ∨ R.contains a₀ := by
  grind [contains, fold]

/-- `T.contains a` decides `a ∈ T`. -/
lemma contains_iff_elemMem [LT α] [DecidableEq α] (T : BinTree α) (a : α) :
    T.contains a ↔ a ∈ T := by
  induction T with
  | nil => constructor <;> simp
  | cons a L R ih₁ ih₂ => grind [contains_cons_or, elemMem_cons_or]

instance [LT α] [DecidableEq α] (T : BinTree α) (a : α) : Decidable (a ∈ T) :=
  decidable_of_decidable_of_iff <| contains_iff_elemMem T a

/-- Returns the infimum of the elements in a tree, with `⊤` for the empty tree. -/
def inf [SemilatticeInf α] : BinTree α → WithTop α :=
  fold (· ⊓ · ⊓ ·) ⊤

/-- The infimum of the empty tree is `⊤`. -/
@[simp, simp_inf]
lemma inf_nil [SemilatticeInf α] : (nil : BinTree α).inf = ⊤ :=
  rfl

/-- This is traversal to the next layer of the tree during simplification.

For general applications, applying this lemma does not result in a simpler statement, so we do not
mark it as `simp` generally. This lemma does result in a simpler statement when the goal is to
traverse the tree searching for the infimum, so we give it to our solving simp set `simp_inf`. -/
@[simp_inf]
lemma inf_cons [SemilatticeInf α] (a : α) (L R : BinTree α) :
    (cons a L R).inf = ↑a ⊓ L.inf ⊓ R.inf :=
  rfl

/-- Returns the supremum of the elements in a tree, with `⊥` for the empty tree. -/
def sup [SemilatticeSup α] : BinTree α → WithBot α :=
  fold (· ⊔ · ⊔ ·) ⊥

/-- The supremum of the empty tree is `⊥`. -/
@[simp, simp_sup]
lemma sup_nil [SemilatticeSup α] : (nil : BinTree α).sup = ⊥ :=
  rfl

/-- This is traversal to the next layer of the tree during simplification.

For general applications, applying this lemma does not result in a simpler statement, so we do not
mark it as `simp` generally. This lemma does result in a simpler statement when the goal is to
traverse the tree searching for the supremum, so we give it to our solving simp set `simp_sup`. -/
@[simp_sup]
lemma sup_cons [SemilatticeSup α] (a : α) (L R : BinTree α) :
    (cons a L R).sup = ↑a ⊔ L.sup ⊔ R.sup :=
  rfl

/-- Asserts that the left-to-right traversal of a tree is strictly increasingly ordered.

This is an important property to automate because it will be an invariant in our type of ordered
maps. The naive simplification procedure—checking at each node the ordering of the supremum of the
left subtree, the node value, and the infimum of the right subtree—unnecessarily recomputes
supremums and infimums of deeper subtrees. Instead, our simplification procedure `simp_ordered`
first rewrites `T.ordered` as a decision on a structure where previous infumum and supremum
computations can be reused. See `infThenSupThenOrdered`. -/
def ordered [LT α] (T : BinTree α) :=
  ∀ I J (_ : I ∈ᵢ T) (_ : J ∈ᵢ T), I < J → T[I] < T[J]

/-- `nil` is ordered. -/
@[simp]
lemma ordered_nil [LT α] : (nil : BinTree α).ordered := by
  simp [ordered]

/-- A tree is ordered if and only if its left subtree is ordered, its right subtree is ordered,
the supremum of its left subtree is less than its root, and its root is less than the infimum of
its right subtree. -/
lemma ordered_cons [Lattice α] (a : α) (L R : BinTree α) :
    (cons a L R).ordered ↔ L.ordered ∧ R.ordered ∧ L.sup < a ∧ a < R.inf := by
  sorry

/-- An information structure intended to contain the infimum of a tree, the supremum of a tree, and
a decision of whether the tree is ordered. For why this is useful, see `infThenSupThenOrdered`. -/
@[ext]
structure InfSupOrdered (α : Type*) where
  inf : WithTop α
  sup : WithBot α
  ordered : Bool

instance [DecidableEq α] : DecidableEq (InfSupOrdered α) := by
  intro x y
  cases x; cases y; rename_i inf₁ sup₁ ordered₁ inf₂ sup₂ ordered₂
  by_cases h₁ : inf₁ = inf₂ <;> by_cases h₂ : sup₁ = sup₂ <;> by_cases h₃ : ordered₁ = ordered₂
  apply isTrue; simp [h₁, h₂, h₃]
  all_goals apply isFalse; simp [h₁, h₂, h₃]

/-- Returns the infiumum of a tree, the supremum of a tree, and a decision of whether the tree is
ordered. Computing all of these at each node allows a more efficient ordering decision, since
previous infimum and supremum computations can be reused. -/
def infThenSupThenOrdered [Lattice α] [DecidableLT α] : BinTree α → InfSupOrdered α := by
  apply fold
  . intro a ⟨Linf, Lsup, Lordered⟩ ⟨Rinf, Rsup, Rordered⟩
    exact ⟨a ⊓ Linf ⊓ Rinf, a ⊔ Lsup ⊔ Rsup, Lordered && Rordered && Lsup < a && a < Rinf⟩
  . exact ⟨⊤, ⊥, true⟩

/-- The result of `infThenSupThenOrdered` in the `nil` case. -/
@[simp, simp_infThenSupThenOrdered, simp_ordered]
lemma infThenSupThenOrdered_nil [Lattice α] [DecidableLT α] :
    (nil : BinTree α).infThenSupThenOrdered = ⟨⊤, ⊥, true⟩ :=
  rfl

/-- The result of `infThenSupThenOrdered` in the `cons` case. The `match` patterns are important
here to ensure that the computation in the body cannot proceed until `L.infThenSupThenOrdered` and
`R.infThenSupThenOrdered` have been computed themselves, preventing a lazy rewrite that leads them
to be computed multiple times. -/
@[simp_infThenSupThenOrdered, simp_ordered]
lemma infSupOrdered_cons [Lattice α] [DecidableLT α] (a : α) (L R : BinTree α) :
    (cons a L R).infThenSupThenOrdered =
    match L.infThenSupThenOrdered, R.infThenSupThenOrdered with
    | ⟨Linf, Lsup, Lordered⟩, ⟨Rinf, Rsup, Rordered⟩ =>
      ⟨a ⊓ Linf ⊓ Rinf, a ⊔ Lsup ⊔ Rsup, Lordered && Rordered && Lsup < a && a < Rinf⟩ :=
  rfl

open Classical in
/-- Correctness proof for `infThenSupThenOrdered`. -/
lemma infThenSupThenOrdered_eq [Lattice α] [DecidableLT α] (T : BinTree α) :
    T.infThenSupThenOrdered = ⟨T.inf, T.sup, T.ordered⟩ := by
  induction T with
  | nil => simp [infThenSupThenOrdered, fold]
  | cons _ _ _ ih₁ ih₂ =>
    ext
    all_goals
      dsimp only [infThenSupThenOrdered, fold]
      rw [←infThenSupThenOrdered, ih₁, ih₂]
    . rfl
    . rfl
    . grind [ordered_cons]

@[simp, simp_inf]
lemma infThenSupThenOrdered_inf [Lattice α] [DecidableLT α] (T : BinTree α) :
    T.infThenSupThenOrdered.inf = T.inf := by
  rw [infThenSupThenOrdered_eq]

@[simp, simp_sup]
lemma infThenSupThenOrdered_sup [Lattice α] [DecidableLT α] (T : BinTree α) :
    T.infThenSupThenOrdered.sup = T.sup := by
  rw [infThenSupThenOrdered_eq]

/-- Though it is tempting to mark this lemma as `simp`, this contradicts the simp normal form for
our simp set `simp_ordered`, which reduces `T.ordered` to `T.infThenSupThenOrdered.ordered` because
the latter is more efficient for deciding order. Thus, to ensure termination of
`simp [simp_ordered]`, this lemma cannot be marked as `simp`. -/
lemma infThenSupThenOrdered_ordered [Lattice α] [DecidableLT α] (T : BinTree α) :
    T.infThenSupThenOrdered.ordered ↔ T.ordered := by
  rw [infThenSupThenOrdered_eq]
  simp

/-- This lemma for our simp set `simp_ordered` reduces `T.ordered` to
`T.infThenSupThenOrdered.ordered` because the latter is more efficient for deciding order. See
`infThenSupThenOrdered`. -/
@[simp_ordered]
lemma infThenSupThenOrdered_ordered_symm [Lattice α] [DecidableLT α] (T : BinTree α) :
    T.ordered ↔ T.infThenSupThenOrdered.ordered := by
  symm; apply infThenSupThenOrdered_ordered

instance [Lattice α] [DecidableLT α] (T : BinTree α) : Decidable T.ordered :=
  decidable_of_decidable_of_iff <| infThenSupThenOrdered_ordered T

end BinTree

end CMaps
