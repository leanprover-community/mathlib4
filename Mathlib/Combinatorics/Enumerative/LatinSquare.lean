/-
Copyright (c) 2026 Christopher J. R. Lloyd and George H. Seelinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher J. R. Lloyd, George H. Seelinger
-/
module

public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# LatinSquare

A Latin rectangle is an $m \times n$ matrix filled with $n$ different
symbols such that each symbol occurs exactly once in each row and
occurs at most once in each column.  When $m = n$, the column
condition forces each symbol to occur exactly once in each column.
This special case is called a Latin Square and their discovery is
attributed to Leohnard Euler in 1782 [euler1782].

Basic examples include the multiplication table of any finite group or
any completely solved Sudoku puzzle. Additionally, Latin squares are a
special case and motivating example of combinatorial designs.  Like
with a Sudoku puzzle, an interesting question is when a "partially
filled" Latin square can be completed to a Latin square.  In general,
it is an open question to figure out the number of distinct $n \times
n$ Latin squares, up to equivalence, although bounds exist.

A classical result in combinatorics, **Hall's Marriage Theorem**, can be
used to show that any Latin rectangle can be extended to a Latin
square; this theorem is formalized as
`latin_rectangle_extends_to_latin_square`.

## Main results

- `group_to_cayley_table`: every finite group `G` yields a `LatinSquare G G`.
- `latin_rectangle_extends_one_row`: a (non-square) `LatinRectangle` extends to a `LatinRectangle`
   with one more row. This is an application of **Hall's Marriage Theorem**,
   `hallMatchingsOn.nonempty`.
- `latin_rectangle_extends_to_latin_square`:  a `LatinRectangle` extends to a `LatinSquare`.

## Notation

- `≃` : The type of equivalences between `LatinRectangle`s.

## TODO

* [DONE] Add theorem that a k-1 × n Latin rectangle can be extended to a k × n Latin rectangle.
* [DONE] Corollary, any k x n Latin rectangle can be extneded to a Latin square.
* [DONE] Add that a n x n Latin rectangle is a Latin square.
* Add Ryser's theorem using partial Latin squares.
* Add Evan's Conjeture.
* Add isomorphism to quasigroups.
* Add isomorphism to orthogonal arrays of triples.
* Add decidablity reductions to the LS definitions

## References

* [Euler, *Recherches sur une nouvelle espèce de quarrés magiques*][euler1782]
* [vanLint, Wilson, *A Course in Combinatorics*, Chapter 17][vanlint_wilson2001]

-/

variable {m m' : Type*} [Fintype m] [Fintype m']
variable {n n' : Type*} [Fintype n] [Fintype n']
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

@[expose] public section LatinSquare

/-- For m ≤ n, an m × n Latin rectangle is a partial n × n Latin Square where
    the first m entries are filled. -/
class LatinRectangle (m : Type*) (n : Type*) (α : Type*)
  [Fintype m] [Fintype n] [Fintype α] [DecidableEq α] where
  /-- An m × n array of symbols. -/
  M : Matrix m n α
  /-- An $m × n$ Latin rectangle contains $n$ distinct entries. -/
  exactly_n_symbols : Fintype.card α = Fintype.card n
  /-- Each row contains each symbol exactly once. -/
  once_per_row : ∀ i, Function.Bijective (M.row i)
  /-- Entries cannot repeat in a given column. -/
  distinct_col_entries : ∀ y, Function.Injective (M.col y)
  /-- The number of rows is less than or equal to the number of columns. -/
  m_le_n : Fintype.card m ≤ Fintype.card n := by simp

attribute [coe] LatinRectangle.M

/-- Pretty printing of Latin rectangles. -/
instance {m n : Nat} {α : Type*} [DecidableEq α] [Fintype α] [ToString α] :
  Repr (LatinRectangle (Fin m) (Fin n) α) where
  reprPrec L _ :=
    let row (i : Fin m) :=
      String.intercalate " " (List.ofFn (fun j => (toString (L.M i j))));
      String.intercalate "\n" (List.ofFn row)

/-- A LatinSquare is a Square LatinRectangle -/
abbrev LatinSquare (n : Type*) [Fintype n] (α : Type*) [Fintype α] [DecidableEq α] :=
  LatinRectangle n n α

/-- An example of a 5 × 5 Latin rectangle with entries in Fin 5. -/
example : LatinRectangle (Fin 5) (Fin 5) (Fin 5) := LatinRectangle.mk (fun x y ↦ ((x + y) : Fin 5))
  (by decide) (by decide) (by decide)

/-- Get the underlying `Matrix` of the LatinRectangle. -/
instance {m : Type*} {n : Type*} {α : Type*} [Fintype m]
  [Fintype n] [Fintype α] [DecidableEq α] :
  Coe (LatinRectangle m n α) (Matrix m n α) where
  coe A := A.M

/-- Get a specific column of the `LatinRectangle`. -/
abbrev col (A : LatinRectangle m n α) : n → m → α := Matrix.col A

/-- Get a specific row of the `LatinRectangle`. -/
abbrev row (A : LatinRectangle m n α) : m → n → α := Matrix.row A

/-- Alernative constructor for LatinSquares using the OncePerColumn property -/
@[reducible]
def LatinSquareFromOncePerColumn
  [Fintype n] [Fintype α] [DecidableEq α]
    (M : Matrix n n α)
    (exactly_n_symbols : Fintype.card α = Fintype.card n)
    (once_per_row : ∀ i, Function.Bijective (M.row i))
    (once_per_column : ∀ j, Function.Bijective (M.col j)) : LatinSquare n α := {
    M := M,
    exactly_n_symbols := exactly_n_symbols,
    once_per_row := once_per_row,
    distinct_col_entries := (once_per_column · |>.injective)
  }

/-- Every Finite Group's Cayley table is an example of a Latin Square. -/
@[to_additive /-- Every Additive Finite Group's Cayley table is an example of a Latin Square -/,
  reducible]
def groupToCayleyTable (G : Type*) [DecidableEq G] [Group G] [Fintype G] :
  LatinSquare G G := LatinSquareFromOncePerColumn
    (M := fun i j ↦ i * j)
    (exactly_n_symbols := by rfl)
    (once_per_row := by
      simp only [Matrix.row]
      exact Group.mulLeft_bijective (G := G))
    (once_per_column := by
      simp only [Matrix.col]
      exact Group.mulRight_bijective (G := G))


section Equivalence

/-- Given relabeling maps for the rows, columns, and symbols,
    produce the relabeled Latin rectangle. -/
@[reducible]
def renameLatinRectangle
    (f : m ≃ m')
    (g : n ≃ n')
    (h : α ≃ β)
    (A : LatinRectangle m n α) :
    LatinRectangle m' n' β := {
  M := fun i' j' ↦ h (A.M (f.symm i') (g.symm j')),
  exactly_n_symbols := by
    have g' : Fintype.card n = Fintype.card n' := Fintype.card_congr g
    have h' : Fintype.card α = Fintype.card β := Fintype.card_congr h
    have k' := A.exactly_n_symbols
    omega,
  once_per_row i' :=
    h.bijective.comp (A.once_per_row (f.symm i') |>.comp g.symm.bijective)
  distinct_col_entries := by
    simp only [Matrix.col]
    have h' := A.distinct_col_entries
    simp only [Matrix.col] at h'
    intro j'
    specialize h' (g.symm j')
    have h_comp :
      (Matrix.transpose (fun i' j' ↦ h (LatinRectangle.M (f.symm i') (g.symm j'))) j') =
      h ∘ (LatinRectangle.M.transpose (g.symm j')) ∘ f.symm := by
      ext
      simp
    rw [h_comp]
    exact h.injective.comp (h'.comp f.symm.injective)
  m_le_n := by
    have ineq := A.m_le_n
    have f' : Fintype.card m = Fintype.card m' := Fintype.card_congr f
    have g' : Fintype.card n = Fintype.card n' := Fintype.card_congr g
    omega
  }

/-- An equivalence of Latin Rectangles -/
structure LREquiv (A : LatinRectangle m n α) (A' : LatinRectangle m' n' β) where
  /-- A row relabeling. -/
  (f : m ≃ m')
  /-- A column relabeling. -/
  (g : n ≃ n')
  /-- A symbol relabeling. -/
  (h : α ≃ β)
  /-- Relabelings preserve structure. -/
  (map_rel : ∀ (r : m) (c : n),
    A'.M (f r) (g c) = h (A.M r c))

/-- Two Latin rectangles are equivalent if one can be obtained from the other by some combination
    of relabeling the row indices, column indices, and symbols. -/
def LatinRectangleEquivRelation (A : LatinRectangle m n α) (A' : LatinRectangle m' n' β) :=
    Nonempty (LREquiv A A')

/-- Notation for two `LatinRectangle`s to be equivalent. -/
infixl:25 " ≃ " => LatinRectangleEquivRelation

lemma induced_latin_rectangle_is_equiv
    (f : m ≃ m')
    (g : n ≃ n')
    (h : α ≃ β)
    (A : LatinRectangle m n α) : A ≃ (renameLatinRectangle f g h A) :=
  ⟨f, g, h, by simp [LatinRectangle.M]⟩

end Equivalence

section Nonvacuous

instance Zn_nonempty {n : Nat} [NeZero n] : LatinSquare (ZMod n) (ZMod n) :=
  addGroupToCayleyTable (ZMod n)

/-- For any positive natural number n, there exists an n × n Latin square. -/
noncomputable instance n_nonempty
    {n : Type*} [Fintype n]
    [nezero_n : NeZero (Fintype.card n)]
    [h : Fact (Fintype.card n = Fintype.card α)] :
    Nonempty (LatinSquare n α) := by
  haveI := Fin.addCommGroup (Fintype.card n)
  let a := addGroupToCayleyTable (Fin (Fintype.card n))
  have f :=  Fintype.equivFin n
  have h' := Fintype.equivFinOfCardEq h.out.symm
  have h'' := Fintype.equivFin α
  have b := renameLatinRectangle f.symm f.symm h'.symm a
  exact Nonempty.intro (b : LatinSquare n α)

end Nonvacuous

section Completion

variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
variable {k : Type*} [Fintype k] [Nonempty k] [DecidableEq k]

/-- Property of `LatinRectangle` being contained in another `LatinRectangle` -/
def IsSubrect (A : LatinRectangle m n α) (B : LatinRectangle m' n' α) :=
  ∃ (ι : m ↪ m') (ι' : n ↪ n') (h : α ≃ α), ∀ (i : m), ∀ (j : n), B.M (ι i) (ι' j) = h (A.M i j)

/-- A map returning the set of symbols in α not in column j. -/
def symbolsNotIn (A : LatinRectangle k n α) (j : n) :=
  let D := Finset.image (col A j) Finset.univ
  Finset.univ \ D

/-- Given a finite collection of finite subsets $B_1, \ldots, B_k$ and, for every
$x \in \bigcup_i B_i$, let $C_x$ be the set of indices of the $B_i$'s that contain $x$.
Then, $\sum_i |B_i| = \sum_x |C_x|$. -/
lemma sum_card_eq_sum_card_fiber_biUnion
    {α : Type*} [DecidableEq α]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ι → Finset α)
    (s : Finset ι) :
    ∑ j ∈ s, (Finset.card (B j)) =
    ∑ x ∈ (s.biUnion B), Finset.card {j | j ∈ s ∧ x ∈ B j} := by
      let r : ι → α → Prop := fun j x => x ∈ B j
      have g := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r (s := s)
        (t := s.biUnion B)
      unfold Finset.bipartiteAbove Finset.bipartiteBelow r at g
      have hB : ∀ j ∈ s, {b ∈ s.biUnion B | b ∈ B j} = B j := by grind
      have hB' : ∀ b, ({a ∈ s | b ∈ B a} : Finset ι) = ({j | j ∈ s ∧ b ∈ B j} : Finset ι) := by
        grind
      rw [Finset.sum_congr rfl (fun j hj => by rw [hB j hj])] at g
      simp [hB', g]

/-- Given a finite collection of finite subsets $B_1, \ldots, B_r$,
    each with cardinality k, if the cardinality of their union is less than r,
    then there exists an element x appearing in strictly more than k of the $B_j$'s. -/
lemma exists_larger_subset
    {n : Type*} [DecidableEq n] [Fintype n]
    {α : Type*} [DecidableEq α]
    {B : n → Finset α}
    {s : Finset n}
    {k : Nat} [nek : NeZero k]
    (h₁ : ∀ j, Finset.card (B j) = k)
    (h₂ : (s.biUnion B).card < (s.card)) :
    ∃ x ∈ s.biUnion B, k < (Finset.card {j | j ∈ s ∧ x ∈ B j}) := by
  by_contra! hc
  have hc' := Finset.sum_le_sum  (s := s.biUnion B) (ι := α)
    (f := fun x => Finset.card {j | j ∈ s ∧ x ∈ B j})
    (g := fun _ => k) (by grind)
  have : (Finset.card (s.biUnion B))*k < s.card*k :=
    Nat.mul_lt_mul_right (Nat.ne_zero_iff_zero_lt.mp nek.out) |>.mpr (by lia)
  simp at hc'
  simpa [← sum_card_eq_sum_card_fiber_biUnion B s, h₁] using Nat.lt_of_le_of_lt hc' this

lemma latin_rect_hall_property
    {α : Type*} [DecidableEq α]
    {n : Type*} [Fintype n] [DecidableEq n]
    {k : Type*} [Fintype k]
    {B : n → Finset α}
    (h₁ : Fintype.card k < Fintype.card n := by omega)
    (h₂ : ∀ j, Finset.card (B j) = Fintype.card n - Fintype.card k)
    (h₃ : ∀ x, ∀ (t : Finset n),
    Finset.card {j | j ∈ t ∧ x ∈ B j} ≤ Fintype.card n - Fintype.card k) :
    ∀ (s : Finset n), (Finset.card s) ≤ (Finset.card (s.biUnion B)) := by
  intro s
  set l := s.card with hl
  have h₁ : ∑ j ∈ s, (Finset.card (B j)) = l*(Fintype.card n - Fintype.card k) := by
    conv =>
      congr
      arg 2
      ext
      rw [h₂]
    simp [hl]
  by_contra hc
  simp only [ge_iff_le, not_le] at hc
  have _ : NeZero ((Fintype.card n) - (Fintype.card k) ) := {out := by omega}
  have hcount := exists_larger_subset h₂ hc
  obtain ⟨ x, hx ⟩ := hcount
  specialize h₃ x s
  omega

/-- For a k × n Latin rectangle, the set of entries in each column has cardinality k. -/
lemma col_card
    {k : Type*} [Fintype k]
    {n : Type*} [Fintype n]
    (A : LatinRectangle k n α) :
    ∀ j, (Finset.image (col A j) Finset.univ).card = Fintype.card k := by
  intro j
  have h_inj := A.distinct_col_entries
  exact Finset.card_image_of_injective Finset.univ (h_inj j)

lemma card_symbols_not_in
    {k : Type*} [Fintype k]
    {n : Type*} [Fintype n]
    (A : LatinRectangle k n α) :
    ∀ j, Finset.card (symbolsNotIn A j) = Fintype.card n - Fintype.card k := by
  simp [symbolsNotIn,
        Finset.card_sdiff,
        A.exactly_n_symbols,
        col_card A]

lemma row_entry_to_column_entry
    {n : Type*} [Fintype n]
    {k : Type*} [Fintype k]
    (A : LatinRectangle k n α)
    (x : α) :
    ∃ f : k → n,
    ∀ {a : k} {b : n}, LatinRectangle.M a b = x ↔ f a = b := by
  have hrow := A.once_per_row
  conv at hrow =>
    ext
    rw [Function.bijective_iff_existsUnique]
  rw [forall_swap] at hrow
  specialize hrow x
  rw [forall_existsUnique_iff] at hrow
  exact hrow

/-- Given an injective map f : k → k' such that k' has cardinality one more than k,
    there is a unique element of k' not in the image of f. -/
lemma unique_missed_element
    {k : Type*} [Fintype k]
    {k' : Type*} [Fintype k'] [DecidableEq k']
    (ι : k ↪ k')
    (h₂ : Fintype.card k' = Fintype.card k + 1) :
    ∃! x, x ∉ Finset.image ι Finset.univ := by
  have h₃pre : (Finset.image ι Finset.univ) ⊆ Finset.univ := by simp
  have h₃ := Finset.card_sdiff_of_subset h₃pre
  simp only [Finset.card_univ] at h₃
  rw [h₂] at h₃
  have h4 := Finset.card_image_of_injective Finset.univ ι.inj'
  simp only [Function.Embedding.toFun_eq_coe, Finset.card_univ] at h4
  rw [h4] at h₃
  simp only [add_tsub_cancel_left] at h₃
  rw [Finset.card_eq_one] at h₃
  rw [Finset.singleton_iff_unique_mem] at h₃
  obtain ⟨x, hx1, hx2⟩ := h₃
  use x
  dsimp
  rw [Finset.mem_sdiff] at hx1
  refine ⟨hx1.2, ?_⟩
  intro y hy
  specialize hx2 y
  dsimp at hx2
  rw [Finset.mem_sdiff] at hx2
  simp only [Finset.mem_univ, true_and] at hx2
  exact hx2 hy

/-- A non-square `LatinRectangle k n α` can be extended by one row to a new Latin rectangle. -/
theorem latin_rectangle_extends_one_row
    {n : Type*} [Fintype n]
    {k : Type*} [Fintype k] [Nonempty k]
    (A : LatinRectangle k n α)
    (h : Fintype.card k < Fintype.card n := by omega)
    {k' : Type*} [Fintype k']
    (ι : k ↪ k')
    (h₂ : Fintype.card k' = Fintype.card k + 1) :
    ∃ (A' : LatinRectangle k' n α), IsSubrect A A' := by
  classical
  let B := symbolsNotIn A
  have Bj_size (j : n) : Finset.card (B j) = (Fintype.card n) - (Fintype.card k) :=
    card_symbols_not_in A j
  have exactly_n_minus_k_cols_without_x : ∀ x,
    (Finset.card {j | x ∈ B j}) = Fintype.card n - Fintype.card k := by
    intro x
    set As : Finset (n) := {j | ∃ i, col A j i = x} with hA -- column indices with x
    set Bs : Finset (n) := {j | x ∈ B j} with hB -- column indices without x
    set Cs : Finset (k) := {i | ∃ j, row A i j = x} with hC -- row indices with x
    set Ds : Finset (k × n) := {(i, j) | A.M i j = x}
    have h := row_entry_to_column_entry A x
    obtain ⟨f, hf⟩ := h
    have f_inj : Function.Injective f := by
      unfold Function.Injective
      intro a1 a2 h₁
      have h₁' := h₁.symm
      have h₁'' := h₁
      rw [<- hf] at h₁
      rw [<- hf] at h₁'
      rw [h₁''] at h₁'
      rw [<-h₁'] at h₁
      have hinj := A.distinct_col_entries
      specialize hinj (f a2)
      simp only [Function.Injective, Matrix.col] at hinj
      exact hinj h₁
    set f' : k ↪ n := ⟨f, f_inj⟩ with hf'
    have h_Cs_card : Finset.card Cs = Fintype.card k := by
      unfold Cs
      obtain ⟨f, hf⟩ := row_entry_to_column_entry A x
      simp [hf]
    let g : Cs -> As := fun x => ⟨f' x, by
      simp only [As]
      rw [Finset.mem_def]
      simp only [Matrix.col_apply,
        Finset.filter_val,
        Multiset.mem_filter,
        Finset.mem_val,
        Finset.mem_univ,
        true_and]
      use x
      rw [hf,<- Function.Embedding.toFun_eq_coe]⟩
    have ginj : Function.Injective g := by
      simp [Function.Injective,g]
    have gsurj : Function.Surjective g := by
      have As_is_f_image : As = Finset.image f Finset.univ := by
        unfold As
        ext b
        simp only [Matrix.col_apply,
                   Finset.mem_image,
                   Finset.mem_filter,
                   Finset.mem_univ,
                   true_and]
        constructor
        · intro h
          obtain ⟨ i, hi ⟩ := h
          rw [hf] at hi
          use i
        · intro h
          obtain ⟨ i, hi ⟩ := h
          rw [<-hf] at hi
          use i
      unfold Function.Surjective
      unfold g
      simp only [Subtype.exists, Subtype.forall, Subtype.mk.injEq, exists_prop]
      rw [As_is_f_image]
      simp only [f']
      intro x'
      rw [Finset.mem_image]
      intro ha
      have h := A.once_per_row
      obtain ⟨a, ha⟩ := ha
      use a
      refine ⟨ ?_, ha.2 ⟩
      simp only [Matrix.row_apply, Finset.mem_filter, Finset.mem_univ, true_and, Cs]
      have h' := (h a).2
      unfold Matrix.row at h'
      simp only [Function.Surjective] at h'
      specialize h' x
      exact h'
    have gbij : Function.Bijective g := ⟨ginj,gsurj⟩
    let As_to_Cs : Cs ≃ As := Equiv.ofBijective g gbij
    have h_As_card : Finset.card As = Fintype.card k := by
      rw [<- h_Cs_card]
      exact Finset.card_eq_of_equiv As_to_Cs.symm
    have h_intersect : As ∩ Bs = ∅ := by
      ext
      simp [As, Bs, B, symbolsNotIn]
    have h_union_card : Finset.card (As ∪ Bs) = Fintype.card n := by
      congr
      simp only [As, Bs, B, symbolsNotIn]
      ext
      simp [exists_or_forall_not]
    have h_card := Finset.card_union As Bs
    simp [h_union_card, h_As_card, h_intersect] at h_card
    omega
  have pre_property_H : ∀ x, ∀ (t : Finset n),
    (Finset.card {j | j ∈ t ∧ x ∈ B j}) ≤ Fintype.card n - Fintype.card k := by
    intro x t
    have h : ({j | j ∈ t ∧ x ∈ B j} : Finset n) ⊆ ({j | x ∈ B j} : Finset n) := by
      simp [Finset.subset_iff]
    have h' := Finset.card_le_card (s := {j | j ∈ t ∧ x ∈ B j}) (t := {j | x ∈ B j})
    have hx := exactly_n_minus_k_cols_without_x x
    rw [hx] at h'
    exact h' h
  let halls := hallMatchingsOn.nonempty (B)
    (latin_rect_hall_property h Bj_size pre_property_H) (Finset.univ)
  set f := Classical.choice halls with hx
  simp only [hallMatchingsOn] at f
  obtain ⟨ f', hf⟩ := f
  let M' : k' → n → α := fun i j =>
    if hif : i ∈ (Finset.image ι Finset.univ)
    then A.M (Function.invFun ι i) j
    else (f' ⟨j, by simp⟩ )
  let A' : LatinRectangle k' n α := {
    M := M'
    exactly_n_symbols := A.exactly_n_symbols
    once_per_row := by
      simp only [Matrix.row, M']
      intro y
      split_ifs
      · rename_i if_h₁
        rw [Finset.mem_image] at if_h₁
        obtain ⟨a1', ha1' ⟩ := if_h₁
        simp only [Finset.mem_univ, true_and] at ha1'
        rw [<- ha1']
        have h₁' := Function.leftInverse_invFun ι.inj'
        simp only [Function.Embedding.toFun_eq_coe] at h₁'
        rw [h₁']
        have h := A.once_per_row
        simp only [Matrix.row] at h
        apply h
      · simp only [Subtype.forall, Finset.mem_univ, forall_true_left, Set.mem_setOf_eq] at hf
        have h₂ := A.exactly_n_symbols.symm
        have h₃pre : Fintype.card ↥(Finset.univ : Finset n) = Fintype.card α := by simp[h₂]
        have h₃ : (Function.Injective f') ∧ (Fintype.card Finset.univ = Fintype.card α) :=
                  ⟨hf.1, h₃pre⟩
        rw [<-Fintype.bijective_iff_injective_and_card] at h₃
        simp only [Function.Bijective]
        constructor
        · simp only [Function.Injective]
          intro a1 a2 h
          apply hf.1 at h
          simp only [Subtype.mk.injEq] at h
          exact h
        · simp only [Function.Surjective]
          intro b
          simp only [B, symbolsNotIn] at hf
          unfold Function.Bijective Function.Surjective at h₃
          replace h₃ := h₃.2
          specialize h₃ b
          simp only [Subtype.exists, Finset.mem_univ, exists_true_left] at h₃
          exact h₃
    distinct_col_entries := by
      intro y
      simp only [Function.Injective, Matrix.col, Matrix.transpose,
                 Finset.mem_image, Finset.mem_univ, true_and,
    dite_eq_ite, Matrix.of_apply, M']
      intro a1 a2
      split_ifs
      all_goals rename_i if_h₁ if_h₂
      · obtain ⟨a1', ha1' ⟩ := if_h₁
        have h₁' := Function.leftInverse_invFun ι.inj'
        simp only [Function.Embedding.toFun_eq_coe] at h₁'
        rw [<- ha1',h₁']
        obtain ⟨a2', ha2' ⟩ := if_h₂
        have h₂' := Function.leftInverse_invFun ι.inj'
        simp only [Function.Embedding.toFun_eq_coe] at h₂'
        rw [<- ha2',h₂']
        have h := A.distinct_col_entries
        unfold Function.Injective at h
        intro hM
        apply h at hM
        congr
      · simp only [Subtype.forall, Finset.mem_univ, forall_true_left, Set.mem_setOf_eq] at hf
        intro h
        have hfy := hf.2 y
        simp only [symbolsNotIn, Finset.mem_sdiff, Finset.mem_univ,
                   Finset.mem_image, Matrix.col_apply, true_and, not_exists, B] at hfy
        have hfyi := hfy (Function.invFun (⇑ι) a1)
        contradiction
      · intro h
        simp only [Subtype.forall, Finset.mem_univ, forall_true_left, Set.mem_setOf_eq] at hf
        have hfy := hf.2 y
        simp only [symbolsNotIn, Finset.mem_sdiff, Finset.mem_univ,
                   Finset.mem_image, Matrix.col_apply, true_and, not_exists, B]  at hfy
        have hfyi := (hfy (Function.invFun (⇑ι) a2))
        have h := h.symm
        contradiction
      · rename_i if_h₁ if_h₂
        -- Here the f drops out and it really is about ι and cards
        -- If a1 and a2 aren't in the image of ι and
        -- card codomain of ι = card domain of ι + 1 then
        -- both a1 and a2 are the unique element ι misses.
        have h := unique_missed_element ι h₂
        simp only [Finset.mem_image] at h
        intro _
        exact ExistsUnique.unique (y₁ := a1) (y₂ := a2) h
          (by simpa using if_h₁) (by simpa using if_h₂)
    m_le_n := by omega
  }
  use A'
  unfold IsSubrect
  unfold LatinRectangle.M
  simp only [A', M']
  use ι
  use (Equiv.refl n)
  use (Equiv.refl α)
  intro i j
  rw [<-Function.comp_apply (f := Function.invFun ι)]
  rw [Function.invFun_comp ι.injective]
  simp
  rfl

/-- Being a subrectangle of a `LatinRectangle` is a transitive property. -/
lemma IsSubrect.trans {m'' : Type*} [Fintype m'']
    {n : Type*} [Fintype n]
    {A : LatinRectangle m n α}
    {A' : LatinRectangle m' n α}
    {A'' : LatinRectangle m'' n α}
    (h₁ : IsSubrect A A')
    (h₂ : IsSubrect A' A'') :
    IsSubrect A A'' := by
  unfold IsSubrect at *
  obtain ⟨f,g,h,h₁⟩ := h₁
  obtain ⟨f',g',h',h₂⟩ := h₂
  set f'' := Function.Embedding.trans f f'
  set g'' := Function.Embedding.trans g g'
  set h'' := Equiv.trans h h'
  use f'', g'', h''
  simp [h'', f'', g'',h₂,h₁]

/-- Any two equivalent `LatinRectangle`s are subrectangles of each other. -/
lemma subrect_refl
    {n : Type*} [Fintype n]
    {A : LatinRectangle m n α}
    {A' : LatinRectangle m' n α} (h : A ≃ A') :
    IsSubrect A A' := by
  obtain ⟨f,g,h,hrfl⟩ := h
  simp only [IsSubrect]
  exact ⟨f, g, h, hrfl⟩

/-- A Latin rectangle `LatinRectangle m n α` extends to a Latin square `LatinSquare n α`.
    In other words, there always exists a Latin square that contains a given Latin rectangle
    as a substructure. -/
theorem latin_rectangle_extends_to_latin_square
    {n : Type*} [Fintype n]
    {k : Type*} [Fintype k] [Nonempty k]
    (A : LatinRectangle k n α)
    (h : Fintype.card k ≤ Fintype.card n := by omega) :
    ∃ (A' : LatinRectangle n n α), IsSubrect A A' := by
  induction h_gap : (Fintype.card n - Fintype.card k) using
    Nat.strong_induction_on generalizing k A with
  | h a ih =>
    by_cases h_full : Fintype.card k = Fintype.card n
    · let f : k ≃ n := Fintype.equivOfCardEq h_full
      let A' := renameLatinRectangle f (Equiv.refl n) (Equiv.refl α) A
      have h_sim : A ≃ A' := by
        simp [induced_latin_rectangle_is_equiv f (Equiv.refl n) (Equiv.refl α) A,A']
      use A'
      exact subrect_refl h_sim
    · set k' := Option k with hk'
      letI : Fintype k' := (inferInstance : Fintype (Option k))
      have hk'_card := Fintype.card_option (α := k)
      replace hk' := hk'.symm
      simp only [hk'] at hk'_card
      have hk'_le : Fintype.card k ≤ Fintype.card k' := by omega
      have h_k_lt_n : Fintype.card k < Fintype.card n := by omega
      have h_k'_le_n : Fintype.card k' ≤ Fintype.card n := by omega
      set m := Fintype.card n - Fintype.card k' with hm
      have hm_lt : m < a := by omega
      have ι_h := Function.Embedding.nonempty_of_card_le hk'_le
      let ι' : k ↪ k' := Classical.choice ι_h
      have H := latin_rectangle_extends_one_row A h_k_lt_n ι' hk'_card
      have ⟨A', hA⟩ := H
      have ih := ih m hm_lt (k := k') (A := A') h_k'_le_n hm
      have ⟨A'', hA''⟩ := ih
      exact ⟨A'', hA.trans hA''⟩

end Completion

end LatinSquare
