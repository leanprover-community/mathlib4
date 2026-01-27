/-
Copyright (c) 2026 Christopher J. R. Lloyd and George H. Seelinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher J. R. Lloyd, George H. Seelinger
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.Hall.Basic
import Mathlib

/-!
# LatinSquare

Description of Latin Squares

## Main definitions

## Main results

## TODO

* Add theorem that a k-1 × n Latin rectangle can be extended to a k × n Latin rectangle.
* Corollary, any k x n Latin rectangle can be extneded to a Latin square.
* Add that a n x n Latin rectangle is a Latin square.
  This will lead to a computable definition of Latin square.
* Add Ryser's theorem using partial Latin squares.
* Add Evan's Conjeture.
* Add isomorphism to quasigroups.
* Add isomorphism to orthogonal arrays of triples.

## References

* [vanLint, Wilson, *A Course in Combinatorics*, Chapter 17][vanlint_wilson2001]

-/

universe u u' v

variable {m m' : Type u} [Fintype m] [Fintype m'] --[DecidableEq α]
variable {n n' : Type u'} [Fintype n] [Fintype n']--[DecidableEq α]
variable {α β : Type v} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

section LatinSquare


-- abbrev symbols (M : Fin m → Fin n → α) : Finset α :=
--   (Finset.image fun (x,y) ↦ M x y) Finset.univ

-- abbrev exactly_n_symbols (M : Fin m → Fin n → α) :=
--   (symbols M).card = n

abbrev once_per_row (M : Matrix m n α) : Prop :=
  -- ∀ i : m, ∀ y : α, ∃! j: n, M i j = y
  ∀ i, Function.Bijective (M.row i)

abbrev distinct_col_entries (M : Matrix m n α) : Prop :=
  -- ∀ y : n, ∀ x₁ x₂ : m, x₁ ≠ x₂ → M x₁ y ≠ M x₂ y
  ∀ y, Function.Injective (M.col y)

abbrev distinct_row_entries (M : Matrix m n α) : Prop :=
  -- ∀ x : m, ∀ y₁ y₂ : n, y₁ ≠ y₂ → M x y₁ ≠ M x y₂
  ∀ y, Function.Injective (M.row y)

/-- For m ≤ n, an m × n Latin rectangle is a partial n × n Latin Square where
    the first m entries are filled. -/
class LatinRectangle (m : Type u) (n : Type u') (α : Type v)
  [Fintype m] [Fintype n] [Fintype α] [DecidableEq α] where
  /-- An m × n array of symbols. -/
  M : Matrix m n α
  /-- An $m × n$ Latin rectangle contains $n$ distinct entries. -/
  exactly_n_symbols : Fintype.card α = Fintype.card n
  /-- Each row contains each symbol exactly once. -/
  once_per_row : once_per_row M
  /-- Entries cannot repeat in a given column. -/
  distinct_col_entries : distinct_col_entries M
  m_le_n : Fintype.card m ≤ Fintype.card n := by simp

-- Pretty printing of rectangles
instance {m n : Nat} {α : Type u} [DecidableEq α] [Fintype α] [ToString α] :
  Repr (LatinRectangle (Fin m) (Fin n) α) where
    reprPrec L _ :=
      let row (i : Fin m) :=
        String.intercalate " " (List.ofFn (fun j => (toString (L.M i j))));
      String.intercalate "\n" (List.ofFn row)

abbrev once_per_column (M : Matrix m n α) : Prop :=
  -- ∀ j : n, ∀ x : α, ∃! i : m, M i j = x
  ∀ j, Function.Bijective (M.col j)

lemma latin_square_col_implies_latin_rectangle_col
  (M : Matrix n n α)
  (h₂ : once_per_column M) :
  distinct_col_entries M := by
    rw [once_per_column] at h₂ 
    rw [distinct_col_entries]
    intro j
    specialize h₂ j
    exact h₂.1

/-- A LatinSquare is an n × n array containing exactly n symbols,
    each occurring exactly once in each row and exactly once in each column. -/
class LatinSquare (n : Type u) (α : Type v) [Fintype n] [Fintype α] [DecidableEq α]
  extends LatinRectangle n n α where
  /-- Each column contains each symbol exactly once. -/
  once_per_column : once_per_column M
  /-- If each column contains each symbol exactly once, then there are no repeats across columns. -/
  distinct_col_entries := latin_square_col_implies_latin_rectangle_col M once_per_column 

  m_le_n := by rfl
  
@[coe]
abbrev to_matrix : (LatinRectangle m n α) → (Matrix m n α)
 | A => A.M

instance {m : Type u} {n : Type u'} {α : Type v} [Fintype m] 
  [Fintype n] [Fintype α] [DecidableEq α] : 
  Coe (LatinRectangle m n α) (Matrix m n α) where
  coe := to_matrix

instance {n : Type u'} {α : Type v}
  [Fintype n] [Fintype α] [DecidableEq α] : 
  Coe (LatinSquare n α) (LatinRectangle n n α) where
  coe := fun A => A.toLatinRectangle

abbrev col (A : LatinRectangle m n α) : n → m → α := Matrix.col A
abbrev row (A : LatinRectangle m n α) : m → n → α := Matrix.row A
  
@[coe]
def lr_to_ls : (LatinRectangle n n α) → (LatinSquare n α) 
  | A => {
      M := A.M,
      exactly_n_symbols := A.exactly_n_symbols,
      once_per_row := A.once_per_row,
      m_le_n := A.m_le_n,
      once_per_column := by 
        unfold once_per_column 
        have h := A.distinct_col_entries
        unfold distinct_col_entries at h
        intro j
        specialize h j
        rw [Fintype.bijective_iff_injective_and_card]
        refine ⟨h, ?_⟩
        exact A.exactly_n_symbols.symm
      }

instance : Coe (LatinRectangle n n α) (LatinSquare n α) where 
  coe := lr_to_ls

theorem lr_as_ls_as_lr_is_eq (A : LatinRectangle n n α) :
  ((A : LatinSquare n α ) : LatinRectangle n n α) = A := by 
     simp[LatinSquare.toLatinRectangle, lr_to_ls]
     
theorem ls_as_lr_as_ls_is_eq (A : LatinSquare n α) :
  ((A : LatinRectangle n n α) : LatinSquare n α) = A := by
      simp[lr_to_ls, LatinSquare.toLatinRectangle]

instance {n : Nat} {α : Type v} [DecidableEq α] [Fintype α] [ToString α] :
  Repr (LatinSquare (Fin n) α) where
    reprPrec L prec := Repr.reprPrec L.toLatinRectangle prec


/-- Every Finite Group's Cayley table is an example of a Latin Square. -/
@[to_additive]
def group_to_cayley_table (G : Type*) [DecidableEq G] [Group G] [Fintype G] :
  LatinSquare G G := {
    M := fun i j ↦ i * j,
    exactly_n_symbols := by rfl,
    once_per_row := by
      simp only [once_per_row, Matrix.row] 
      exact Group.mulLeft_bijective (G := G),
    once_per_column := by
      simp only [once_per_column, Matrix.col]
      exact Group.mulRight_bijective (G := G)
   }

#check col (addGroup_to_cayley_table (ZMod 5) : LatinRectangle (ZMod 5) (ZMod 5) (ZMod 5))

def latin_rectangle_isomorphism
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
  once_per_row := by 
    simp only [once_per_row, Matrix.row]
    have h' := A.once_per_row
    simp only [once_per_row, Matrix.row] at h'
    intro i'
    specialize h' (f.symm i') --(h.symm b')
    have h_comp : 
      (fun j' ↦ h (LatinRectangle.M (f.symm i') (g.symm j'))) = 
      h ∘ (LatinRectangle.M (f.symm i')) ∘ g.symm := by 
      ext
      simp
    rw [h_comp]
    apply Function.Bijective.comp
    · exact Equiv.bijective h
    · apply Function.Bijective.comp
      · exact h'
      · exact Equiv.bijective g.symm,
  distinct_col_entries := by 
    simp only [distinct_col_entries, Matrix.col]
    have h' := A.distinct_col_entries 
    simp only [distinct_col_entries, Matrix.col] at h'
    intro j'
    specialize h' (g.symm j')
    have h_comp : 
      (Matrix.transpose (fun i' j' ↦ h (LatinRectangle.M (f.symm i') (g.symm j'))) j') = 
      h ∘ (LatinRectangle.M.transpose (g.symm j')) ∘ f.symm := by 
      ext
      simp
    rw [h_comp]
    apply Function.Injective.comp
    · exact (Equiv.bijective h).1
    · apply Function.Injective.comp
      · exact h'
      · exact (Equiv.bijective f.symm).1,
  m_le_n := by 
    have ineq := A.m_le_n
    have f' : Fintype.card m = Fintype.card m' := Fintype.card_congr f
    have g' : Fintype.card n = Fintype.card n' := Fintype.card_congr g
    omega
  }
  
def latin_square_isomorphism
  (f : n ≃ n')
  (g : n ≃ n')
  (h : α ≃ β)
  (A : LatinSquare n α) : 
  LatinSquare n' β := latin_rectangle_isomorphism f g h (A : LatinRectangle n n α)

-- Cyclic Example
-- We construct an infinite family of Latin Squares from the infinite family of Cyclic Groups

-- For example, addGroup_to_cayley_table (ZMod.finEquiv 5).toEquiv

instance nonempty {n : Nat} [NeZero n] : LatinSquare (ZMod n) (ZMod n) :=
  addGroup_to_cayley_table (ZMod n)
  
-- #check Matrix.transpose (addGroup_to_cayley_table (ZMod 5) : Matrix (ZMod 5) (ZMod 5) (ZMod 5))

section Isotopy

structure LatinSquareIsotopy
  (L₁ : LatinSquare n α)
  (L₂ : LatinSquare n' β)
  where
    symbol_map : α ≃ β
    reindex_row : n' ≃ n
    reindex_col : n' ≃ n
    intertwine : ∀ i, ∀ j, symbol_map (L₁.M (reindex_row i) (reindex_col j)) = L₂.M i j

def reflLatinSquareIsotopy
  (L : LatinSquare n α) : LatinSquareIsotopy L L := {
    symbol_map := Equiv.refl α,
    reindex_row := Equiv.refl n,
    reindex_col := Equiv.refl n,
    intertwine := by simp
  }

end Isotopy

section Completion

variable {n : Type u'} [Fintype n] [Nonempty n]
variable {k : Type u} [Fintype k] [Nonempty k]

def is_subrect
  (A : LatinRectangle m n α)
  (B : LatinRectangle m' n' α)
  (i₁ : m ↪ m')
  (i₂ : n ↪ n') :=
  ∀ (i : m), ∀ (j : n), A.M i j = B.M (i₁ i) (i₂ j)


def symbols_in
 (A : LatinRectangle k n α) (j : n) :=
  let D := Finset.image (col A j) Finset.univ
  D

def symbols_not_in
 (A : LatinRectangle k n α) (j : n) :=
  let D := Finset.image (col A j) Finset.univ
  Finset.univ \ D
  
-- lemma symbols_in_count
--  (A : LatinRectangle k n α) (j : n) : 
--    Nonempty (symbols_in A j ≃ k) := by sorry
 
-- lemma symbols_in_and_not_in_disjoint 
-- {k n : Nat} [NeZero k] [NeZero n]
--  (A : LatinRectangle k n α) (j : Fin n) : 
--  (symbols_in A j) ∩ (symbols_not_in A j) = ∅ := by sorry

lemma count_by_group_or_element_indicator
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (B : ι → Finset α)
  (s : Finset ι)
  : ∑ j ∈ s, (Finset.card (B j)) =
  ∑ x ∈ (s.biUnion B), Finset.card {j | j ∈ s ∧ x ∈ B j} := by
    let E : Finset (ι × (s.biUnion B)) := {b | b.1 ∈ s ∧ ↑(b.2) ∈ (B b.1)}
    let amb : E → ι × (s.biUnion B) := fun b => (b : ι × (s.biUnion B))
    let p1 : E → ι := Prod.fst ∘ amb
    have hp1 : Set.MapsTo p1 (Finset.univ : Finset E) (Finset.univ : Finset ι) := by simp
    have h1 := Finset.card_eq_sum_card_fiberwise hp1
    have j_not_in_s_zero_summand : ∀ j ∈ sᶜ, Finset.card {a | p1 a = j} = 0 := by
      intro j hjc
      rw [Finset.card_eq_zero]
      ext b
      constructor
      · intro hm
        simp at hm
        simp [p1,amb] at hm
        have hb := b.property
        simp only [E] at hb
        rw [Finset.mem_def] at hb
        simp at hb
        have hj := hb.1
        rw [hm] at hj
        simp at hjc
        contradiction
      · simp
    have s_s_complement_disj : Disjoint s (sᶜ) := by
      simp [Disjoint]
      intro x hx hxc
      have h := Finset.subset_inter hx hxc
      simp at h
      exact h
    have h1_split := Finset.sum_union s_s_complement_disj (f := fun j => Finset.card {a | p1 a = j})
    replace j_not_in_s_zero_summand := Finset.sum_congr (by rfl) j_not_in_s_zero_summand
    conv at j_not_in_s_zero_summand =>
      rhs
      simp
    rw [j_not_in_s_zero_summand] at h1_split
    simp at h1_split
    simp at h1
    rw [h1_split] at h1
    have p1_im : ∀ j ∈ s, {a | p1 a = j} ≃ B j := by
      intro j hj
      refine ⟨fun x => ⟨x.val.1.2.val, by
                have h := x.val.property
                unfold E at h
                rw [Finset.mem_def] at h
                simp at h
                replace h := h.right
                have j' := x.property
                dsimp [p1,amb] at j'
                rw [j'] at h
                exact h⟩,
              fun x => ⟨⟨(j, ⟨x.val, by
                have h := x.property
                rw [Finset.mem_biUnion]
                use j ⟩), by simp [E]; exact hj ⟩,
              by simp [p1,amb]⟩,
              ?left_inv,
              ?right_inv⟩
      · simp [Function.LeftInverse]
        intros _ _ _ _ _ _ hp1
        simp [p1,amb] at hp1
        exact hp1.symm
      · simp [Function.RightInverse, Function.LeftInverse]
    have h1'set : ∀ j ∈ s, Finset.card {a | p1 a = j} = (B j).card := by
      intro j hj
      specialize p1_im j hj
      simp at p1_im
      apply Finset.card_eq_of_equiv
      simp
      exact p1_im
    have h1'' := Finset.sum_congr (by rfl) h1'set
      (f := fun j => Finset.card {a | p1 a = j}) (g := fun j => Finset.card (B j))
    rw [←h1'']
    simp
    rw [←h1]
    -- Second half is E.card
    clear h1 h1'' hp1 h1_split p1_im h1'set s_s_complement_disj j_not_in_s_zero_summand
    let p2 : E → s.biUnion B := Prod.snd ∘ amb
    have hp2 : Set.MapsTo p2 (Finset.univ : Finset E)
      (Finset.univ : Finset (s.biUnion B)) := by simp
    have h2 := Finset.card_eq_sum_card_fiberwise hp2
    have h2' : ∀ x ∈ (s.biUnion B), {a | p2 a = x} ≃ {j | j ∈ s ∧ ↑x ∈ B j} := by
      intro x hx
      simp [p2,amb]
      refine ⟨fun a => ⟨a.val.val.1, by
                have h := a.val.property
                unfold E at h
                rw [Finset.mem_def] at h
                simp at h
                have a' := a.property
                rw[a'] at h
                exact h⟩,
              fun j => ⟨⟨(j.val, ⟨x,hx⟩), by
                simp[E]
                exact j.property⟩, by simp⟩, ?_, ?_⟩
      · simp[Function.LeftInverse]
        intro _ _ _ _ _ _ ha
        exact ha.symm
      · simp[Function.RightInverse, Function.LeftInverse]
    have h2'set : ∀ x ∈ (s.biUnion B),
      Finset.card {a | p2 a = x} = Finset.card {j | j ∈ s ∧ ↑x ∈ B j} := by
        intro x hx
        apply Finset.card_eq_of_equiv
        specialize h2' x hx
        simp at h2'
        simp
        exact h2'
    have h2'' := Finset.sum_congr
      (s₁ := s.biUnion B) (s₂ := s.biUnion B) (by rfl) h2'set
      (f := fun x => Finset.card  {a | p2 a = x})
      (g := fun x => Finset.card  {j | j ∈ s ∧ ↑x ∈ B j})
    rw [←h2'']
    simp
    simp at h2
    have hfin : ∑ x ∈ (s.biUnion B).attach, {a ∈ E.attach | p2 a = x}.card =
                ∑ x ∈ s.biUnion B, {a ∈ E.attach | ↑(p2 a) = x}.card := by
         have h := Finset.sum_attach (s.biUnion B) (fun x => {a ∈ E.attach | p2 a = x}.card )
         rw [<- h]
         congr
         ext x
         congr
         ext a
         rw [SetCoe.ext_iff]
    rw[← hfin]
    exact h2

lemma exists_larger_subset
  {B : Fin n → Finset α}
  {s : Finset (Fin n)}
  {k : Nat} [nek : NeZero k]
  (h₁ : ∀ j, Finset.card (B j) = k)
  (h₂ : (s.biUnion B).card < (s.card)) :
      ∃ x ∈ s.biUnion B, k < (Finset.card {j | j ∈ s ∧ x ∈ B j}) := by
      by_contra hc
      simp at hc
      have pullback : ∀ i ∈ (s.biUnion B),
        ∃ x, ∀ j, (j ∈ s ∧ i ∈ B j) ↔ (j ∈ s ∧ x ∈ B j) := by
          intro i hi
          use i
          simp
      have hc' : (∀ i ∈ s.biUnion B, Finset.card {j | j ∈ s ∧ i ∈ B j} ≤ k) := by
        intro i
        intro h
        have h' := hc i
        rw [ Finset.mem_biUnion ] at h
        obtain ⟨ a, i ⟩ := h
        specialize h' a
        specialize h' i.left
        specialize h' i.right
        exact h'
      have g := Finset.sum_le_sum  (s := s.biUnion B) (ι := α)
        (f := fun x => Finset.card {j | j ∈ s ∧ x ∈ B j})
        (g := fun _ => k)
      apply g at hc'
      simp at hc'
      have _ : 0 < k := by
        have _ := nek.out
        omega
      have _ : (Finset.card (s.biUnion B))*k < s.card*k := by
        rw [Nat.mul_lt_mul_right]
        omega
        assumption
      replace hc' : ∑ i ∈ s.biUnion B, Finset.card {j | j ∈ s ∧ i ∈ B j} < (s.card) * k := by omega
      have h' : ∑ j ∈ s, (Finset.card (B j)) =
        ∑ x ∈ (s.biUnion B), Finset.card {j | j ∈ s ∧ x ∈ B j} :=
        count_by_group_or_element_indicator B s
      rw[←h'] at hc'
      simp[h₁] at hc'


lemma latin_rect_hall_property
  {k n : Nat} [NeZero k] [NeZero n]
  {B : Fin n → Finset α}
  (h1 : k < n := by omega)
  (h2 : ∀ j, Finset.card (B j) = n - k)
  (h3 : ∀ x, ∀ (t : Finset (Fin n)), Finset.card {j | j ∈ t ∧ x ∈ B j} ≤ n - k) :
  ∀ (s : Finset (Fin n)), (Finset.card s) ≤ (Finset.card (s.biUnion B)) := by
    intro s
    set l := s.card with hl
    have h1 : ∑ j ∈ s, (Finset.card (B j)) = l*(n-k) := by
      conv =>
        congr
        arg 2
        ext j
        rw [h2]
      simp [hl]
    by_contra hc
    simp at hc
    have _ : NeZero (n-k) := {out := by omega}
    have hcount := exists_larger_subset h2 hc
    obtain ⟨ x, hx ⟩ := hcount
    specialize h3 x s
    omega

lemma col_map_in_symbols
    {k n : Nat} [NeZero k] [NeZero n]
    (A : LatinRectangle k n α) :
    ∀ j, (Finset.image (col_map A j) Finset.univ) ∩ (symbols A.M) 
     = (Finset.image (col_map A j) Finset.univ) := by 
     intro j
     unfold col_map symbols
     simp [Finset.inter_eq_left, Finset.subset_iff]

lemma col_injective
    {k n : Nat} [NeZero k] [NeZero n]
    (A : LatinRectangle k n α)
    (h : k < n := by omega) :
    ∀ j, Function.Injective (col_map A j) := by 
    have h_col := A.distinct_col_entries
    unfold distinct_col_entries at h_col
    unfold Function.Injective col_map
    intro j a1 a2
    specialize h_col j a1 a2
    replace h_col := h_col.mt
    simp at h_col
    exact h_col

lemma col_card
    {k n : Nat} [NeZero k] [NeZero n]
    (A : LatinRectangle k n α)
    (h : k < n := by omega) :
    ∀ j, (Finset.image (col_map A j) Finset.univ).card = k := by 
    intro j
    have h_inj := col_injective A h j
    simp [Finset.card_image_of_injective Finset.univ h_inj]
    

lemma card_symbols_not_in
  {k n : Nat} [NeZero k] [NeZero n]
    (A : LatinRectangle k n α)
    (h : k < n := by omega) :
  ∀ j, Finset.card (symbols_not_in A j) = n - k := by
    simp [symbols_not_in,
          Finset.card_sdiff, 
          A.exactly_n_symbols,
          col_map_in_symbols,
          col_card A]

lemma row_entry_to_column_entry
  {k n : Nat} [NeZero k] [NeZero n]
    (A : LatinRectangle k n α)
    (x : α)
    (h : k < n := by omega) :
    ∃ f : Fin k → Fin n, 
    ∀ {a : Fin k} {b : Fin n}, LatinRectangle.M a b = x ↔ f a = b := by
      have hrow := A.once_per_row
      unfold once_per_row at hrow
      rw[forall_swap] at hrow
      specialize hrow x
      have hx : x ∈ symbols A.M := by sorry -- garbage only for sake of argument
      rw [← imp_forall_iff] at hrow
      specialize hrow hx
      rw [ forall_existsUnique_iff] at hrow
      exact hrow

-- TODO Rewrite in terms of new definition!
theorem latin_rectangle_extends
  {k n : Nat} [NeZero k] [NeZero n]
    (A : LatinRectangle k n α)
    (h : k < n := by omega) :
    ∃ (A' : LatinRectangle (k + 1) n α), is_subrect A A' := by
  let B := symbols_not_in A
  have Bj_size (j : Fin n) : Finset.card (B j) = n-k := 
    card_symbols_not_in A h j
  have Bj_characterized (j : Fin n) (x : α) : x ∈ B j ↔ ¬ (∃ i, A.M i j = x)  := by sorry
  have exactly_n_minus_k_cols_without_x : ∀ x, (Finset.card {j | x ∈ B j}) = n-k := by 
    -- Uses properties of latin rectangle
    -- intro x
    -- conv =>
    --   lhs
    --   congr
    --   congr
    --   ext j
    --   rw [Bj_characterized j]

    intro x
    set As : Finset (Fin n) := {j | ∃ i, A.M i j = x} with hA
    set Bs : Finset (Fin n) := {j | x ∈ B j} with hB
    set Cs : Finset (Fin k) := {i | ∃ j, A.M i j = x} with hC
    set Ds := {(i,j) | A.M i j = x} with hD
    have h := row_entry_to_column_entry A x
    obtain ⟨f, hf⟩ := h
    have h_Cs_card : Finset.card Cs = k := by
      unfold Cs
      obtain ⟨f, hf⟩ := row_entry_to_column_entry A x
      simp [hf]
    have h_Cs_bij_h_Bs : Cs ≃ Bs := by
      refine ⟨?toF, ?invF, ?_, ?_⟩ 
      · exact fun i => ⟨f i, sorry⟩
      · exact fun p => ⟨p.fst, sorry⟩ 
      · sorry
      · sorry
    have h_As_card : Finset.card As = k := by 
      unfold As
      have hrow := A.once_per_row
      unfold once_per_row at hrow
      have hcol := A.distinct_col_entries
      unfold distinct_col_entries at hcol
      
      sorry
    -- have h_union : As ∪ Bs = Fin n := by sorry
    have h_union_card : Finset.card (As ∪ Bs) = n := by sorry
    have h_intersect : As ∩ Bs = ∅ := by 
      ext
      sorry
      
    have h_card := Finset.card_union As Bs
    simp [h_union_card, h_As_card, h_intersect] at h_card
    omega
    -- There are n-k columns that do not have an x


  have pre_property_H : ∀ x, ∀ (t : Finset (Fin n)),
    (Finset.card {j | j ∈ t ∧ x ∈ B j}) ≤ n-k := by
    intro x t
    have h : ({j | j ∈ t ∧ x ∈ B j} : Finset (Fin n)) ⊆ ({j | x ∈ B j} : Finset (Fin n)) := by
      simp [Finset.subset_iff]
    have h' := Finset.card_le_card (s := {j | j ∈ t ∧ x ∈ B j}) (t := {j | x ∈ B j}) 
    have hx := exactly_n_minus_k_cols_without_x x
    simp at hx
    rw[hx] at h'
    exact h' h

  let halls := hallMatchingsOn.nonempty (B)
    (latin_rect_hall_property h Bj_size pre_property_H) (Finset.univ)
  set f := Classical.choice halls with hx
  simp [hallMatchingsOn] at f
  obtain ⟨ f', hf⟩ := f
  let M' : Fin (k+1) → (Fin n) → α := fun i j =>
    if hif : i < k then A.M ⟨i, hif⟩ j else (f' ⟨j, by simp⟩ )
  let A' : LatinRectangle (k+1) n α := {
    M := M'
    exactly_n_symbols := sorry
    once_per_row := sorry
    distinct_col_entries := sorry
    m_le_n := by omega
  }
  use A'
  unfold is_subrect
  unfold LatinRectangle.M
  simp[A', M']
  intro i j
  rfl

end Completion

end LatinSquare
