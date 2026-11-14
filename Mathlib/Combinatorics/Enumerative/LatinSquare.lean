/-
Copyright (c) 2026 Christopher J. R. Lloyd and George H. Seelinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher J. R. Lloyd, George H. Seelinger
-/
module

public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Latin Squares

A Latin rectangle is an `m × n` matrix filled with `n` different
symbols such that each symbol occurs exactly once in each row and
occurs at most once in each column.  When `m = n`, the column
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

A classical result in combinatorics, **Hall's Marriage Theorem**, can be used to show that any
Latin rectangle can be extended to a Latin square; this theorem is formalized as
`latin_rectangle_extends_to_latin_square`.

## Main results

- `group_to_cayley_table`: every finite group `G` yields a `LatinSquare G G`.
- `LatinRectangle.exists_extension_of_non_square_LatinRectangle`: a (non-square) `LatinRectangle`
   extends to a `LatinRectangle` with one more row. This is an application of
  **Hall's Marriage Theorem**, `hallMatchingsOn.nonempty`.
- `LatinRectangle.exists_LatinSquare_of_LatinRectangle`: a `LatinRectangle`
  extends to a `LatinSquare`.

## Notation

- `≃` : The type of equivalences between `LatinRectangle`s.

## TODO

* Add Ryser's theorem using partial Latin squares.
* Add Evan's Conjeture.
* Add isomorphism to quasigroups.
* Add isomorphism to orthogonal arrays of triples.
* Add decidablity reductions to the LS definitions

## References

* [Euler, *Recherches sur une nouvelle espèce de quarrés magiques*][euler1782]
* [van Lint, Wilson, *A Course in Combinatorics* (Chapter 17)][vanlint_wilson2001]
-/

variable {m m' : Type*} [Fintype m] [Fintype m']
variable {n n' : Type*} [Fintype n] [Fintype n']
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

@[expose] public section

/-- For `m ≤ n`, an `m × n` Latin rectangle is a partial `n × n` Latin Square where
    the first `m` entries are filled. -/
class LatinRectangle (m : Type*) (n : Type*) (α : Type*)
  [Fintype m] [Fintype n] [Fintype α] [DecidableEq α] where
  /-- An `m × n` array of symbols. -/
  M : Matrix m n α
  /-- An `m × n` Latin rectangle contains `n` distinct entries. -/
  card_eq : Fintype.card α = Fintype.card n
  /-- Each row contains each symbol exactly once. -/
  row_bijective : ∀ i, Function.Bijective (M.row i)
  /-- Entries cannot repeat in a given column. -/
  col_injective : ∀ y, Function.Injective (M.col y)
  /-- The number of rows is less than or equal to the number of columns. -/
  card_le : Fintype.card m ≤ Fintype.card n := by simp

attribute [coe] LatinRectangle.M

/-- Pretty printing of Latin rectangles. -/
instance {m n : ℕ} [Repr α] : Repr (LatinRectangle (Fin m) (Fin n) α) where
  reprPrec L _ := repr L.M

variable (n α) in
/-- A `LatinSquare` is a square `LatinRectangle` -/
abbrev LatinSquare := LatinRectangle n n α

/-- Get the underlying `Matrix` of a `LatinRectangle`. -/
instance : Coe (LatinRectangle m n α) (Matrix m n α) where
  coe A := A.M

/-- Get a specific column of a `LatinRectangle`. -/
abbrev LatinRectangle.col (A : LatinRectangle m n α) : n → m → α := Matrix.col A

/-- Get a specific row of a `LatinRectangle`. -/
abbrev LatinRectangle.row (A : LatinRectangle m n α) : m → n → α := Matrix.row A

/-- Construct a `LatinSquare` given that both the rows and columns are bijective -/
@[reducible]
def LatinSquare.fromOncePerColumn (M : Matrix n n α) (card_eq : Fintype.card α = Fintype.card n)
    (row_bijective : ∀ i, Function.Bijective (M.row i))
    (col_bijective : ∀ j, Function.Bijective (M.col j)) :
    LatinSquare n α := {
  M := M,
  card_eq := card_eq,
  row_bijective := row_bijective,
  col_injective := (col_bijective · |>.injective)
  }

/-- The Cayley table of a finite `Group` is an example of a Latin square. -/
@[to_additive /-- The Cayley table of a finite `AddGroup` is an example of a Latin square. -/,
  reducible]
def LatinSquare.ofGroup (G : Type*) [DecidableEq G] [Group G] [Fintype G] :
    LatinSquare G G :=
  LatinSquare.fromOncePerColumn
    (M := fun i j ↦ i * j)
    (card_eq := by rfl)
    (row_bijective := by
      simp only [Matrix.row]
      exact Group.mulLeft_bijective (G := G))
    (col_bijective := by
      simp only [Matrix.col]
      exact Group.mulRight_bijective (G := G))

section Equivalence

/-- Given relabeling maps for the rows, columns, and symbols,
    produce the relabeled Latin rectangle. -/
@[reducible]
def LatinRectangle.relabel (A : LatinRectangle m n α) (f : m ≃ m') (g : n ≃ n') (h : α ≃ β) :
    LatinRectangle m' n' β := {
  M := (A.M.reindex f g).map h.toFun
  card_eq := by
    have g' : Fintype.card n = Fintype.card n' := Fintype.card_congr g
    have h' : Fintype.card α = Fintype.card β := Fintype.card_congr h
    have k' := A.card_eq
    lia,
  row_bijective i' :=
    h.bijective.comp (A.row_bijective (f.symm i') |>.comp g.symm.bijective)
  col_injective := by
    have h' := A.col_injective
    simp only [Function.Injective, Matrix.col_apply, Matrix.reindex_apply, Equiv.toFun_as_coe,
      Matrix.map_apply, Matrix.submatrix_apply, EmbeddingLike.apply_eq_iff_eq] at *
    intro y a₁ a₂ h
    convert h' (g.symm y) h
    simp
  card_le := by
    have ineq := A.card_le
    have f' : Fintype.card m = Fintype.card m' := Fintype.card_congr f
    have g' : Fintype.card n = Fintype.card n' := Fintype.card_congr g
    lia
  }

/-- An equivalence of Latin Rectangles -/
structure LatinRectangle.Equiv (A : LatinRectangle m n α) (A' : LatinRectangle m' n' β) where
  /-- A row relabeling. -/
  (f : m ≃ m')
  /-- A column relabeling. -/
  (g : n ≃ n')
  /-- A symbol relabeling. -/
  (h : α ≃ β)
  /-- Relabelings preserve structure. -/
  (map_rel : LatinRectangle.relabel A f g h = A')

/-- Two Latin rectangles are equivalent if one can be obtained from the other by some combination
    of relabeling the row indices, column indices, and symbols. -/
def LatinRectangle.EquivRelation (A : LatinRectangle m n α) (A' : LatinRectangle m' n' β) :=
    Nonempty (LatinRectangle.Equiv A A')

/-- Notation for two `LatinRectangle`s to be equivalent. -/
infixl:25 " ≃ " => LatinRectangle.EquivRelation

lemma LatinRectangle.equiv_relabel (f : m ≃ m') (g : n ≃ n') (h : α ≃ β)
    (A : LatinRectangle m n α) : A ≃ (LatinRectangle.relabel A f g h) :=
  ⟨f, g, h, by rfl⟩

end Equivalence

section Nonvacuous

instance {n : Nat} [NeZero n] : LatinSquare (ZMod n) (ZMod n) :=
  LatinSquare.ofAddGroup (ZMod n)

/-- For any positive natural number n, there exists an n × n Latin square. -/
noncomputable instance n_nonempty {n : Type*} [Fintype n]
    [nezero_n : NeZero (Fintype.card n)]
    [h : Fact (Fintype.card n = Fintype.card α)] :
    Nonempty (LatinSquare n α) := by
  have := Fin.addCommGroup (Fintype.card n)
  let a := LatinSquare.ofAddGroup (Fin (Fintype.card n))
  have f :=  Fintype.equivFin n
  have h' := Fintype.equivFinOfCardEq h.out.symm
  have h'' := Fintype.equivFin α
  have b := LatinRectangle.relabel a f.symm f.symm h'.symm
  exact Nonempty.intro (b : LatinSquare n α)

end Nonvacuous

section Completion

variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
variable {k : Type*} [Fintype k] [Nonempty k] [DecidableEq k]

/-- Property of `LatinRectangle` being contained in another `LatinRectangle` -/
def IsSubrect (A : LatinRectangle m n α) (B : LatinRectangle m' n' α) :=
  ∃ (ι : m ↪ m') (ι' : n ↪ n'), B.M.submatrix ι ι' = A.M

/-- A map returning the set of symbols in α not in column j. -/
def symbolsNotIn (A : LatinRectangle k n α) (j : n) :=
  let D := Finset.image (LatinRectangle.col A j) Finset.univ
  Finset.univ \ D

/-- For a k × n Latin rectangle, the set of entries in each column has cardinality k. -/
lemma col_card {k n : Type*} [Fintype k] [Fintype n] (A : LatinRectangle k n α) :
    ∀ j, (Finset.image (LatinRectangle.col A j) Finset.univ).card = Fintype.card k := by
  intro j
  have h_inj := A.col_injective
  exact Finset.card_image_of_injective Finset.univ (h_inj j)


lemma LatinRectangle.card_symbols_not_in {k n : Type*} [Fintype k] [Fintype n]
    (A : LatinRectangle k n α) :
    ∀ j, Finset.card (symbolsNotIn A j) = Fintype.card n - Fintype.card k := by
  simp [symbolsNotIn,
        Finset.card_sdiff,
        A.card_eq,
        col_card A]

/-- For fixed symbol x, a Latin rectangle gives a map from row indices to column indices. -/
lemma LatinRectangle.row_entry_to_column_entry {k n : Type*} [Fintype k] [Fintype n]
    (A : LatinRectangle k n α) (x : α) :
    ∃ f : k → n, ∀ {a : k} {b : n}, LatinRectangle.M a b = x ↔ f a = b := by
  have hrow := A.row_bijective
  conv at hrow =>
    ext
    rw [Function.bijective_iff_existsUnique]
  rw [forall_comm] at hrow
  specialize hrow x
  rw [forall_existsUnique_iff] at hrow
  exact hrow



/-- The number of columns that do c not contain a given entry x is equal to n-k. -/
lemma LatinRectangle.card_symbolsNotIn_eq {k n : Type*} [Fintype n]
    [Fintype k] (A : LatinRectangle k n α) (_ : Fintype.card k < Fintype.card n) :
  ∀ x, (Finset.card {j : n | x ∈ (symbolsNotIn A) j}) = Fintype.card n - Fintype.card k := by
  classical
  intro x
  obtain ⟨f, hf⟩ := A.row_entry_to_column_entry x
  have h₁ : Finset.filter (fun j => x ∈ (symbolsNotIn A) j) Finset.univ =
      (Finset.image f Finset.univ)ᶜ := by
    ext j
    simp [symbolsNotIn, hf, eq_comm]
  have hf_inj : Function.Injective f := by
    intro a₁ a₂ heq
    have ha₁ : A.M a₁ (f a₂) = x := by
      rw [←heq]
      exact hf.mpr rfl
    have ha₂ : A.M a₂ (f a₂) = x := hf.mpr rfl
    exact A.col_injective (f a₂) (ha₁.trans ha₂.symm)
  rw [h₁, Finset.card_compl, Finset.card_image_of_injective Finset.univ hf_inj, Finset.card_univ]


open Classical in
/-- At most n-k columns that do not contain a given entry x -/
lemma LatinRectangle.card_symbolsNotIn_le {k n : Type*} [Fintype n]
    [Fintype k] (A : LatinRectangle k n α) (h : Fintype.card k < Fintype.card n) :
    ∀ x, ∀ (t : Finset n),
    (Finset.card {j : n | j ∈ t ∧ x ∈ (symbolsNotIn A) j}) ≤ Fintype.card n - Fintype.card k := by
  intro x t
  rw [← A.card_symbolsNotIn_eq h x]
  exact Finset.card_le_card (by simp [Finset.subset_iff])

/-- Extend LatinRectangle given a valid extension map -/
@[instance_reducible]
noncomputable def LatinRectangle.extendRow {k n : Type*} [Fintype n]
    [Fintype k] [Nonempty k] (A : LatinRectangle k n α) (h : Fintype.card k < Fintype.card n)
    {k' : Type*} [Fintype k'] [DecidableEq k']
    (ι : k ↪ k') (h₂ : Fintype.card k' = Fintype.card k + 1)
    (f : n → α) (hf_inj : Function.Injective f) (hf_valid : ∀ j, f j ∈ symbolsNotIn A j) :
    LatinRectangle k' n α :=
  let M' : k' → n → α := fun i j =>
    if hif : i ∈ (Finset.image ι Finset.univ)
    then A.M (Function.invFun ι i) j
    else f j
  {
    M := M'
    card_eq := A.card_eq
    row_bijective := by
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
        have h := A.row_bijective
        simp only [Matrix.row] at h
        apply h
      · have h_card : Fintype.card n = Fintype.card α := A.card_eq.symm
        exact (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, h_card⟩
    col_injective := by
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
        have h := A.col_injective
        unfold Function.Injective at h
        intro hM
        apply h at hM
        congr
      · intro h
        have hfy := hf_valid y
        simp only [symbolsNotIn, Finset.mem_sdiff, Finset.mem_univ,
                   Finset.mem_image, Matrix.col_apply, true_and, not_exists] at hfy
        have hfyi := hfy (Function.invFun ι a1)
        contradiction
      · intro h
        have hfy := hf_valid y
        simp only [symbolsNotIn, Finset.mem_sdiff, Finset.mem_univ,
                   Finset.mem_image, Matrix.col_apply, true_and, not_exists] at hfy
        have hfyi := hfy (Function.invFun ι a2)
        have h_symm := h.symm
        contradiction
      · have h := Fintype.existsUnique_notMem_image_of_injective_of_card_eq_add_one
          ι.toFun ι.inj' h₂
        simp only [Finset.mem_image] at h
        intro _
        exact ExistsUnique.unique (y₁ := a1) (y₂ := a2) h
          (by simpa using if_h₁) (by simpa using if_h₂)
    card_le := by lia
  }

/-- A non-square `LatinRectangle k n α` can be extended by one row to a new Latin rectangle. -/
theorem LatinRectangle.exists_isSubrect_of_card_eq_card_add_one {k n : Type*} [Fintype n]
    [Fintype k] [Nonempty k] (A : LatinRectangle k n α) (h : Fintype.card k < Fintype.card n)
    {k' : Type*} [Fintype k'] (ι : k ↪ k') (h₂ : Fintype.card k' = Fintype.card k + 1) :
    ∃ (A' : LatinRectangle k' n α), IsSubrect A A' := by
  classical
  let B := symbolsNotIn A
  have Bj_size (j : n) : Finset.card (B j) = (Fintype.card n) - (Fintype.card k) :=
    LatinRectangle.card_symbols_not_in A j
  have exactly_n_minus_k_cols_without_x := LatinRectangle.card_symbolsNotIn_eq (n := n) (k := k)
    (α := α) A h
  have pre_property_H : ∀ (x : α) (t : Finset n),
    {j ∈ t | x ∈ B j}.card ≤ Fintype.card n - Fintype.card k := by
    convert LatinRectangle.card_symbolsNotIn_le (n := n) (k := k) (α := α) A h using 4
    grind
  have _ : NeZero (Fintype.card n - Fintype.card k)  := ⟨by lia⟩
  let halls := hallMatchingsOn.nonempty (B)
    (Finset.card_le_card_biUnion_of_card_eq_of_card_filter_le (by lia) Bj_size pre_property_H)
    (Finset.univ)
  set f := Classical.choice halls with hx
  simp only [hallMatchingsOn] at f
  obtain ⟨ f', hf⟩ := f
  let M' : k' → n → α := fun i j =>
    if hif : i ∈ (Finset.image ι Finset.univ)
    then A.M (Function.invFun ι i) j
    else (f' ⟨j, by simp⟩ )
  let f : n → α := fun j ↦ f' ⟨j, Finset.mem_univ j⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply hf.1 at hab
    simp only [Subtype.mk.injEq] at hab
    exact hab
  have hf_valid : ∀ j, f j ∈ symbolsNotIn A j := by
    intro j
    exact hf.2 ⟨j, Finset.mem_univ j⟩
  let A' : LatinRectangle k' n α := LatinRectangle.extendRow A h ι h₂ f hf_inj hf_valid
  use A'
  unfold IsSubrect
  unfold LatinRectangle.M
  use ι
  use (Equiv.refl n)
  ext
  simp only [A', LatinRectangle.extendRow]
  unfold Matrix.submatrix
  simp only [Finset.mem_image, Finset.mem_univ, EmbeddingLike.apply_eq_iff_eq, true_and, exists_eq,
    reduceDIte, Equiv.refl_toEmbedding, Function.Embedding.refl_apply, Matrix.of_apply]
  rw [<-Function.comp_apply (f := Function.invFun ι)]
  rw [Function.invFun_comp ι.injective]
  rfl

/-- Being a subrectangle of a `LatinRectangle` is a transitive property. -/
lemma IsSubrect.trans {m'' : Type*} [Fintype m''] {n : Type*} [Fintype n] {A : LatinRectangle m n α}
    {A' : LatinRectangle m' n α} {A'' : LatinRectangle m'' n α} (h₁ : IsSubrect A A')
    (h₂ : IsSubrect A' A'') : IsSubrect A A'' := by
  unfold IsSubrect at *
  obtain ⟨f,g,h₁⟩ := h₁
  obtain ⟨f',g',h₂⟩ := h₂
  set f'' := Function.Embedding.trans f f'
  set g'' := Function.Embedding.trans g g'
  use f'', g''
  simp only [f'', g'']
  repeat rw [Function.Embedding.coe_trans]
  rw [<- Matrix.submatrix_submatrix]
  rw [h₂, h₁]

/-- Any two row relabeled `LatinRectangle`s are subrectangles of each other. -/
lemma IsSubrect.refl {n : Type*} [Fintype n] {A : LatinRectangle m n α} {A' : LatinRectangle m' n α}
    (f : m ≃ m') (h : A' = A.relabel f (.refl n) (.refl α)) : IsSubrect A A' := by
  simp only [IsSubrect]
  use f
  use Equiv.refl n
  unfold LatinRectangle.relabel at h
  simp only [Matrix.submatrix, Equiv.coe_toEmbedding, Equiv.refl_toEmbedding,
    Function.Embedding.refl_apply]
  have h2 := congr_arg (·.M) h
  simp only [Matrix.reindex_apply, Equiv.refl_symm, Equiv.coe_refl, Equiv.toFun_as_coe,
    Matrix.map_id] at h2
  rw [h2]
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, id_eq]
  rfl

/-- A Latin rectangle `LatinRectangle m n α` extends to a Latin square `LatinSquare n α`.
    In other words, there always exists a Latin square that contains a given Latin rectangle
    as a substructure. -/
theorem LatinRectangle.exists_LatinSquare_of_LatinRectangle {k n : Type*} [Fintype n]
    [Fintype k] [Nonempty k] (A : LatinRectangle k n α) (h : Fintype.card k ≤ Fintype.card n) :
    ∃ (A' : LatinRectangle n n α), IsSubrect A A' := by
  induction h_gap : (Fintype.card n - Fintype.card k) using
    Nat.strong_induction_on generalizing k A with
  | h a ih =>
    by_cases h_full : Fintype.card k = Fintype.card n
    · let f : k ≃ n := Fintype.equivOfCardEq h_full
      set A' := LatinRectangle.relabel A f (Equiv.refl n) (Equiv.refl α) with hA'
      use A'
      exact IsSubrect.refl f hA'
    · set k' := Option k with hk'
      let : Fintype k' := (inferInstance : Fintype (Option k))
      have hk'_card := Fintype.card_option (α := k)
      replace hk' := hk'.symm
      simp only [hk'] at hk'_card
      have hk'_le : Fintype.card k ≤ Fintype.card k' := by lia
      have h_k_lt_n : Fintype.card k < Fintype.card n := by lia
      have h_k'_le_n : Fintype.card k' ≤ Fintype.card n := by lia
      set m := Fintype.card n - Fintype.card k' with hm
      have hm_lt : m < a := by lia
      have ι_h := Function.Embedding.nonempty_of_card_le hk'_le
      let ι' : k ↪ k' := Classical.choice ι_h
      have H := LatinRectangle.exists_isSubrect_of_card_eq_card_add_one A h_k_lt_n ι' hk'_card
      have ⟨A', hA⟩ := H
      have ih := ih m hm_lt (k := k') (A := A') h_k'_le_n hm
      have ⟨A'', hA''⟩ := ih
      exact ⟨A'', hA.trans hA''⟩

end Completion

end
