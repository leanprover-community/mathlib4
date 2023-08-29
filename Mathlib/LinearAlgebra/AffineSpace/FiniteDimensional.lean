/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.FiniteDimensional

#align_import linear_algebra.affine_space.finite_dimensional from "leanprover-community/mathlib"@"67e606eaea14c7854bdc556bd53d98aefdf76ec0"

/-!
# Finite-dimensional subspaces of affine spaces.

This file provides a few results relating to finite-dimensional
subspaces of affine spaces.

## Main definitions

* `Collinear` defines collinear sets of points as those that span a
  subspace of dimension at most 1.

-/


noncomputable section

open BigOperators Affine

section AffineSpace'

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

open AffineSubspace FiniteDimensional Module

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- The `vectorSpan` of a finite set is finite-dimensional. -/
theorem finiteDimensional_vectorSpan_of_finite {s : Set P} (h : Set.Finite s) :
    FiniteDimensional k (vectorSpan k s) :=
  span_of_finite k <| h.vsub h
#align finite_dimensional_vector_span_of_finite finiteDimensional_vectorSpan_of_finite

/-- The `vectorSpan` of a family indexed by a `Fintype` is
finite-dimensional. -/
instance finiteDimensional_vectorSpan_range [Finite ι] (p : ι → P) :
    FiniteDimensional k (vectorSpan k (Set.range p)) :=
  finiteDimensional_vectorSpan_of_finite k (Set.finite_range _)
#align finite_dimensional_vector_span_range finiteDimensional_vectorSpan_range

/-- The `vectorSpan` of a subset of a family indexed by a `Fintype`
is finite-dimensional. -/
instance finiteDimensional_vectorSpan_image_of_finite [Finite ι] (p : ι → P) (s : Set ι) :
    FiniteDimensional k (vectorSpan k (p '' s)) :=
  finiteDimensional_vectorSpan_of_finite k (Set.toFinite _)
#align finite_dimensional_vector_span_image_of_finite finiteDimensional_vectorSpan_image_of_finite

/-- The direction of the affine span of a finite set is
finite-dimensional. -/
theorem finiteDimensional_direction_affineSpan_of_finite {s : Set P} (h : Set.Finite s) :
    FiniteDimensional k (affineSpan k s).direction :=
  (direction_affineSpan k s).symm ▸ finiteDimensional_vectorSpan_of_finite k h
#align finite_dimensional_direction_affine_span_of_finite finiteDimensional_direction_affineSpan_of_finite

/-- The direction of the affine span of a family indexed by a
`Fintype` is finite-dimensional. -/
instance finiteDimensional_direction_affineSpan_range [Finite ι] (p : ι → P) :
    FiniteDimensional k (affineSpan k (Set.range p)).direction :=
  finiteDimensional_direction_affineSpan_of_finite k (Set.finite_range _)
#align finite_dimensional_direction_affine_span_range finiteDimensional_direction_affineSpan_range

/-- The direction of the affine span of a subset of a family indexed
by a `Fintype` is finite-dimensional. -/
instance finiteDimensional_direction_affineSpan_image_of_finite [Finite ι] (p : ι → P) (s : Set ι) :
    FiniteDimensional k (affineSpan k (p '' s)).direction :=
  finiteDimensional_direction_affineSpan_of_finite k (Set.toFinite _)
#align finite_dimensional_direction_affine_span_image_of_finite finiteDimensional_direction_affineSpan_image_of_finite

/-- An affine-independent family of points in a finite-dimensional affine space is finite. -/
theorem finite_of_fin_dim_affineIndependent [FiniteDimensional k V] {p : ι → P}
    (hi : AffineIndependent k p) : Finite ι := by
  nontriviality ι; inhabit ι
  -- ⊢ _root_.Finite ι
                   -- ⊢ _root_.Finite ι
  rw [affineIndependent_iff_linearIndependent_vsub k p default] at hi
  -- ⊢ _root_.Finite ι
  letI : IsNoetherian k V := IsNoetherian.iff_fg.2 inferInstance
  -- ⊢ _root_.Finite ι
  exact
    (Set.finite_singleton default).finite_of_compl (Set.finite_coe_iff.1 hi.finite_of_isNoetherian)
#align finite_of_fin_dim_affine_independent finite_of_fin_dim_affineIndependent

/-- An affine-independent subset of a finite-dimensional affine space is finite. -/
theorem finite_set_of_fin_dim_affineIndependent [FiniteDimensional k V] {s : Set ι} {f : s → P}
    (hi : AffineIndependent k f) : s.Finite :=
  @Set.toFinite _ s (finite_of_fin_dim_affineIndependent k hi)
#align finite_set_of_fin_dim_affine_independent finite_set_of_fin_dim_affineIndependent

variable {k}

/-- The `vectorSpan` of a finite subset of an affinely independent
family has dimension one less than its cardinality. -/
theorem AffineIndependent.finrank_vectorSpan_image_finset [DecidableEq P]
    {p : ι → P} (hi : AffineIndependent k p) {s : Finset ι} {n : ℕ} (hc : Finset.card s = n + 1) :
    finrank k (vectorSpan k (s.image p : Set P)) = n := by
  classical
  have hi' := hi.range.mono (Set.image_subset_range p ↑s)
  have hc' : (s.image p).card = n + 1 := by rwa [s.card_image_of_injective hi.injective]
  have hn : (s.image p).Nonempty := by simp [hc', ← Finset.card_pos]
  rcases hn with ⟨p₁, hp₁⟩
  have hp₁' : p₁ ∈ p '' s := by simpa using hp₁
  rw [affineIndependent_set_iff_linearIndependent_vsub k hp₁', ← Finset.coe_singleton,
    ← Finset.coe_image, ← Finset.coe_sdiff, Finset.sdiff_singleton_eq_erase, ← Finset.coe_image]
    at hi'
  have hc : (Finset.image (fun p : P => p -ᵥ p₁) ((Finset.image p s).erase p₁)).card = n := by
    rw [Finset.card_image_of_injective _ (vsub_left_injective _), Finset.card_erase_of_mem hp₁]
    exact Nat.pred_eq_of_eq_succ hc'
  rwa [vectorSpan_eq_span_vsub_finset_right_ne k hp₁, finrank_span_finset_eq_card, hc]
#align affine_independent.finrank_vector_span_image_finset AffineIndependent.finrank_vectorSpan_image_finset

/-- The `vectorSpan` of a finite affinely independent family has
dimension one less than its cardinality. -/
theorem AffineIndependent.finrank_vectorSpan [Fintype ι] {p : ι → P} (hi : AffineIndependent k p)
    {n : ℕ} (hc : Fintype.card ι = n + 1) : finrank k (vectorSpan k (Set.range p)) = n := by
  classical
  rw [← Finset.card_univ] at hc
  rw [← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image]
  exact hi.finrank_vectorSpan_image_finset hc
#align affine_independent.finrank_vector_span AffineIndependent.finrank_vectorSpan

/-- The `vectorSpan` of a finite affinely independent family whose
cardinality is one more than that of the finite-dimensional space is
`⊤`. -/
theorem AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one [FiniteDimensional k V]
    [Fintype ι] {p : ι → P} (hi : AffineIndependent k p) (hc : Fintype.card ι = finrank k V + 1) :
    vectorSpan k (Set.range p) = ⊤ :=
  Submodule.eq_top_of_finrank_eq <| hi.finrank_vectorSpan hc
#align affine_independent.vector_span_eq_top_of_card_eq_finrank_add_one AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one

variable (k)

/-- The `vectorSpan` of `n + 1` points in an indexed family has
dimension at most `n`. -/
theorem finrank_vectorSpan_image_finset_le [DecidableEq P] (p : ι → P) (s : Finset ι) {n : ℕ}
    (hc : Finset.card s = n + 1) : finrank k (vectorSpan k (s.image p : Set P)) ≤ n := by
  classical
  have hn : (s.image p).Nonempty := by
    rw [Finset.Nonempty.image_iff, ← Finset.card_pos, hc]
    apply Nat.succ_pos
  rcases hn with ⟨p₁, hp₁⟩
  rw [vectorSpan_eq_span_vsub_finset_right_ne k hp₁]
  refine' le_trans (finrank_span_finset_le_card (((s.image p).erase p₁).image fun p => p -ᵥ p₁)) _
  rw [Finset.card_image_of_injective _ (vsub_left_injective p₁), Finset.card_erase_of_mem hp₁,
    tsub_le_iff_right, ← hc]
  apply Finset.card_image_le
#align finrank_vector_span_image_finset_le finrank_vectorSpan_image_finset_le

/-- The `vectorSpan` of an indexed family of `n + 1` points has
dimension at most `n`. -/
theorem finrank_vectorSpan_range_le [Fintype ι] (p : ι → P) {n : ℕ} (hc : Fintype.card ι = n + 1) :
    finrank k (vectorSpan k (Set.range p)) ≤ n := by
  classical
  rw [← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image]
  rw [← Finset.card_univ] at hc
  exact finrank_vectorSpan_image_finset_le _ _ _ hc
#align finrank_vector_span_range_le finrank_vectorSpan_range_le

/-- `n + 1` points are affinely independent if and only if their
`vectorSpan` has dimension `n`. -/
theorem affineIndependent_iff_finrank_vectorSpan_eq [Fintype ι] (p : ι → P) {n : ℕ}
    (hc : Fintype.card ι = n + 1) :
    AffineIndependent k p ↔ finrank k (vectorSpan k (Set.range p)) = n := by
  classical
  have hn : Nonempty ι := by simp [← Fintype.card_pos_iff, hc]
  cases' hn with i₁
  rw [affineIndependent_iff_linearIndependent_vsub _ _ i₁,
    linearIndependent_iff_card_eq_finrank_span, eq_comm,
    vectorSpan_range_eq_span_range_vsub_right_ne k p i₁, Set.finrank]
  congr
  rw [← Finset.card_univ] at hc
  rw [Fintype.subtype_card]
  simp [Finset.filter_ne', Finset.card_erase_of_mem, hc]
#align affine_independent_iff_finrank_vector_span_eq affineIndependent_iff_finrank_vectorSpan_eq

/-- `n + 1` points are affinely independent if and only if their
`vectorSpan` has dimension at least `n`. -/
theorem affineIndependent_iff_le_finrank_vectorSpan [Fintype ι] (p : ι → P) {n : ℕ}
    (hc : Fintype.card ι = n + 1) :
    AffineIndependent k p ↔ n ≤ finrank k (vectorSpan k (Set.range p)) := by
  rw [affineIndependent_iff_finrank_vectorSpan_eq k p hc]
  -- ⊢ finrank k { x // x ∈ vectorSpan k (Set.range p) } = n ↔ n ≤ finrank k { x // …
  constructor
  -- ⊢ finrank k { x // x ∈ vectorSpan k (Set.range p) } = n → n ≤ finrank k { x // …
  · rintro rfl
    -- ⊢ finrank k { x // x ∈ vectorSpan k (Set.range p) } ≤ finrank k { x // x ∈ vec …
    rfl
    -- 🎉 no goals
  · exact fun hle => le_antisymm (finrank_vectorSpan_range_le k p hc) hle
    -- 🎉 no goals
#align affine_independent_iff_le_finrank_vector_span affineIndependent_iff_le_finrank_vectorSpan

/-- `n + 2` points are affinely independent if and only if their
`vectorSpan` does not have dimension at most `n`. -/
theorem affineIndependent_iff_not_finrank_vectorSpan_le [Fintype ι] (p : ι → P) {n : ℕ}
    (hc : Fintype.card ι = n + 2) :
    AffineIndependent k p ↔ ¬finrank k (vectorSpan k (Set.range p)) ≤ n := by
  rw [affineIndependent_iff_le_finrank_vectorSpan k p hc, ← Nat.lt_iff_add_one_le, lt_iff_not_ge]
  -- 🎉 no goals
#align affine_independent_iff_not_finrank_vector_span_le affineIndependent_iff_not_finrank_vectorSpan_le

/-- `n + 2` points have a `vectorSpan` with dimension at most `n` if
and only if they are not affinely independent. -/
theorem finrank_vectorSpan_le_iff_not_affineIndependent [Fintype ι] (p : ι → P) {n : ℕ}
    (hc : Fintype.card ι = n + 2) :
    finrank k (vectorSpan k (Set.range p)) ≤ n ↔ ¬AffineIndependent k p :=
  (not_iff_comm.1 (affineIndependent_iff_not_finrank_vectorSpan_le k p hc).symm).symm
#align finrank_vector_span_le_iff_not_affine_independent finrank_vectorSpan_le_iff_not_affineIndependent

variable {k}

/-- If the `vectorSpan` of a finite subset of an affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule. -/
theorem AffineIndependent.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one
    [DecidableEq P] {p : ι → P}
    (hi : AffineIndependent k p) {s : Finset ι} {sm : Submodule k V} [FiniteDimensional k sm]
    (hle : vectorSpan k (s.image p : Set P) ≤ sm) (hc : Finset.card s = finrank k sm + 1) :
    vectorSpan k (s.image p : Set P) = sm :=
  eq_of_le_of_finrank_eq hle <| hi.finrank_vectorSpan_image_finset hc
#align affine_independent.vector_span_image_finset_eq_of_le_of_card_eq_finrank_add_one AffineIndependent.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one

/-- If the `vectorSpan` of a finite affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule. -/
theorem AffineIndependent.vectorSpan_eq_of_le_of_card_eq_finrank_add_one [Fintype ι] {p : ι → P}
    (hi : AffineIndependent k p) {sm : Submodule k V} [FiniteDimensional k sm]
    (hle : vectorSpan k (Set.range p) ≤ sm) (hc : Fintype.card ι = finrank k sm + 1) :
    vectorSpan k (Set.range p) = sm :=
  eq_of_le_of_finrank_eq hle <| hi.finrank_vectorSpan hc
#align affine_independent.vector_span_eq_of_le_of_card_eq_finrank_add_one AffineIndependent.vectorSpan_eq_of_le_of_card_eq_finrank_add_one

/-- If the `affineSpan` of a finite subset of an affinely independent
family lies in an affine subspace whose direction has dimension one
less than its cardinality, it equals that subspace. -/
theorem AffineIndependent.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one
    [DecidableEq P] {p : ι → P}
    (hi : AffineIndependent k p) {s : Finset ι} {sp : AffineSubspace k P}
    [FiniteDimensional k sp.direction] (hle : affineSpan k (s.image p : Set P) ≤ sp)
    (hc : Finset.card s = finrank k sp.direction + 1) : affineSpan k (s.image p : Set P) = sp := by
  have hn : s.Nonempty := by
    rw [← Finset.card_pos, hc]
    apply Nat.succ_pos
  refine' eq_of_direction_eq_of_nonempty_of_le _ ((hn.image p).to_set.affineSpan k) hle
  -- ⊢ direction (affineSpan k ↑(Finset.image p s)) = direction sp
  have hd := direction_le hle
  -- ⊢ direction (affineSpan k ↑(Finset.image p s)) = direction sp
  rw [direction_affineSpan] at hd ⊢
  -- ⊢ vectorSpan k ↑(Finset.image p s) = direction sp
  exact hi.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one hd hc
  -- 🎉 no goals
#align affine_independent.affine_span_image_finset_eq_of_le_of_card_eq_finrank_add_one AffineIndependent.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one

/-- If the `affineSpan` of a finite affinely independent family lies
in an affine subspace whose direction has dimension one less than its
cardinality, it equals that subspace. -/
theorem AffineIndependent.affineSpan_eq_of_le_of_card_eq_finrank_add_one [Fintype ι] {p : ι → P}
    (hi : AffineIndependent k p) {sp : AffineSubspace k P} [FiniteDimensional k sp.direction]
    (hle : affineSpan k (Set.range p) ≤ sp) (hc : Fintype.card ι = finrank k sp.direction + 1) :
    affineSpan k (Set.range p) = sp := by
  classical
  rw [← Finset.card_univ] at hc
  rw [← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image] at hle ⊢
  exact hi.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one hle hc
#align affine_independent.affine_span_eq_of_le_of_card_eq_finrank_add_one AffineIndependent.affineSpan_eq_of_le_of_card_eq_finrank_add_one

/-- The `affineSpan` of a finite affinely independent family is `⊤` iff the
family's cardinality is one more than that of the finite-dimensional space. -/
theorem AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one [FiniteDimensional k V]
    [Fintype ι] {p : ι → P} (hi : AffineIndependent k p) :
    affineSpan k (Set.range p) = ⊤ ↔ Fintype.card ι = finrank k V + 1 := by
  constructor
  -- ⊢ affineSpan k (Set.range p) = ⊤ → Fintype.card ι = finrank k V + 1
  · intro h_tot
    -- ⊢ Fintype.card ι = finrank k V + 1
    let n := Fintype.card ι - 1
    -- ⊢ Fintype.card ι = finrank k V + 1
    have hn : Fintype.card ι = n + 1 :=
      (Nat.succ_pred_eq_of_pos (card_pos_of_affineSpan_eq_top k V P h_tot)).symm
    rw [hn, ← finrank_top, ← (vectorSpan_eq_top_of_affineSpan_eq_top k V P) h_tot,
      ← hi.finrank_vectorSpan hn]
  · intro hc
    -- ⊢ affineSpan k (Set.range p) = ⊤
    rw [← finrank_top, ← direction_top k V P] at hc
    -- ⊢ affineSpan k (Set.range p) = ⊤
    exact hi.affineSpan_eq_of_le_of_card_eq_finrank_add_one le_top hc
    -- 🎉 no goals
#align affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one

theorem Affine.Simplex.span_eq_top [FiniteDimensional k V] {n : ℕ} (T : Affine.Simplex k V n)
    (hrank : finrank k V = n) : affineSpan k (Set.range T.points) = ⊤ := by
  rw [AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one T.Independent,
    Fintype.card_fin, hrank]
#align affine.simplex.span_eq_top Affine.Simplex.span_eq_top

/-- The `vectorSpan` of adding a point to a finite-dimensional subspace is finite-dimensional. -/
instance finiteDimensional_vectorSpan_insert (s : AffineSubspace k P)
    [FiniteDimensional k s.direction] (p : P) :
    FiniteDimensional k (vectorSpan k (insert p (s : Set P))) := by
  rw [← direction_affineSpan, ← affineSpan_insert_affineSpan]
  -- ⊢ FiniteDimensional k { x // x ∈ direction (affineSpan k (insert p ↑(affineSpa …
  rcases (s : Set P).eq_empty_or_nonempty with (hs | ⟨p₀, hp₀⟩)
  -- ⊢ FiniteDimensional k { x // x ∈ direction (affineSpan k (insert p ↑(affineSpa …
  · rw [coe_eq_bot_iff] at hs
    -- ⊢ FiniteDimensional k { x // x ∈ direction (affineSpan k (insert p ↑(affineSpa …
    rw [hs, bot_coe, span_empty, bot_coe, direction_affineSpan]
    -- ⊢ FiniteDimensional k { x // x ∈ vectorSpan k (insert p ∅) }
    convert finiteDimensional_bot _ _ <;> simp
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- 🎉 no goals
  · rw [affineSpan_coe, direction_affineSpan_insert hp₀]
    -- ⊢ FiniteDimensional k { x // x ∈ Submodule.span k {p -ᵥ p₀} ⊔ direction s }
    infer_instance
    -- 🎉 no goals
#align finite_dimensional_vector_span_insert finiteDimensional_vectorSpan_insert

/-- The direction of the affine span of adding a point to a finite-dimensional subspace is
finite-dimensional. -/
instance finiteDimensional_direction_affineSpan_insert (s : AffineSubspace k P)
    [FiniteDimensional k s.direction] (p : P) :
    FiniteDimensional k (affineSpan k (insert p (s : Set P))).direction :=
  (direction_affineSpan k (insert p (s : Set P))).symm ▸ finiteDimensional_vectorSpan_insert s p
#align finite_dimensional_direction_affine_span_insert finiteDimensional_direction_affineSpan_insert

variable (k)

/-- The `vectorSpan` of adding a point to a set with a finite-dimensional `vectorSpan` is
finite-dimensional. -/
instance finiteDimensional_vectorSpan_insert_set (s : Set P) [FiniteDimensional k (vectorSpan k s)]
    (p : P) : FiniteDimensional k (vectorSpan k (insert p s)) := by
  haveI : FiniteDimensional k (affineSpan k s).direction :=
    (direction_affineSpan k s).symm ▸ inferInstance
  rw [← direction_affineSpan, ← affineSpan_insert_affineSpan, direction_affineSpan]
  -- ⊢ FiniteDimensional k { x // x ∈ vectorSpan k (insert p ↑(affineSpan k s)) }
  exact finiteDimensional_vectorSpan_insert (affineSpan k s) p
  -- 🎉 no goals
#align finite_dimensional_vector_span_insert_set finiteDimensional_vectorSpan_insert_set

/-- A set of points is collinear if their `vectorSpan` has dimension
at most `1`. -/
def Collinear (s : Set P) : Prop :=
  Module.rank k (vectorSpan k s) ≤ 1
#align collinear Collinear

/-- The definition of `Collinear`. -/
theorem collinear_iff_rank_le_one (s : Set P) :
    Collinear k s ↔ Module.rank k (vectorSpan k s) ≤ 1 := Iff.rfl
#align collinear_iff_rank_le_one collinear_iff_rank_le_one

variable {k}

/-- A set of points, whose `vectorSpan` is finite-dimensional, is
collinear if and only if their `vectorSpan` has dimension at most
`1`. -/
theorem collinear_iff_finrank_le_one {s : Set P} [FiniteDimensional k (vectorSpan k s)] :
    Collinear k s ↔ finrank k (vectorSpan k s) ≤ 1 := by
  have h := collinear_iff_rank_le_one k s
  -- ⊢ Collinear k s ↔ finrank k { x // x ∈ vectorSpan k s } ≤ 1
  rw [← finrank_eq_rank] at h
  -- ⊢ Collinear k s ↔ finrank k { x // x ∈ vectorSpan k s } ≤ 1
  exact_mod_cast h
  -- 🎉 no goals
#align collinear_iff_finrank_le_one collinear_iff_finrank_le_one

alias ⟨Collinear.finrank_le_one, _⟩ := collinear_iff_finrank_le_one
#align collinear.finrank_le_one Collinear.finrank_le_one

/-- A subset of a collinear set is collinear. -/
theorem Collinear.subset {s₁ s₂ : Set P} (hs : s₁ ⊆ s₂) (h : Collinear k s₂) : Collinear k s₁ :=
  (rank_le_of_submodule (vectorSpan k s₁) (vectorSpan k s₂) (vectorSpan_mono k hs)).trans h
#align collinear.subset Collinear.subset

/-- The `vectorSpan` of collinear points is finite-dimensional. -/
theorem Collinear.finiteDimensional_vectorSpan {s : Set P} (h : Collinear k s) :
    FiniteDimensional k (vectorSpan k s) :=
  IsNoetherian.iff_fg.1
    (IsNoetherian.iff_rank_lt_aleph0.2 (lt_of_le_of_lt h Cardinal.one_lt_aleph0))
#align collinear.finite_dimensional_vector_span Collinear.finiteDimensional_vectorSpan

/-- The direction of the affine span of collinear points is finite-dimensional. -/
theorem Collinear.finiteDimensional_direction_affineSpan {s : Set P} (h : Collinear k s) :
    FiniteDimensional k (affineSpan k s).direction :=
  (direction_affineSpan k s).symm ▸ h.finiteDimensional_vectorSpan
#align collinear.finite_dimensional_direction_affine_span Collinear.finiteDimensional_direction_affineSpan

variable (k P)

/-- The empty set is collinear. -/
theorem collinear_empty : Collinear k (∅ : Set P) := by
  rw [collinear_iff_rank_le_one, vectorSpan_empty]
  -- ⊢ Module.rank k { x // x ∈ ⊥ } ≤ 1
  simp
  -- 🎉 no goals
#align collinear_empty collinear_empty

variable {P}

/-- A single point is collinear. -/
theorem collinear_singleton (p : P) : Collinear k ({p} : Set P) := by
  rw [collinear_iff_rank_le_one, vectorSpan_singleton]
  -- ⊢ Module.rank k { x // x ∈ ⊥ } ≤ 1
  simp
  -- 🎉 no goals
#align collinear_singleton collinear_singleton

variable {k}

/-- Given a point `p₀` in a set of points, that set is collinear if and
only if the points can all be expressed as multiples of the same
vector, added to `p₀`. -/
theorem collinear_iff_of_mem {s : Set P} {p₀ : P} (h : p₀ ∈ s) :
    Collinear k s ↔ ∃ v : V, ∀ p ∈ s, ∃ r : k, p = r • v +ᵥ p₀ := by
  simp_rw [collinear_iff_rank_le_one, rank_submodule_le_one_iff', Submodule.le_span_singleton_iff]
  -- ⊢ (∃ v₀, ∀ (v : V), v ∈ vectorSpan k s → ∃ r, r • v₀ = v) ↔ ∃ v, ∀ (p : P), p  …
  constructor
  -- ⊢ (∃ v₀, ∀ (v : V), v ∈ vectorSpan k s → ∃ r, r • v₀ = v) → ∃ v, ∀ (p : P), p  …
  · rintro ⟨v₀, hv⟩
    -- ⊢ ∃ v, ∀ (p : P), p ∈ s → ∃ r, p = r • v +ᵥ p₀
    use v₀
    -- ⊢ ∀ (p : P), p ∈ s → ∃ r, p = r • v₀ +ᵥ p₀
    intro p hp
    -- ⊢ ∃ r, p = r • v₀ +ᵥ p₀
    obtain ⟨r, hr⟩ := hv (p -ᵥ p₀) (vsub_mem_vectorSpan k hp h)
    -- ⊢ ∃ r, p = r • v₀ +ᵥ p₀
    use r
    -- ⊢ p = r • v₀ +ᵥ p₀
    rw [eq_vadd_iff_vsub_eq]
    -- ⊢ p -ᵥ p₀ = r • v₀
    exact hr.symm
    -- 🎉 no goals
  · rintro ⟨v, hp₀v⟩
    -- ⊢ ∃ v₀, ∀ (v : V), v ∈ vectorSpan k s → ∃ r, r • v₀ = v
    use v
    -- ⊢ ∀ (v_1 : V), v_1 ∈ vectorSpan k s → ∃ r, r • v = v_1
    intro w hw
    -- ⊢ ∃ r, r • v = w
    have hs : vectorSpan k s ≤ k ∙ v := by
      rw [vectorSpan_eq_span_vsub_set_right k h, Submodule.span_le, Set.subset_def]
      intro x hx
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      rw [Set.mem_image] at hx
      rcases hx with ⟨p, hp, rfl⟩
      rcases hp₀v p hp with ⟨r, rfl⟩
      use r
      simp
    have hw' := SetLike.le_def.1 hs hw
    -- ⊢ ∃ r, r • v = w
    rwa [Submodule.mem_span_singleton] at hw'
    -- 🎉 no goals
#align collinear_iff_of_mem collinear_iff_of_mem

/-- A set of points is collinear if and only if they can all be
expressed as multiples of the same vector, added to the same base
point. -/
theorem collinear_iff_exists_forall_eq_smul_vadd (s : Set P) :
    Collinear k s ↔ ∃ (p₀ : P) (v : V), ∀ p ∈ s, ∃ r : k, p = r • v +ᵥ p₀ := by
  rcases Set.eq_empty_or_nonempty s with (rfl | ⟨⟨p₁, hp₁⟩⟩)
  -- ⊢ Collinear k ∅ ↔ ∃ p₀ v, ∀ (p : P), p ∈ ∅ → ∃ r, p = r • v +ᵥ p₀
  · simp [collinear_empty]
    -- 🎉 no goals
  · rw [collinear_iff_of_mem hp₁]
    -- ⊢ (∃ v, ∀ (p : P), p ∈ s → ∃ r, p = r • v +ᵥ p₁) ↔ ∃ p₀ v, ∀ (p : P), p ∈ s →  …
    constructor
    -- ⊢ (∃ v, ∀ (p : P), p ∈ s → ∃ r, p = r • v +ᵥ p₁) → ∃ p₀ v, ∀ (p : P), p ∈ s →  …
    · exact fun h => ⟨p₁, h⟩
      -- 🎉 no goals
    · rintro ⟨p, v, hv⟩
      -- ⊢ ∃ v, ∀ (p : P), p ∈ s → ∃ r, p = r • v +ᵥ p₁
      use v
      -- ⊢ ∀ (p : P), p ∈ s → ∃ r, p = r • v +ᵥ p₁
      intro p₂ hp₂
      -- ⊢ ∃ r, p₂ = r • v +ᵥ p₁
      rcases hv p₂ hp₂ with ⟨r, rfl⟩
      -- ⊢ ∃ r_1, r • v +ᵥ p = r_1 • v +ᵥ p₁
      rcases hv p₁ hp₁ with ⟨r₁, rfl⟩
      -- ⊢ ∃ r_1, r • v +ᵥ p = r_1 • v +ᵥ (r₁ • v +ᵥ p)
      use r - r₁
      -- ⊢ r • v +ᵥ p = (r - r₁) • v +ᵥ (r₁ • v +ᵥ p)
      simp [vadd_vadd, ← add_smul]
      -- 🎉 no goals
#align collinear_iff_exists_forall_eq_smul_vadd collinear_iff_exists_forall_eq_smul_vadd

variable (k)

/-- Two points are collinear. -/
theorem collinear_pair (p₁ p₂ : P) : Collinear k ({p₁, p₂} : Set P) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  -- ⊢ ∃ p₀ v, ∀ (p : P), p ∈ {p₁, p₂} → ∃ r, p = r • v +ᵥ p₀
  use p₁, p₂ -ᵥ p₁
  -- ⊢ ∀ (p : P), p ∈ {p₁, p₂} → ∃ r, p = r • (p₂ -ᵥ p₁) +ᵥ p₁
  intro p hp
  -- ⊢ ∃ r, p = r • (p₂ -ᵥ p₁) +ᵥ p₁
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  -- ⊢ ∃ r, p = r • (p₂ -ᵥ p₁) +ᵥ p₁
  cases' hp with hp hp
  -- ⊢ ∃ r, p = r • (p₂ -ᵥ p₁) +ᵥ p₁
  · use 0
    -- ⊢ p = 0 • (p₂ -ᵥ p₁) +ᵥ p₁
    simp [hp]
    -- 🎉 no goals
  · use 1
    -- ⊢ p = 1 • (p₂ -ᵥ p₁) +ᵥ p₁
    simp [hp]
    -- 🎉 no goals
#align collinear_pair collinear_pair

variable {k}

/-- Three points are affinely independent if and only if they are not
collinear. -/
theorem affineIndependent_iff_not_collinear {p : Fin 3 → P} :
    AffineIndependent k p ↔ ¬Collinear k (Set.range p) := by
  rw [collinear_iff_finrank_le_one,
    affineIndependent_iff_not_finrank_vectorSpan_le k p (Fintype.card_fin 3)]
#align affine_independent_iff_not_collinear affineIndependent_iff_not_collinear

/-- Three points are collinear if and only if they are not affinely
independent. -/
theorem collinear_iff_not_affineIndependent {p : Fin 3 → P} :
    Collinear k (Set.range p) ↔ ¬AffineIndependent k p := by
  rw [collinear_iff_finrank_le_one,
    finrank_vectorSpan_le_iff_not_affineIndependent k p (Fintype.card_fin 3)]
#align collinear_iff_not_affine_independent collinear_iff_not_affineIndependent

/-- Three points are affinely independent if and only if they are not collinear. -/
theorem affineIndependent_iff_not_collinear_set {p₁ p₂ p₃ : P} :
    AffineIndependent k ![p₁, p₂, p₃] ↔ ¬Collinear k ({p₁, p₂, p₃} : Set P) := by
  rw [affineIndependent_iff_not_collinear]
  -- ⊢ ¬Collinear k (Set.range ![p₁, p₂, p₃]) ↔ ¬Collinear k {p₁, p₂, p₃}
  simp_rw [Matrix.range_cons, Matrix.range_empty, Set.singleton_union, insert_emptyc_eq]
  -- 🎉 no goals
#align affine_independent_iff_not_collinear_set affineIndependent_iff_not_collinear_set

/-- Three points are collinear if and only if they are not affinely independent. -/
theorem collinear_iff_not_affineIndependent_set {p₁ p₂ p₃ : P} :
    Collinear k ({p₁, p₂, p₃} : Set P) ↔ ¬AffineIndependent k ![p₁, p₂, p₃] :=
  affineIndependent_iff_not_collinear_set.not_left.symm
#align collinear_iff_not_affine_independent_set collinear_iff_not_affineIndependent_set

/-- Three points are affinely independent if and only if they are not collinear. -/
theorem affineIndependent_iff_not_collinear_of_ne {p : Fin 3 → P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    AffineIndependent k p ↔ ¬Collinear k ({p i₁, p i₂, p i₃} : Set P) := by
  have hu : (Finset.univ : Finset (Fin 3)) = {i₁, i₂, i₃} := by
    -- Porting note: Originally `by decide!`
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases i₃ <;> simp only at h₁₂ h₁₃ h₂₃ ⊢
  rw [affineIndependent_iff_not_collinear, ← Set.image_univ, ← Finset.coe_univ, hu,
    Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_pair]
#align affine_independent_iff_not_collinear_of_ne affineIndependent_iff_not_collinear_of_ne

/-- Three points are collinear if and only if they are not affinely independent. -/
theorem collinear_iff_not_affineIndependent_of_ne {p : Fin 3 → P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    Collinear k ({p i₁, p i₂, p i₃} : Set P) ↔ ¬AffineIndependent k p :=
  (affineIndependent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃).not_left.symm
#align collinear_iff_not_affine_independent_of_ne collinear_iff_not_affineIndependent_of_ne

/-- If three points are not collinear, the first and second are different. -/
theorem ne₁₂_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P)) :
    p₁ ≠ p₂ := by
  rintro rfl
  -- ⊢ False
  simp [collinear_pair] at h
  -- 🎉 no goals
#align ne₁₂_of_not_collinear ne₁₂_of_not_collinear

/-- If three points are not collinear, the first and third are different. -/
theorem ne₁₃_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P)) :
    p₁ ≠ p₃ := by
  rintro rfl
  -- ⊢ False
  simp [collinear_pair] at h
  -- 🎉 no goals
#align ne₁₃_of_not_collinear ne₁₃_of_not_collinear

/-- If three points are not collinear, the second and third are different. -/
theorem ne₂₃_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P)) :
    p₂ ≠ p₃ := by
  rintro rfl
  -- ⊢ False
  simp [collinear_pair] at h
  -- 🎉 no goals
#align ne₂₃_of_not_collinear ne₂₃_of_not_collinear

/-- A point in a collinear set of points lies in the affine span of any two distinct points of
that set. -/
theorem Collinear.mem_affineSpan_of_mem_of_ne {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₁p₂ : p₁ ≠ p₂) : p₃ ∈ line[k, p₁, p₂] := by
  rw [collinear_iff_of_mem hp₁] at h
  -- ⊢ p₃ ∈ affineSpan k {p₁, p₂}
  rcases h with ⟨v, h⟩
  -- ⊢ p₃ ∈ affineSpan k {p₁, p₂}
  rcases h p₂ hp₂ with ⟨r₂, rfl⟩
  -- ⊢ p₃ ∈ affineSpan k {p₁, r₂ • v +ᵥ p₁}
  rcases h p₃ hp₃ with ⟨r₃, rfl⟩
  -- ⊢ r₃ • v +ᵥ p₁ ∈ affineSpan k {p₁, r₂ • v +ᵥ p₁}
  rw [vadd_left_mem_affineSpan_pair]
  -- ⊢ ∃ r, r • (r₂ • v +ᵥ p₁ -ᵥ p₁) = r₃ • v
  refine' ⟨r₃ / r₂, _⟩
  -- ⊢ (r₃ / r₂) • (r₂ • v +ᵥ p₁ -ᵥ p₁) = r₃ • v
  have h₂ : r₂ ≠ 0 := by
    rintro rfl
    simp at hp₁p₂
  simp [smul_smul, h₂]
  -- 🎉 no goals
#align collinear.mem_affine_span_of_mem_of_ne Collinear.mem_affineSpan_of_mem_of_ne

/-- The affine span of any two distinct points of a collinear set of points equals the affine
span of the whole set. -/
theorem Collinear.affineSpan_eq_of_ne {s : Set P} (h : Collinear k s) {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (hp₁p₂ : p₁ ≠ p₂) : line[k, p₁, p₂] = affineSpan k s :=
  le_antisymm (affineSpan_mono _ (Set.insert_subset_iff.2 ⟨hp₁, Set.singleton_subset_iff.2 hp₂⟩))
    (affineSpan_le.2 fun _ hp => h.mem_affineSpan_of_mem_of_ne hp₁ hp₂ hp hp₁p₂)
#align collinear.affine_span_eq_of_ne Collinear.affineSpan_eq_of_ne

/-- Given a collinear set of points, and two distinct points `p₂` and `p₃` in it, a point `p₁` is
collinear with the set if and only if it is collinear with `p₂` and `p₃`. -/
theorem Collinear.collinear_insert_iff_of_ne {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P}
    (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₂p₃ : p₂ ≠ p₃) :
    Collinear k (insert p₁ s) ↔ Collinear k ({p₁, p₂, p₃} : Set P) := by
  have hv : vectorSpan k (insert p₁ s) = vectorSpan k ({p₁, p₂, p₃} : Set P) := by
    -- Porting note: Original proof used `conv_lhs` and `conv_rhs`, but these tactics timed out.
    rw [← direction_affineSpan, ← affineSpan_insert_affineSpan]
    symm
    rw [← direction_affineSpan, ← affineSpan_insert_affineSpan, h.affineSpan_eq_of_ne hp₂ hp₃ hp₂p₃]
  rw [Collinear, Collinear, hv]
  -- 🎉 no goals
#align collinear.collinear_insert_iff_of_ne Collinear.collinear_insert_iff_of_ne

/-- Adding a point in the affine span of a set does not change whether that set is collinear. -/
theorem collinear_insert_iff_of_mem_affineSpan {s : Set P} {p : P} (h : p ∈ affineSpan k s) :
    Collinear k (insert p s) ↔ Collinear k s := by
  rw [Collinear, Collinear, vectorSpan_insert_eq_vectorSpan h]
  -- 🎉 no goals
#align collinear_insert_iff_of_mem_affine_span collinear_insert_iff_of_mem_affineSpan

/-- If a point lies in the affine span of two points, those three points are collinear. -/
theorem collinear_insert_of_mem_affineSpan_pair {p₁ p₂ p₃ : P} (h : p₁ ∈ line[k, p₂, p₃]) :
    Collinear k ({p₁, p₂, p₃} : Set P) := by
  rw [collinear_insert_iff_of_mem_affineSpan h]
  -- ⊢ Collinear k {p₂, p₃}
  exact collinear_pair _ _ _
  -- 🎉 no goals
#align collinear_insert_of_mem_affine_span_pair collinear_insert_of_mem_affineSpan_pair

/-- If two points lie in the affine span of two points, those four points are collinear. -/
theorem collinear_insert_insert_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ : P} (h₁ : p₁ ∈ line[k, p₃, p₄])
    (h₂ : p₂ ∈ line[k, p₃, p₄]) : Collinear k ({p₁, p₂, p₃, p₄} : Set P) := by
  rw [collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1 (affineSpan_mono k (Set.subset_insert _ _)) _ h₁),
    collinear_insert_iff_of_mem_affineSpan h₂]
  exact collinear_pair _ _ _
  -- 🎉 no goals
#align collinear_insert_insert_of_mem_affine_span_pair collinear_insert_insert_of_mem_affineSpan_pair

/-- If three points lie in the affine span of two points, those five points are collinear. -/
theorem collinear_insert_insert_insert_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ p₅ : P}
    (h₁ : p₁ ∈ line[k, p₄, p₅]) (h₂ : p₂ ∈ line[k, p₄, p₅]) (h₃ : p₃ ∈ line[k, p₄, p₅]) :
    Collinear k ({p₁, p₂, p₃, p₄, p₅} : Set P) := by
  rw [collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1
        (affineSpan_mono k ((Set.subset_insert _ _).trans (Set.subset_insert _ _))) _ h₁),
    collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1 (affineSpan_mono k (Set.subset_insert _ _)) _ h₂),
    collinear_insert_iff_of_mem_affineSpan h₃]
  exact collinear_pair _ _ _
  -- 🎉 no goals
#align collinear_insert_insert_insert_of_mem_affine_span_pair collinear_insert_insert_insert_of_mem_affineSpan_pair

/-- If three points lie in the affine span of two points, the first four points are collinear. -/
theorem collinear_insert_insert_insert_left_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ p₅ : P}
    (h₁ : p₁ ∈ line[k, p₄, p₅]) (h₂ : p₂ ∈ line[k, p₄, p₅]) (h₃ : p₃ ∈ line[k, p₄, p₅]) :
    Collinear k ({p₁, p₂, p₃, p₄} : Set P) := by
  refine' (collinear_insert_insert_insert_of_mem_affineSpan_pair h₁ h₂ h₃).subset _
  -- ⊢ {p₁, p₂, p₃, p₄} ⊆ {p₁, p₂, p₃, p₄, p₅}
  repeat apply Set.insert_subset_insert
  -- ⊢ {p₄} ⊆ {p₄, p₅}
  simp
  -- 🎉 no goals
#align collinear_insert_insert_insert_left_of_mem_affine_span_pair collinear_insert_insert_insert_left_of_mem_affineSpan_pair

/-- If three points lie in the affine span of two points, the first three points are collinear. -/
theorem collinear_triple_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ p₅ : P} (h₁ : p₁ ∈ line[k, p₄, p₅])
    (h₂ : p₂ ∈ line[k, p₄, p₅]) (h₃ : p₃ ∈ line[k, p₄, p₅]) :
    Collinear k ({p₁, p₂, p₃} : Set P) := by
  refine' (collinear_insert_insert_insert_left_of_mem_affineSpan_pair h₁ h₂ h₃).subset _
  -- ⊢ {p₁, p₂, p₃} ⊆ {p₁, p₂, p₃, p₄}
  simp [Set.insert_subset_insert]
  -- 🎉 no goals
#align collinear_triple_of_mem_affine_span_pair collinear_triple_of_mem_affineSpan_pair

variable (k)

/-- A set of points is coplanar if their `vectorSpan` has dimension at most `2`. -/
def Coplanar (s : Set P) : Prop :=
  Module.rank k (vectorSpan k s) ≤ 2
#align coplanar Coplanar

variable {k}

/-- The `vectorSpan` of coplanar points is finite-dimensional. -/
theorem Coplanar.finiteDimensional_vectorSpan {s : Set P} (h : Coplanar k s) :
    FiniteDimensional k (vectorSpan k s) := by
  refine' IsNoetherian.iff_fg.1 (IsNoetherian.iff_rank_lt_aleph0.2 (lt_of_le_of_lt h _))
  -- ⊢ 2 < Cardinal.aleph0
  exact Cardinal.lt_aleph0.2 ⟨2, rfl⟩
  -- 🎉 no goals
#align coplanar.finite_dimensional_vector_span Coplanar.finiteDimensional_vectorSpan

/-- The direction of the affine span of coplanar points is finite-dimensional. -/
theorem Coplanar.finiteDimensional_direction_affineSpan {s : Set P} (h : Coplanar k s) :
    FiniteDimensional k (affineSpan k s).direction :=
  (direction_affineSpan k s).symm ▸ h.finiteDimensional_vectorSpan
#align coplanar.finite_dimensional_direction_affine_span Coplanar.finiteDimensional_direction_affineSpan

/-- A set of points, whose `vectorSpan` is finite-dimensional, is coplanar if and only if their
`vectorSpan` has dimension at most `2`. -/
theorem coplanar_iff_finrank_le_two {s : Set P} [FiniteDimensional k (vectorSpan k s)] :
    Coplanar k s ↔ finrank k (vectorSpan k s) ≤ 2 := by
  have h : Coplanar k s ↔ Module.rank k (vectorSpan k s) ≤ 2 := Iff.rfl
  -- ⊢ Coplanar k s ↔ finrank k { x // x ∈ vectorSpan k s } ≤ 2
  rw [← finrank_eq_rank] at h
  -- ⊢ Coplanar k s ↔ finrank k { x // x ∈ vectorSpan k s } ≤ 2
  exact_mod_cast h
  -- 🎉 no goals
#align coplanar_iff_finrank_le_two coplanar_iff_finrank_le_two

alias ⟨Coplanar.finrank_le_two, _⟩ := coplanar_iff_finrank_le_two
#align coplanar.finrank_le_two Coplanar.finrank_le_two

/-- A subset of a coplanar set is coplanar. -/
theorem Coplanar.subset {s₁ s₂ : Set P} (hs : s₁ ⊆ s₂) (h : Coplanar k s₂) : Coplanar k s₁ :=
  (rank_le_of_submodule (vectorSpan k s₁) (vectorSpan k s₂) (vectorSpan_mono k hs)).trans h
#align coplanar.subset Coplanar.subset

/-- Collinear points are coplanar. -/
theorem Collinear.coplanar {s : Set P} (h : Collinear k s) : Coplanar k s :=
  le_trans h one_le_two
#align collinear.coplanar Collinear.coplanar

variable (k) (P)

/-- The empty set is coplanar. -/
theorem coplanar_empty : Coplanar k (∅ : Set P) :=
  (collinear_empty k P).coplanar
#align coplanar_empty coplanar_empty

variable {P}

/-- A single point is coplanar. -/
theorem coplanar_singleton (p : P) : Coplanar k ({p} : Set P) :=
  (collinear_singleton k p).coplanar
#align coplanar_singleton coplanar_singleton

/-- Two points are coplanar. -/
theorem coplanar_pair (p₁ p₂ : P) : Coplanar k ({p₁, p₂} : Set P) :=
  (collinear_pair k p₁ p₂).coplanar
#align coplanar_pair coplanar_pair

variable {k}

/-- Adding a point in the affine span of a set does not change whether that set is coplanar. -/
theorem coplanar_insert_iff_of_mem_affineSpan {s : Set P} {p : P} (h : p ∈ affineSpan k s) :
    Coplanar k (insert p s) ↔ Coplanar k s := by
  rw [Coplanar, Coplanar, vectorSpan_insert_eq_vectorSpan h]
  -- 🎉 no goals
#align coplanar_insert_iff_of_mem_affine_span coplanar_insert_iff_of_mem_affineSpan

end AffineSpace'

section DivisionRing

variable {k : Type*} {V : Type*} {P : Type*}

open AffineSubspace FiniteDimensional Module

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- Adding a point to a finite-dimensional subspace increases the dimension by at most one. -/
theorem finrank_vectorSpan_insert_le (s : AffineSubspace k P) (p : P) :
    finrank k (vectorSpan k (insert p (s : Set P))) ≤ finrank k s.direction + 1 := by
  by_cases hf : FiniteDimensional k s.direction; swap
  -- ⊢ finrank k { x // x ∈ vectorSpan k (insert p ↑s) } ≤ finrank k { x // x ∈ dir …
                                                 -- ⊢ finrank k { x // x ∈ vectorSpan k (insert p ↑s) } ≤ finrank k { x // x ∈ dir …
  · have hf' : ¬FiniteDimensional k (vectorSpan k (insert p (s : Set P))) := by
      intro h
      have h' : s.direction ≤ vectorSpan k (insert p (s : Set P)) := by
        conv_lhs => rw [← affineSpan_coe s, direction_affineSpan]
        exact vectorSpan_mono k (Set.subset_insert _ _)
      exact hf (Submodule.finiteDimensional_of_le h')
    rw [finrank_of_infinite_dimensional hf, finrank_of_infinite_dimensional hf', zero_add]
    -- ⊢ 0 ≤ 1
    exact zero_le_one
    -- 🎉 no goals
  have : FiniteDimensional k s.direction := hf
  -- ⊢ finrank k { x // x ∈ vectorSpan k (insert p ↑s) } ≤ finrank k { x // x ∈ dir …
  rw [← direction_affineSpan, ← affineSpan_insert_affineSpan]
  -- ⊢ finrank k { x // x ∈ direction (affineSpan k (insert p ↑(affineSpan k ↑s)))  …
  rcases (s : Set P).eq_empty_or_nonempty with (hs | ⟨p₀, hp₀⟩)
  -- ⊢ finrank k { x // x ∈ direction (affineSpan k (insert p ↑(affineSpan k ↑s)))  …
  · rw [coe_eq_bot_iff] at hs
    -- ⊢ finrank k { x // x ∈ direction (affineSpan k (insert p ↑(affineSpan k ↑s)))  …
    rw [hs, bot_coe, span_empty, bot_coe, direction_affineSpan, direction_bot, finrank_bot,
      zero_add]
    convert zero_le_one' ℕ
    -- ⊢ finrank k { x // x ∈ vectorSpan k (insert p ∅) } = 0
    rw [← finrank_bot k V]
    -- ⊢ finrank k { x // x ∈ vectorSpan k (insert p ∅) } = finrank k { x // x ∈ ⊥ }
    convert rfl <;> simp
                    -- 🎉 no goals
                    -- 🎉 no goals
                    -- 🎉 no goals
  · rw [affineSpan_coe, direction_affineSpan_insert hp₀, add_comm]
    -- ⊢ finrank k { x // x ∈ Submodule.span k {p -ᵥ p₀} ⊔ direction s } ≤ 1 + finran …
    refine' (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (add_le_add_right _ _)
    -- ⊢ finrank k { x // x ∈ Submodule.span k {p -ᵥ p₀} } ≤ 1
    refine' finrank_le_one ⟨p -ᵥ p₀, Submodule.mem_span_singleton_self _⟩ fun v => _
    -- ⊢ ∃ c, c • { val := p -ᵥ p₀, property := (_ : p -ᵥ p₀ ∈ Submodule.span k {p -ᵥ …
    have h := v.property
    -- ⊢ ∃ c, c • { val := p -ᵥ p₀, property := (_ : p -ᵥ p₀ ∈ Submodule.span k {p -ᵥ …
    rw [Submodule.mem_span_singleton] at h
    -- ⊢ ∃ c, c • { val := p -ᵥ p₀, property := (_ : p -ᵥ p₀ ∈ Submodule.span k {p -ᵥ …
    rcases h with ⟨c, hc⟩
    -- ⊢ ∃ c, c • { val := p -ᵥ p₀, property := (_ : p -ᵥ p₀ ∈ Submodule.span k {p -ᵥ …
    refine' ⟨c, _⟩
    -- ⊢ c • { val := p -ᵥ p₀, property := (_ : p -ᵥ p₀ ∈ Submodule.span k {p -ᵥ p₀}) …
    ext
    -- ⊢ ↑(c • { val := p -ᵥ p₀, property := (_ : p -ᵥ p₀ ∈ Submodule.span k {p -ᵥ p₀ …
    exact hc
    -- 🎉 no goals
#align finrank_vector_span_insert_le finrank_vectorSpan_insert_le

variable (k)

/-- Adding a point to a set with a finite-dimensional span increases the dimension by at most
one. -/
theorem finrank_vectorSpan_insert_le_set (s : Set P) (p : P) :
    finrank k (vectorSpan k (insert p s)) ≤ finrank k (vectorSpan k s) + 1 := by
  rw [← direction_affineSpan, ← affineSpan_insert_affineSpan, direction_affineSpan]
  -- ⊢ finrank k { x // x ∈ vectorSpan k (insert p ↑(affineSpan k s)) } ≤ finrank k …
  refine' (finrank_vectorSpan_insert_le _ _).trans (add_le_add_right _ _)
  -- ⊢ finrank k { x // x ∈ direction (affineSpan k s) } ≤ finrank k { x // x ∈ vec …
  rw [direction_affineSpan]
  -- 🎉 no goals
#align finrank_vector_span_insert_le_set finrank_vectorSpan_insert_le_set

variable {k}

/-- Adding a point to a collinear set produces a coplanar set. -/
theorem Collinear.coplanar_insert {s : Set P} (h : Collinear k s) (p : P) :
    Coplanar k (insert p s) := by
  have : FiniteDimensional k { x // x ∈ vectorSpan k s } := h.finiteDimensional_vectorSpan
  -- ⊢ Coplanar k (insert p s)
  rw [coplanar_iff_finrank_le_two]
  -- ⊢ finrank k { x // x ∈ vectorSpan k (insert p s) } ≤ 2
  exact (finrank_vectorSpan_insert_le_set k s p).trans (add_le_add_right h.finrank_le_one _)
  -- 🎉 no goals
#align collinear.coplanar_insert Collinear.coplanar_insert

/-- A set of points in a two-dimensional space is coplanar. -/
theorem coplanar_of_finrank_eq_two (s : Set P) (h : finrank k V = 2) : Coplanar k s := by
  have : FiniteDimensional k V := finiteDimensional_of_finrank_eq_succ h
  -- ⊢ Coplanar k s
  rw [coplanar_iff_finrank_le_two, ← h]
  -- ⊢ finrank k { x // x ∈ vectorSpan k s } ≤ finrank k V
  exact Submodule.finrank_le _
  -- 🎉 no goals
#align coplanar_of_finrank_eq_two coplanar_of_finrank_eq_two

/-- A set of points in a two-dimensional space is coplanar. -/
theorem coplanar_of_fact_finrank_eq_two (s : Set P) [h : Fact (finrank k V = 2)] : Coplanar k s :=
  coplanar_of_finrank_eq_two s h.out
#align coplanar_of_fact_finrank_eq_two coplanar_of_fact_finrank_eq_two

variable (k)

/-- Three points are coplanar. -/
theorem coplanar_triple (p₁ p₂ p₃ : P) : Coplanar k ({p₁, p₂, p₃} : Set P) :=
  (collinear_pair k p₂ p₃).coplanar_insert p₁
#align coplanar_triple coplanar_triple

end DivisionRing

namespace AffineBasis

universe u₁ u₂ u₃ u₄

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AffineSpace V P]

section DivisionRing

variable [DivisionRing k] [Module k V]

protected theorem finiteDimensional [Finite ι] (b : AffineBasis ι k P) : FiniteDimensional k V :=
  let ⟨i⟩ := b.nonempty
  FiniteDimensional.of_fintype_basis (b.basisOf i)
#align affine_basis.finite_dimensional AffineBasis.finiteDimensional

protected theorem finite [FiniteDimensional k V] (b : AffineBasis ι k P) : Finite ι :=
  finite_of_fin_dim_affineIndependent k b.ind
#align affine_basis.finite AffineBasis.finite

protected theorem finite_set [FiniteDimensional k V] {s : Set ι} (b : AffineBasis s k P) :
    s.Finite :=
  finite_set_of_fin_dim_affineIndependent k b.ind
#align affine_basis.finite_set AffineBasis.finite_set

theorem card_eq_finrank_add_one [Fintype ι] (b : AffineBasis ι k P) :
    Fintype.card ι = FiniteDimensional.finrank k V + 1 :=
  have : FiniteDimensional k V := b.finiteDimensional
  b.ind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp b.tot
#align affine_basis.card_eq_finrank_add_one AffineBasis.card_eq_finrank_add_one

theorem exists_affineBasis_of_finiteDimensional [Fintype ι] [FiniteDimensional k V]
    (h : Fintype.card ι = FiniteDimensional.finrank k V + 1) : Nonempty (AffineBasis ι k P) := by
  obtain ⟨s, b, hb⟩ := AffineBasis.exists_affineBasis k V P
  -- ⊢ Nonempty (AffineBasis ι k P)
  lift s to Finset P using b.finite_set
  -- ⊢ Nonempty (AffineBasis ι k P)
  refine' ⟨b.reindex <| Fintype.equivOfCardEq _⟩
  -- ⊢ Fintype.card ↑↑s = Fintype.card ι
  rw [h, ← b.card_eq_finrank_add_one]
  -- 🎉 no goals
#align affine_basis.exists_affine_basis_of_finite_dimensional AffineBasis.exists_affineBasis_of_finiteDimensional

end DivisionRing

end AffineBasis
