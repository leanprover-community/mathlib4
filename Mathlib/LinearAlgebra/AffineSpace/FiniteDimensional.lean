/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite-dimensional subspaces of affine spaces.

This file provides a few results relating to finite-dimensional
subspaces of affine spaces.

## Main definitions

* `Collinear` defines collinear sets of points as those that span a
  subspace of dimension at most 1.

-/


noncomputable section

open Affine
open scoped Finset

section AffineSpace'

variable (k : Type*) {V : Type*} {P : Type*}
variable {ι : Type*}

open AffineSubspace Module

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- The `vectorSpan` of a finite set is finite-dimensional. -/
theorem finiteDimensional_vectorSpan_of_finite {s : Set P} (h : Set.Finite s) :
    FiniteDimensional k (vectorSpan k s) :=
  .span_of_finite k <| h.vsub h

/-- The vector span of a singleton is finite-dimensional. -/
instance finiteDimensional_vectorSpan_singleton (p : P) :
    FiniteDimensional k (vectorSpan k {p}) :=
  finiteDimensional_vectorSpan_of_finite _ (Set.finite_singleton p)

/-- The `vectorSpan` of a family indexed by a `Fintype` is
finite-dimensional. -/
instance finiteDimensional_vectorSpan_range [Finite ι] (p : ι → P) :
    FiniteDimensional k (vectorSpan k (Set.range p)) :=
  finiteDimensional_vectorSpan_of_finite k (Set.finite_range _)

/-- The `vectorSpan` of a subset of a family indexed by a `Fintype`
is finite-dimensional. -/
instance finiteDimensional_vectorSpan_image_of_finite [Finite ι] (p : ι → P) (s : Set ι) :
    FiniteDimensional k (vectorSpan k (p '' s)) :=
  finiteDimensional_vectorSpan_of_finite k (Set.toFinite _)

/-- The direction of the affine span of a finite set is
finite-dimensional. -/
theorem finiteDimensional_direction_affineSpan_of_finite {s : Set P} (h : Set.Finite s) :
    FiniteDimensional k (affineSpan k s).direction :=
  (direction_affineSpan k s).symm ▸ finiteDimensional_vectorSpan_of_finite k h

/-- The direction of the affine span of a singleton is finite-dimensional. -/
instance finiteDimensional_direction_affineSpan_singleton (p : P) :
    FiniteDimensional k (affineSpan k {p}).direction := by
  rw [direction_affineSpan]
  infer_instance

/-- The direction of the affine span of a family indexed by a
`Fintype` is finite-dimensional. -/
instance finiteDimensional_direction_affineSpan_range [Finite ι] (p : ι → P) :
    FiniteDimensional k (affineSpan k (Set.range p)).direction :=
  finiteDimensional_direction_affineSpan_of_finite k (Set.finite_range _)

/-- The direction of the affine span of a subset of a family indexed
by a `Fintype` is finite-dimensional. -/
instance finiteDimensional_direction_affineSpan_image_of_finite [Finite ι] (p : ι → P) (s : Set ι) :
    FiniteDimensional k (affineSpan k (p '' s)).direction :=
  finiteDimensional_direction_affineSpan_of_finite k (Set.toFinite _)

/-- An affine-independent family of points in a finite-dimensional affine space is finite. -/
theorem finite_of_fin_dim_affineIndependent [FiniteDimensional k V] {p : ι → P}
    (hi : AffineIndependent k p) : Finite ι := by
  nontriviality ι; inhabit ι
  rw [affineIndependent_iff_linearIndependent_vsub k p default] at hi
  letI : IsNoetherian k V := IsNoetherian.iff_fg.2 inferInstance
  exact
    (Set.finite_singleton default).finite_of_compl (Set.finite_coe_iff.1 hi.finite_of_isNoetherian)

/-- An affine-independent subset of a finite-dimensional affine space is finite. -/
theorem finite_set_of_fin_dim_affineIndependent [FiniteDimensional k V] {s : Set ι} {f : s → P}
    (hi : AffineIndependent k f) : s.Finite :=
  @Set.toFinite _ s (finite_of_fin_dim_affineIndependent k hi)

variable {k}

/-- The supremum of two finite-dimensional affine subspaces is finite-dimensional. -/
instance AffineSubspace.finiteDimensional_sup (s₁ s₂ : AffineSubspace k P)
    [FiniteDimensional k s₁.direction] [FiniteDimensional k s₂.direction] :
    FiniteDimensional k (s₁ ⊔ s₂).direction := by
  rcases eq_bot_or_nonempty s₁ with rfl | ⟨p₁, hp₁⟩
  · rwa [bot_sup_eq]
  rcases eq_bot_or_nonempty s₂ with rfl | ⟨p₂, hp₂⟩
  · rwa [sup_bot_eq]
  rw [AffineSubspace.direction_sup hp₁ hp₂]
  infer_instance

/-- The `vectorSpan` of a finite subset of an affinely independent
family has dimension one less than its cardinality. -/
theorem AffineIndependent.finrank_vectorSpan_image_finset [DecidableEq P]
    {p : ι → P} (hi : AffineIndependent k p) {s : Finset ι} {n : ℕ} (hc : #s = n + 1) :
    finrank k (vectorSpan k (s.image p : Set P)) = n := by
  classical
  have hi' := hi.range.mono (Set.image_subset_range p ↑s)
  have hc' : #(s.image p) = n + 1 := by rwa [s.card_image_of_injective hi.injective]
  have hn : (s.image p).Nonempty := by simp [hc', ← Finset.card_pos]
  rcases hn with ⟨p₁, hp₁⟩
  have hp₁' : p₁ ∈ p '' s := by simpa using hp₁
  rw [affineIndependent_set_iff_linearIndependent_vsub k hp₁', ← Finset.coe_singleton,
    ← Finset.coe_image, ← Finset.coe_sdiff, Finset.sdiff_singleton_eq_erase, ← Finset.coe_image]
    at hi'
  have hc : #(((s.image p).erase p₁).image (· -ᵥ p₁)) = n := by
    rw [Finset.card_image_of_injective _ (vsub_left_injective _), Finset.card_erase_of_mem hp₁]
    exact Nat.pred_eq_of_eq_succ hc'
  rwa [vectorSpan_eq_span_vsub_finset_right_ne k hp₁, finrank_span_finset_eq_card, hc]

/-- The `vectorSpan` of a finite affinely independent family has
dimension one less than its cardinality. -/
theorem AffineIndependent.finrank_vectorSpan [Fintype ι] {p : ι → P} (hi : AffineIndependent k p)
    {n : ℕ} (hc : Fintype.card ι = n + 1) : finrank k (vectorSpan k (Set.range p)) = n := by
  classical
  rw [← Finset.card_univ] at hc
  rw [← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image]
  exact hi.finrank_vectorSpan_image_finset hc

/-- The `vectorSpan` of a finite affinely independent family has dimension one less than its
cardinality. -/
lemma AffineIndependent.finrank_vectorSpan_add_one [Fintype ι] [Nonempty ι] {p : ι → P}
    (hi : AffineIndependent k p) : finrank k (vectorSpan k (Set.range p)) + 1 = Fintype.card ι := by
  rw [hi.finrank_vectorSpan (tsub_add_cancel_of_le _).symm, tsub_add_cancel_of_le] <;>
    exact Fintype.card_pos

/-- The `vectorSpan` of a finite affinely independent family whose
cardinality is one more than that of the finite-dimensional space is
`⊤`. -/
theorem AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one [FiniteDimensional k V]
    [Fintype ι] {p : ι → P} (hi : AffineIndependent k p) (hc : Fintype.card ι = finrank k V + 1) :
    vectorSpan k (Set.range p) = ⊤ :=
  Submodule.eq_top_of_finrank_eq <| hi.finrank_vectorSpan hc

variable (k)

/-- The `vectorSpan` of `n + 1` points in an indexed family has
dimension at most `n`. -/
theorem finrank_vectorSpan_image_finset_le [DecidableEq P] (p : ι → P) (s : Finset ι) {n : ℕ}
    (hc : #s = n + 1) : finrank k (vectorSpan k (s.image p : Set P)) ≤ n := by
  classical
  have hn : (s.image p).Nonempty := by
    rw [Finset.image_nonempty, ← Finset.card_pos, hc]
    apply Nat.succ_pos
  rcases hn with ⟨p₁, hp₁⟩
  rw [vectorSpan_eq_span_vsub_finset_right_ne k hp₁]
  refine le_trans (finrank_span_finset_le_card (((s.image p).erase p₁).image fun p => p -ᵥ p₁)) ?_
  rw [Finset.card_image_of_injective _ (vsub_left_injective p₁), Finset.card_erase_of_mem hp₁,
    tsub_le_iff_right, ← hc]
  apply Finset.card_image_le

/-- The `vectorSpan` of an indexed family of `n + 1` points has
dimension at most `n`. -/
theorem finrank_vectorSpan_range_le [Fintype ι] (p : ι → P) {n : ℕ} (hc : Fintype.card ι = n + 1) :
    finrank k (vectorSpan k (Set.range p)) ≤ n := by
  classical
  rw [← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image]
  rw [← Finset.card_univ] at hc
  exact finrank_vectorSpan_image_finset_le _ _ _ hc

/-- The `vectorSpan` of an indexed family of `n + 1` points has dimension at most `n`. -/
lemma finrank_vectorSpan_range_add_one_le [Fintype ι] [Nonempty ι] (p : ι → P) :
    finrank k (vectorSpan k (Set.range p)) + 1 ≤ Fintype.card ι :=
  (le_tsub_iff_right <| Nat.succ_le_iff.2 Fintype.card_pos).1 <| finrank_vectorSpan_range_le _ _
    (tsub_add_cancel_of_le <| Nat.succ_le_iff.2 Fintype.card_pos).symm

/-- `n + 1` points are affinely independent if and only if their
`vectorSpan` has dimension `n`. -/
theorem affineIndependent_iff_finrank_vectorSpan_eq [Fintype ι] (p : ι → P) {n : ℕ}
    (hc : Fintype.card ι = n + 1) :
    AffineIndependent k p ↔ finrank k (vectorSpan k (Set.range p)) = n := by
  classical
  have hn : Nonempty ι := by simp [← Fintype.card_pos_iff, hc]
  obtain ⟨i₁⟩ := hn
  rw [affineIndependent_iff_linearIndependent_vsub _ _ i₁,
    linearIndependent_iff_card_eq_finrank_span, eq_comm,
    vectorSpan_range_eq_span_range_vsub_right_ne k p i₁, Set.finrank]
  rw [← Finset.card_univ] at hc
  rw [Fintype.subtype_card]
  simp [Finset.filter_ne', Finset.card_erase_of_mem, hc]

/-- `n + 1` points are affinely independent if and only if their
`vectorSpan` has dimension at least `n`. -/
theorem affineIndependent_iff_le_finrank_vectorSpan [Fintype ι] (p : ι → P) {n : ℕ}
    (hc : Fintype.card ι = n + 1) :
    AffineIndependent k p ↔ n ≤ finrank k (vectorSpan k (Set.range p)) := by
  rw [affineIndependent_iff_finrank_vectorSpan_eq k p hc]
  constructor
  · rintro rfl
    rfl
  · exact fun hle => le_antisymm (finrank_vectorSpan_range_le k p hc) hle

/-- `n + 2` points are affinely independent if and only if their
`vectorSpan` does not have dimension at most `n`. -/
theorem affineIndependent_iff_not_finrank_vectorSpan_le [Fintype ι] (p : ι → P) {n : ℕ}
    (hc : Fintype.card ι = n + 2) :
    AffineIndependent k p ↔ ¬finrank k (vectorSpan k (Set.range p)) ≤ n := by
  rw [affineIndependent_iff_le_finrank_vectorSpan k p hc, ← Nat.lt_iff_add_one_le, lt_iff_not_ge]

/-- `n + 2` points have a `vectorSpan` with dimension at most `n` if
and only if they are not affinely independent. -/
theorem finrank_vectorSpan_le_iff_not_affineIndependent [Fintype ι] (p : ι → P) {n : ℕ}
    (hc : Fintype.card ι = n + 2) :
    finrank k (vectorSpan k (Set.range p)) ≤ n ↔ ¬AffineIndependent k p :=
  (not_iff_comm.1 (affineIndependent_iff_not_finrank_vectorSpan_le k p hc).symm).symm

variable {k}

lemma AffineIndependent.card_le_finrank_succ [Fintype ι] {p : ι → P} (hp : AffineIndependent k p) :
    Fintype.card ι ≤ Module.finrank k (vectorSpan k (Set.range p)) + 1 := by
  cases isEmpty_or_nonempty ι
  · simp [Fintype.card_eq_zero]
  rw [← tsub_le_iff_right]
  exact (affineIndependent_iff_le_finrank_vectorSpan _ _
    (tsub_add_cancel_of_le <| Nat.one_le_iff_ne_zero.2 Fintype.card_ne_zero).symm).1 hp

open Finset in
/-- If an affine independent finset is contained in the affine span of another finset, then its
cardinality is at most the cardinality of that finset. -/
lemma AffineIndependent.card_le_card_of_subset_affineSpan {s t : Finset V}
    (hs : AffineIndependent k ((↑) : s → V)) (hst : (s : Set V) ⊆ affineSpan k (t : Set V)) :
    #s ≤ #t := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht' := t.eq_empty_or_nonempty
  · simpa [Set.subset_empty_iff] using hst
  have := hs'.to_subtype
  have := ht'.to_set.to_subtype
  have direction_le := AffineSubspace.direction_le (affineSpan_mono k hst)
  rw [AffineSubspace.affineSpan_coe, direction_affineSpan, direction_affineSpan,
    ← @Subtype.range_coe _ (s : Set V), ← @Subtype.range_coe _ (t : Set V)] at direction_le
  have finrank_le := add_le_add_right (Submodule.finrank_mono direction_le) 1
  -- We use `erw` to elide the difference between `↥s` and `↥(s : Set V)}`
  erw [hs.finrank_vectorSpan_add_one] at finrank_le
  simpa using finrank_le.trans <| finrank_vectorSpan_range_add_one_le _ _

open Finset in
/-- If the affine span of an affine independent finset is strictly contained in the affine span of
another finset, then its cardinality is strictly less than the cardinality of that finset. -/
lemma AffineIndependent.card_lt_card_of_affineSpan_lt_affineSpan {s t : Finset V}
    (hs : AffineIndependent k ((↑) : s → V))
    (hst : affineSpan k (s : Set V) < affineSpan k (t : Set V)) : #s < #t := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simpa [card_pos] using hst
  obtain rfl | ht' := t.eq_empty_or_nonempty
  · simp at hst
  have := hs'.to_subtype
  have := ht'.to_set.to_subtype
  have dir_lt := AffineSubspace.direction_lt_of_nonempty (k := k) hst <| hs'.to_set.affineSpan k
  rw [direction_affineSpan, direction_affineSpan,
    ← @Subtype.range_coe _ (s : Set V), ← @Subtype.range_coe _ (t : Set V)] at dir_lt
  have finrank_lt := add_lt_add_right (Submodule.finrank_lt_finrank_of_lt dir_lt) 1
  -- We use `erw` to elide the difference between `↥s` and `↥(s : Set V)}`
  erw [hs.finrank_vectorSpan_add_one] at finrank_lt
  simpa using finrank_lt.trans_le <| finrank_vectorSpan_range_add_one_le _ _

/-- If the `vectorSpan` of a finite subset of an affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule. -/
theorem AffineIndependent.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one
    [DecidableEq P] {p : ι → P}
    (hi : AffineIndependent k p) {s : Finset ι} {sm : Submodule k V} [FiniteDimensional k sm]
    (hle : vectorSpan k (s.image p : Set P) ≤ sm) (hc : #s = finrank k sm + 1) :
    vectorSpan k (s.image p : Set P) = sm :=
  Submodule.eq_of_le_of_finrank_eq hle <| hi.finrank_vectorSpan_image_finset hc

/-- If the `vectorSpan` of a finite affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule. -/
theorem AffineIndependent.vectorSpan_eq_of_le_of_card_eq_finrank_add_one [Fintype ι] {p : ι → P}
    (hi : AffineIndependent k p) {sm : Submodule k V} [FiniteDimensional k sm]
    (hle : vectorSpan k (Set.range p) ≤ sm) (hc : Fintype.card ι = finrank k sm + 1) :
    vectorSpan k (Set.range p) = sm :=
  Submodule.eq_of_le_of_finrank_eq hle <| hi.finrank_vectorSpan hc

/-- If the `affineSpan` of a finite subset of an affinely independent
family lies in an affine subspace whose direction has dimension one
less than its cardinality, it equals that subspace. -/
theorem AffineIndependent.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one
    [DecidableEq P] {p : ι → P}
    (hi : AffineIndependent k p) {s : Finset ι} {sp : AffineSubspace k P}
    [FiniteDimensional k sp.direction] (hle : affineSpan k (s.image p : Set P) ≤ sp)
    (hc : #s = finrank k sp.direction + 1) : affineSpan k (s.image p : Set P) = sp := by
  have hn : s.Nonempty := by
    rw [← Finset.card_pos, hc]
    apply Nat.succ_pos
  refine eq_of_direction_eq_of_nonempty_of_le ?_ ((hn.image p).to_set.affineSpan k) hle
  have hd := direction_le hle
  rw [direction_affineSpan] at hd ⊢
  exact hi.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one hd hc

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

/-- The `affineSpan` of a finite affinely independent family is `⊤` iff the
family's cardinality is one more than that of the finite-dimensional space. -/
theorem AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one [FiniteDimensional k V]
    [Fintype ι] {p : ι → P} (hi : AffineIndependent k p) :
    affineSpan k (Set.range p) = ⊤ ↔ Fintype.card ι = finrank k V + 1 := by
  constructor
  · intro h_tot
    let n := Fintype.card ι - 1
    have hn : Fintype.card ι = n + 1 :=
      (Nat.succ_pred_eq_of_pos (card_pos_of_affineSpan_eq_top k V P h_tot)).symm
    rw [hn, ← finrank_top, ← (vectorSpan_eq_top_of_affineSpan_eq_top k V P) h_tot,
      ← hi.finrank_vectorSpan hn]
  · intro hc
    rw [← finrank_top, ← direction_top k V P] at hc
    exact hi.affineSpan_eq_of_le_of_card_eq_finrank_add_one le_top hc

theorem Affine.Simplex.span_eq_top [FiniteDimensional k V] {n : ℕ} (T : Affine.Simplex k V n)
    (hrank : finrank k V = n) : affineSpan k (Set.range T.points) = ⊤ := by
  rw [AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one T.independent,
    Fintype.card_fin, hrank]

/-- The `vectorSpan` of adding a point to a finite-dimensional subspace is finite-dimensional. -/
instance finiteDimensional_vectorSpan_insert (s : AffineSubspace k P)
    [FiniteDimensional k s.direction] (p : P) :
    FiniteDimensional k (vectorSpan k (insert p (s : Set P))) := by
  rw [← direction_affineSpan, ← affineSpan_insert_affineSpan]
  rcases (s : Set P).eq_empty_or_nonempty with (hs | ⟨p₀, hp₀⟩)
  · rw [coe_eq_bot_iff] at hs
    rw [hs, bot_coe, span_empty, bot_coe, direction_affineSpan]
    convert finiteDimensional_bot k V <;> simp
  · rw [affineSpan_coe, direction_affineSpan_insert hp₀]
    infer_instance

/-- The direction of the affine span of adding a point to a finite-dimensional subspace is
finite-dimensional. -/
instance finiteDimensional_direction_affineSpan_insert (s : AffineSubspace k P)
    [FiniteDimensional k s.direction] (p : P) :
    FiniteDimensional k (affineSpan k (insert p (s : Set P))).direction :=
  (direction_affineSpan k (insert p (s : Set P))).symm ▸ finiteDimensional_vectorSpan_insert s p

variable (k)

/-- The `vectorSpan` of adding a point to a set with a finite-dimensional `vectorSpan` is
finite-dimensional. -/
instance finiteDimensional_vectorSpan_insert_set (s : Set P) [FiniteDimensional k (vectorSpan k s)]
    (p : P) : FiniteDimensional k (vectorSpan k (insert p s)) := by
  haveI : FiniteDimensional k (affineSpan k s).direction :=
    (direction_affineSpan k s).symm ▸ inferInstance
  rw [← direction_affineSpan, ← affineSpan_insert_affineSpan, direction_affineSpan]
  exact finiteDimensional_vectorSpan_insert (affineSpan k s) p

/-- The direction of the affine span of adding a point to a set with a set with finite-dimensional
direction of the `affineSpan` is finite-dimensional. -/
instance finiteDimensional_direction_affineSpan_insert_set (s : Set P)
    [FiniteDimensional k (affineSpan k s).direction] (p : P) :
    FiniteDimensional k (affineSpan k (insert p s)).direction := by
  haveI : FiniteDimensional k (vectorSpan k s) := (direction_affineSpan k s) ▸ inferInstance
  rw [direction_affineSpan]
  infer_instance

/-- A set of points is collinear if their `vectorSpan` has dimension
at most `1`. -/
def Collinear (s : Set P) : Prop :=
  Module.rank k (vectorSpan k s) ≤ 1

/-- The definition of `Collinear`. -/
theorem collinear_iff_rank_le_one (s : Set P) :
    Collinear k s ↔ Module.rank k (vectorSpan k s) ≤ 1 := Iff.rfl

variable {k}

/-- A set of points, whose `vectorSpan` is finite-dimensional, is
collinear if and only if their `vectorSpan` has dimension at most
`1`. -/
theorem collinear_iff_finrank_le_one {s : Set P} [FiniteDimensional k (vectorSpan k s)] :
    Collinear k s ↔ finrank k (vectorSpan k s) ≤ 1 := by
  have h := collinear_iff_rank_le_one k s
  rw [← finrank_eq_rank] at h
  exact mod_cast h

alias ⟨Collinear.finrank_le_one, _⟩ := collinear_iff_finrank_le_one

/-- A subset of a collinear set is collinear. -/
theorem Collinear.subset {s₁ s₂ : Set P} (hs : s₁ ⊆ s₂) (h : Collinear k s₂) : Collinear k s₁ :=
  (Submodule.rank_mono (vectorSpan_mono k hs)).trans h

/-- The `vectorSpan` of collinear points is finite-dimensional. -/
theorem Collinear.finiteDimensional_vectorSpan {s : Set P} (h : Collinear k s) :
    FiniteDimensional k (vectorSpan k s) :=
  IsNoetherian.iff_fg.1
    (IsNoetherian.iff_rank_lt_aleph0.2 (lt_of_le_of_lt h Cardinal.one_lt_aleph0))

/-- The direction of the affine span of collinear points is finite-dimensional. -/
theorem Collinear.finiteDimensional_direction_affineSpan {s : Set P} (h : Collinear k s) :
    FiniteDimensional k (affineSpan k s).direction :=
  (direction_affineSpan k s).symm ▸ h.finiteDimensional_vectorSpan

variable (k P)

/-- The empty set is collinear. -/
theorem collinear_empty : Collinear k (∅ : Set P) := by
  rw [collinear_iff_rank_le_one, vectorSpan_empty]
  simp

variable {P}

/-- A single point is collinear. -/
theorem collinear_singleton (p : P) : Collinear k ({p} : Set P) := by
  rw [collinear_iff_rank_le_one, vectorSpan_singleton]
  simp

variable {k}

/-- Given a point `p₀` in a set of points, that set is collinear if and
only if the points can all be expressed as multiples of the same
vector, added to `p₀`. -/
theorem collinear_iff_of_mem {s : Set P} {p₀ : P} (h : p₀ ∈ s) :
    Collinear k s ↔ ∃ v : V, ∀ p ∈ s, ∃ r : k, p = r • v +ᵥ p₀ := by
  simp_rw [collinear_iff_rank_le_one, rank_submodule_le_one_iff', Submodule.le_span_singleton_iff]
  constructor
  · rintro ⟨v₀, hv⟩
    use v₀
    intro p hp
    obtain ⟨r, hr⟩ := hv (p -ᵥ p₀) (vsub_mem_vectorSpan k hp h)
    use r
    rw [eq_vadd_iff_vsub_eq]
    exact hr.symm
  · rintro ⟨v, hp₀v⟩
    use v
    intro w hw
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
    rwa [Submodule.mem_span_singleton] at hw'

/-- A set of points is collinear if and only if they can all be
expressed as multiples of the same vector, added to the same base
point. -/
theorem collinear_iff_exists_forall_eq_smul_vadd (s : Set P) :
    Collinear k s ↔ ∃ (p₀ : P) (v : V), ∀ p ∈ s, ∃ r : k, p = r • v +ᵥ p₀ := by
  rcases Set.eq_empty_or_nonempty s with (rfl | ⟨⟨p₁, hp₁⟩⟩)
  · simp [collinear_empty]
  · rw [collinear_iff_of_mem hp₁]
    constructor
    · exact fun h => ⟨p₁, h⟩
    · rintro ⟨p, v, hv⟩
      use v
      intro p₂ hp₂
      rcases hv p₂ hp₂ with ⟨r, rfl⟩
      rcases hv p₁ hp₁ with ⟨r₁, rfl⟩
      use r - r₁
      simp [vadd_vadd, ← add_smul]

variable (k) in
/-- Two points are collinear. -/
theorem collinear_pair (p₁ p₂ : P) : Collinear k ({p₁, p₂} : Set P) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  use p₁, p₂ -ᵥ p₁
  intro p hp
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp | hp
  · use 0
    simp [hp]
  · use 1
    simp [hp]

/-- Three points are affinely independent if and only if they are not
collinear. -/
theorem affineIndependent_iff_not_collinear {p : Fin 3 → P} :
    AffineIndependent k p ↔ ¬Collinear k (Set.range p) := by
  rw [collinear_iff_finrank_le_one,
    affineIndependent_iff_not_finrank_vectorSpan_le k p (Fintype.card_fin 3)]

/-- Three points are collinear if and only if they are not affinely
independent. -/
theorem collinear_iff_not_affineIndependent {p : Fin 3 → P} :
    Collinear k (Set.range p) ↔ ¬AffineIndependent k p := by
  rw [collinear_iff_finrank_le_one,
    finrank_vectorSpan_le_iff_not_affineIndependent k p (Fintype.card_fin 3)]

/-- Three points are affinely independent if and only if they are not collinear. -/
theorem affineIndependent_iff_not_collinear_set {p₁ p₂ p₃ : P} :
    AffineIndependent k ![p₁, p₂, p₃] ↔ ¬Collinear k ({p₁, p₂, p₃} : Set P) := by
  rw [affineIndependent_iff_not_collinear]
  simp_rw [Matrix.range_cons, Matrix.range_empty, Set.singleton_union, insert_empty_eq]

/-- Three points are collinear if and only if they are not affinely independent. -/
theorem collinear_iff_not_affineIndependent_set {p₁ p₂ p₃ : P} :
    Collinear k ({p₁, p₂, p₃} : Set P) ↔ ¬AffineIndependent k ![p₁, p₂, p₃] :=
  affineIndependent_iff_not_collinear_set.not_left.symm

/-- Three points are affinely independent if and only if they are not collinear. -/
theorem affineIndependent_iff_not_collinear_of_ne {p : Fin 3 → P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    AffineIndependent k p ↔ ¬Collinear k ({p i₁, p i₂, p i₃} : Set P) := by
  have hu : (Finset.univ : Finset (Fin 3)) = {i₁, i₂, i₃} := by decide +revert
  rw [affineIndependent_iff_not_collinear, ← Set.image_univ, ← Finset.coe_univ, hu,
    Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_pair]

/-- Three points are collinear if and only if they are not affinely independent. -/
theorem collinear_iff_not_affineIndependent_of_ne {p : Fin 3 → P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    Collinear k ({p i₁, p i₂, p i₃} : Set P) ↔ ¬AffineIndependent k p :=
  (affineIndependent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃).not_left.symm

/-- If three points are not collinear, the first and second are different. -/
theorem ne₁₂_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P)) :
    p₁ ≠ p₂ := by
  rintro rfl
  simp [collinear_pair] at h

/-- If three points are not collinear, the first and third are different. -/
theorem ne₁₃_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P)) :
    p₁ ≠ p₃ := by
  rintro rfl
  simp [collinear_pair] at h

/-- If three points are not collinear, the second and third are different. -/
theorem ne₂₃_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P)) :
    p₂ ≠ p₃ := by
  rintro rfl
  simp [collinear_pair] at h

/-- A point in a collinear set of points lies in the affine span of any two distinct points of
that set. -/
theorem Collinear.mem_affineSpan_of_mem_of_ne {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₁p₂ : p₁ ≠ p₂) : p₃ ∈ line[k, p₁, p₂] := by
  rw [collinear_iff_of_mem hp₁] at h
  rcases h with ⟨v, h⟩
  rcases h p₂ hp₂ with ⟨r₂, rfl⟩
  rcases h p₃ hp₃ with ⟨r₃, rfl⟩
  rw [vadd_left_mem_affineSpan_pair]
  refine ⟨r₃ / r₂, ?_⟩
  have h₂ : r₂ ≠ 0 := by
    rintro rfl
    simp at hp₁p₂
  simp [smul_smul, h₂]

/-- The affine span of any two distinct points of a collinear set of points equals the affine
span of the whole set. -/
theorem Collinear.affineSpan_eq_of_ne {s : Set P} (h : Collinear k s) {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (hp₁p₂ : p₁ ≠ p₂) : line[k, p₁, p₂] = affineSpan k s :=
  le_antisymm (affineSpan_mono _ (Set.insert_subset_iff.2 ⟨hp₁, Set.singleton_subset_iff.2 hp₂⟩))
    (affineSpan_le.2 fun _ hp => h.mem_affineSpan_of_mem_of_ne hp₁ hp₂ hp hp₁p₂)

/-- Given a collinear set of points, and two distinct points `p₂` and `p₃` in it, a point `p₁` is
collinear with the set if and only if it is collinear with `p₂` and `p₃`. -/
theorem Collinear.collinear_insert_iff_of_ne {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P}
    (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₂p₃ : p₂ ≠ p₃) :
    Collinear k (insert p₁ s) ↔ Collinear k ({p₁, p₂, p₃} : Set P) := by
  have hv : vectorSpan k (insert p₁ s) = vectorSpan k ({p₁, p₂, p₃} : Set P) := by
    conv_rhs => rw [← direction_affineSpan, ← affineSpan_insert_affineSpan]
    rw [← direction_affineSpan, ← affineSpan_insert_affineSpan, h.affineSpan_eq_of_ne hp₂ hp₃ hp₂p₃]
  rw [Collinear, Collinear, hv]

/-- Adding a point in the affine span of a set does not change whether that set is collinear. -/
theorem collinear_insert_iff_of_mem_affineSpan {s : Set P} {p : P} (h : p ∈ affineSpan k s) :
    Collinear k (insert p s) ↔ Collinear k s := by
  rw [Collinear, Collinear, vectorSpan_insert_eq_vectorSpan h]

/-- If a point lies in the affine span of two points, those three points are collinear. -/
theorem collinear_insert_of_mem_affineSpan_pair {p₁ p₂ p₃ : P} (h : p₁ ∈ line[k, p₂, p₃]) :
    Collinear k ({p₁, p₂, p₃} : Set P) := by
  rw [collinear_insert_iff_of_mem_affineSpan h]
  exact collinear_pair _ _ _

/-- If two points lie in the affine span of two points, those four points are collinear. -/
theorem collinear_insert_insert_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ : P} (h₁ : p₁ ∈ line[k, p₃, p₄])
    (h₂ : p₂ ∈ line[k, p₃, p₄]) : Collinear k ({p₁, p₂, p₃, p₄} : Set P) := by
  rw [collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1 (affineSpan_mono k (Set.subset_insert _ _)) _ h₁),
    collinear_insert_iff_of_mem_affineSpan h₂]
  exact collinear_pair _ _ _

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

/-- If three points lie in the affine span of two points, the first four points are collinear. -/
theorem collinear_insert_insert_insert_left_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ p₅ : P}
    (h₁ : p₁ ∈ line[k, p₄, p₅]) (h₂ : p₂ ∈ line[k, p₄, p₅]) (h₃ : p₃ ∈ line[k, p₄, p₅]) :
    Collinear k ({p₁, p₂, p₃, p₄} : Set P) := by
  refine (collinear_insert_insert_insert_of_mem_affineSpan_pair h₁ h₂ h₃).subset ?_
  gcongr; simp

/-- If three points lie in the affine span of two points, the first three points are collinear. -/
theorem collinear_triple_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ p₅ : P} (h₁ : p₁ ∈ line[k, p₄, p₅])
    (h₂ : p₂ ∈ line[k, p₄, p₅]) (h₃ : p₃ ∈ line[k, p₄, p₅]) :
    Collinear k ({p₁, p₂, p₃} : Set P) := by
  refine (collinear_insert_insert_insert_left_of_mem_affineSpan_pair h₁ h₂ h₃).subset ?_
  gcongr; simp

variable (k) in
/-- A set of points is coplanar if their `vectorSpan` has dimension at most `2`. -/
def Coplanar (s : Set P) : Prop :=
  Module.rank k (vectorSpan k s) ≤ 2

/-- The `vectorSpan` of coplanar points is finite-dimensional. -/
theorem Coplanar.finiteDimensional_vectorSpan {s : Set P} (h : Coplanar k s) :
    FiniteDimensional k (vectorSpan k s) := by
  refine IsNoetherian.iff_fg.1 (IsNoetherian.iff_rank_lt_aleph0.2 (lt_of_le_of_lt h ?_))
  exact Cardinal.lt_aleph0.2 ⟨2, rfl⟩

/-- The direction of the affine span of coplanar points is finite-dimensional. -/
theorem Coplanar.finiteDimensional_direction_affineSpan {s : Set P} (h : Coplanar k s) :
    FiniteDimensional k (affineSpan k s).direction :=
  (direction_affineSpan k s).symm ▸ h.finiteDimensional_vectorSpan

/-- A set of points, whose `vectorSpan` is finite-dimensional, is coplanar if and only if their
`vectorSpan` has dimension at most `2`. -/
theorem coplanar_iff_finrank_le_two {s : Set P} [FiniteDimensional k (vectorSpan k s)] :
    Coplanar k s ↔ finrank k (vectorSpan k s) ≤ 2 := by
  have h : Coplanar k s ↔ Module.rank k (vectorSpan k s) ≤ 2 := Iff.rfl
  rw [← finrank_eq_rank] at h
  exact mod_cast h

alias ⟨Coplanar.finrank_le_two, _⟩ := coplanar_iff_finrank_le_two

/-- A subset of a coplanar set is coplanar. -/
theorem Coplanar.subset {s₁ s₂ : Set P} (hs : s₁ ⊆ s₂) (h : Coplanar k s₂) : Coplanar k s₁ :=
  (Submodule.rank_mono (vectorSpan_mono k hs)).trans h

/-- Collinear points are coplanar. -/
theorem Collinear.coplanar {s : Set P} (h : Collinear k s) : Coplanar k s :=
  le_trans h one_le_two

variable (k) (P)

/-- The empty set is coplanar. -/
theorem coplanar_empty : Coplanar k (∅ : Set P) :=
  (collinear_empty k P).coplanar

variable {P}

/-- A single point is coplanar. -/
theorem coplanar_singleton (p : P) : Coplanar k ({p} : Set P) :=
  (collinear_singleton k p).coplanar

/-- Two points are coplanar. -/
theorem coplanar_pair (p₁ p₂ : P) : Coplanar k ({p₁, p₂} : Set P) :=
  (collinear_pair k p₁ p₂).coplanar

variable {k}

/-- Adding a point in the affine span of a set does not change whether that set is coplanar. -/
theorem coplanar_insert_iff_of_mem_affineSpan {s : Set P} {p : P} (h : p ∈ affineSpan k s) :
    Coplanar k (insert p s) ↔ Coplanar k s := by
  rw [Coplanar, Coplanar, vectorSpan_insert_eq_vectorSpan h]

end AffineSpace'

/-!
## Affine dimension and affine equivalences

This section develops the theory of affine dimension and proves that affinely independent
families of the same size can be mapped to each other by affine automorphisms.
-/

section AffineIndependenceAutomorphisms

variable (k : Type*) {V : Type*} {P : Type*}
variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- The affine dimension of a set in an affine space is the finite rank of the direction
of its affine span. -/
noncomputable def affineDim (s : Set P) : ℕ :=
  Module.finrank k (affineSpan k s).direction

/-- If the affine span of a set equals the whole space, then its affine dimension equals
the dimension of the ambient vector space. This version doesn't require proving the set
is nonempty, since that follows from the spanning condition when the space is nonempty. -/
lemma affineDim_eq_finrank_of_affineSpan_eq_top
    {k : Type*} {V : Type*} {P : Type*}
    [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P] [_inst : FiniteDimensional k V]
    [Nonempty P]
    {s : Set P} (h : affineSpan k s = ⊤) :
    affineDim k s = Module.finrank k V :=
  calc affineDim k s
      = Module.finrank k (affineSpan k s).direction := rfl
    _ = Module.finrank k (⊤ : AffineSubspace k P).direction := by rw [h]
    _ = Module.finrank k (⊤ : Submodule k V) := by rw [AffineSubspace.direction_top]
    _ = Module.finrank k V := finrank_top k V

/-- The affine span of a nonempty set equals the whole space if and only if its affine
dimension equals the dimension of the ambient vector space. -/
lemma affineSpan_eq_top_iff_affineDim_eq_finrank
    {k : Type*} {V : Type*} {P : Type*}
    [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P] [FiniteDimensional k V]
    {s : Set P} (hs : s.Nonempty) :
    affineSpan k s = ⊤ ↔ affineDim k s = Module.finrank k V := by
  haveI : Nonempty P := hs.to_type
  have h_span_nonempty : (affineSpan k s : Set P).Nonempty :=
    hs.mono (subset_affineSpan k s)
  constructor
  · intro h_top
    exact affineDim_eq_finrank_of_affineSpan_eq_top h_top
  · intro h_dim
    have h_dir_eq : (affineSpan k s).direction = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [← h_dim]
      rfl
    exact (AffineSubspace.direction_eq_top_iff_of_nonempty h_span_nonempty).mp h_dir_eq

/-- Affine dimension is monotone: if `s ⊆ affineSpan k t`, then
`affineDim k s ≤ affineDim k t`. -/
theorem affineDim_le_of_subset_affineSpan
    {k : Type*} {V : Type*} {P : Type*}
    [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P] [FiniteDimensional k V]
    {s t : Set P} (h : s ⊆ affineSpan k t) :
    affineDim k s ≤ affineDim k t := by
  calc affineDim k s
      = Module.finrank k (affineSpan k s).direction := rfl
    _ ≤ Module.finrank k (affineSpan k t).direction :=
        Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_le_of_subset_coe h))
    _ = affineDim k t := rfl

/-- For an affinely independent family spanning the whole space, removing any base point
leaves exactly `finrank` points.

This follows from the fact that affinely independent spanning families have `finrank + 1`
elements. -/
lemma AffineIndependent.card_subtype_ne_eq_finrank_of_span_eq_top
    {k : Type*} {V : Type*} {P : Type*}
    [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P] [FiniteDimensional k V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → P}
    (hf : AffineIndependent k f)
    (hf_span : affineSpan k (Set.range f) = ⊤)
    (i₀ : ι) :
    Fintype.card {i // i ≠ i₀} = Module.finrank k V := by
  calc Fintype.card {i // i ≠ i₀}
      = Fintype.card ι - 1 := Set.card_ne_eq i₀
    _ = (Module.finrank k V + 1) - 1 := by
          rw [hf.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp hf_span]
    _ = Module.finrank k V := by omega

/-- Two affinely independent families with the same index type that both span the entire
space can be mapped to each other by an affine automorphism.

This result is closely related to the TODO in `Mathlib.LinearAlgebra.AffineSpace.Basis` about
constructing affine equivalences to barycentric coordinate spaces. Once that equivalence is
fully constructed, this theorem could be reproven as a simple composition through the
barycentric coordinate space. -/
theorem AffineIndependent.exists_affineEquiv_of_span_eq_top
    {k : Type*} {V : Type*} {P : Type*}
    [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → P)
    (hf : AffineIndependent k f)
    (hg : AffineIndependent k g)
    (hf_span : affineSpan k (Set.range f) = ⊤)
    (hg_span : affineSpan k (Set.range g) = ⊤) :
    ∃ (T : P ≃ᵃ[k] P), T ∘ f = g := by
  obtain ⟨i₀⟩ := Nonempty.of_affineSpan_range_eq_top f hf_span

  let b_f : AffineBasis ι k P := ⟨f, hf, hf_span⟩
  let b_g : AffineBasis ι k P := ⟨g, hg, hg_span⟩

  use AffineEquiv.ofLinearEquiv
    ((b_f.basisOf i₀).equiv (b_g.basisOf i₀) (Equiv.refl _)) (f i₀) (g i₀)

  ext i
  by_cases hi : i = i₀
  · simp [hi]
  · simp only [AffineEquiv.ofLinearEquiv_apply, Function.comp_apply]
    have hf_basis : f i -ᵥ f i₀ = b_f.basisOf i₀ ⟨i, hi⟩ :=
      (AffineBasis.basisOf_apply b_f i₀ ⟨i, hi⟩).symm
    have hg_basis : g i -ᵥ g i₀ = b_g.basisOf i₀ ⟨i, hi⟩ :=
      (AffineBasis.basisOf_apply b_g i₀ ⟨i, hi⟩).symm
    rw [hf_basis, Module.Basis.equiv_apply, Equiv.refl_apply, hg_basis.symm, vsub_vadd]

/-- An affinely independent family in a finite-dimensional space has cardinality at most
`finrank + 1`. -/
lemma AffineIndependent.card_le_finrank_add_one
    {k : Type*} {V : Type*} {P : Type*}
    [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P] [FiniteDimensional k V]
    {ι : Type*} [Fintype ι] {f : ι → P} (hf : AffineIndependent k f) :
    Fintype.card ι ≤ Module.finrank k V + 1 := by
  calc Fintype.card ι
      ≤ Module.finrank k (vectorSpan k (Set.range f)) + 1 := hf.card_le_finrank_succ
    _ ≤ Module.finrank k V + 1 := by
        apply Nat.add_le_add_right
        exact Submodule.finrank_le _

/-- If an affinely independent family has cardinality strictly less than `finrank + 1`,
then its affine span is a proper subspace. -/
lemma AffineIndependent.affineSpan_ne_top_of_card_lt_finrank_add_one
    {k : Type*} {V : Type*} {P : Type*}
    [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P] [FiniteDimensional k V]
    {ι : Type*} [Fintype ι] {f : ι → P}
    (hf : AffineIndependent k f)
    (h_card : Fintype.card ι < Module.finrank k V + 1) :
    affineSpan k (Set.range f) ≠ ⊤ := by
  intro h_top
  have h_card_eq := hf.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp h_top
  omega

/-- Two affinely independent families spanning affine subspaces with
equal affine dimension have the same cardinality. -/
lemma affineIndependent_card_eq_of_affineDim_eq
    {k : Type*} {V : Type*} {P : Type*}
    [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Nonempty ι₁] [Nonempty ι₂]
    {f₁ : ι₁ → P} {f₂ : ι₂ → P}
    {M₁ M₂ : AffineSubspace k P}
    (hf₁_span : affineSpan k (Set.range f₁) = M₁)
    (hf₂_span : affineSpan k (Set.range f₂) = M₂)
    (hf₁_indep : AffineIndependent k f₁)
    (hf₂_indep : AffineIndependent k f₂)
    (h_dim : affineDim k (M₁ : Set P) = affineDim k (M₂ : Set P)) :
    Fintype.card ι₁ = Fintype.card ι₂ := by
  have h₁ := hf₁_indep.finrank_vectorSpan_add_one
  have h₂ := hf₂_indep.finrank_vectorSpan_add_one
  have : vectorSpan k (Set.range f₁) = M₁.direction := by
    rw [← direction_affineSpan, hf₁_span]
  rw [this] at h₁
  have : vectorSpan k (Set.range f₂) = M₂.direction := by
    rw [← direction_affineSpan, hf₂_span]
  rw [this] at h₂
  have h_finrank_eq : Module.finrank k M₁.direction = Module.finrank k M₂.direction := by
    unfold affineDim at h_dim
    rwa [AffineSubspace.affineSpan_coe, AffineSubspace.affineSpan_coe] at h_dim
  omega

/-- Affinely independent families of the same size can be mapped to each other by an affine
automorphism.

This corresponds to Rockafellar's "Convex Analysis" (1970), Theorem 1.6.

Given two affinely independent families `f, g : ι → P` with the same finite index type,
there exists an affine automorphism `T : P ≃ᵃ[k] P` such that `T (f i) = g i` for all `i`. -/
theorem AffineIndependent.exists_affineEquiv
    {k : Type*} {V : Type*} {P : Type*}
    [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P] [FiniteDimensional k V]
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (f g : ι → P)
    (hf : AffineIndependent k f)
    (hg : AffineIndependent k g) :
    ∃ (T : P ≃ᵃ[k] P), T ∘ f = g := by
  have h_card_bound : Fintype.card ι ≤ Module.finrank k V + 1 := hf.card_le_finrank_add_one
  induction h : Module.finrank k V + 1 - Fintype.card ι generalizing ι f g with
  | zero =>
    have h_lower : Module.finrank k V + 1 ≤ Fintype.card ι := by
      exact Nat.sub_eq_zero_iff_le.mp h
    by_cases h_empty : IsEmpty ι
    · use AffineEquiv.refl k P
      ext i
      exact IsEmpty.elim h_empty i
    · rw [not_isEmpty_iff] at h_empty
      have h_card_eq : Fintype.card ι = Module.finrank k V + 1 := by omega
      have h_span_f : affineSpan k (Set.range f) = ⊤ := by
        exact hf.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr h_card_eq
      have h_span_g : affineSpan k (Set.range g) = ⊤ := by
        exact hg.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr h_card_eq
      exact AffineIndependent.exists_affineEquiv_of_span_eq_top f g hf hg h_span_f h_span_g

  | succ n ih =>
    by_cases h_empty : IsEmpty ι
    · use AffineEquiv.refl k P
      ext i
      exact IsEmpty.elim h_empty i
    · rw [not_isEmpty_iff] at h_empty
      have h_card_lt : Fintype.card ι < Module.finrank k V + 1 := by omega
      obtain ⟨p_f, hp_f⟩ := AffineSubspace.exists_not_mem_of_ne_top _
        (hf.affineSpan_ne_top_of_card_lt_finrank_add_one h_card_lt)
      obtain ⟨p_g, hp_g⟩ := AffineSubspace.exists_not_mem_of_ne_top _
        (hg.affineSpan_ne_top_of_card_lt_finrank_add_one h_card_lt)
      let f' : Option ι → P := fun o => o.elim p_f f
      let g' : Option ι → P := fun o => o.elim p_g g
      have hf' : AffineIndependent k f' := hf.option_extend hp_f
      have hg' : AffineIndependent k g' := hg.option_extend hp_g
      obtain ⟨T, hT⟩ := @ih (Option ι) _ _ f' g' hf' hg'
        (by simp only [Fintype.card_option]; omega)
        (by simp only [Fintype.card_option]; omega)
      use T
      ext i
      exact congrFun hT (some i)

/-!
### Affine subspaces of equal dimension
-/

/-- Every affine subspace contains a finite affinely independent spanning set.

Given an affine subspace M, we can find a finite set within M that affinely spans M
and is affinely independent. -/
lemma exists_affineIndependent_of_affineSubspace
    {k : Type*} {V : Type*}
    [DivisionRing k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (M : AffineSubspace k V) :
    ∃ (s : Set V),
      s.Finite ∧
      s ⊆ M ∧
      affineSpan k s = M ∧
      AffineIndependent k (Subtype.val : s → V) := by
  -- Apply exists_affineIndependent to the underlying set of M
  obtain ⟨t, ht_sub, ht_span, ht_indep⟩ := exists_affineIndependent k V (M : Set V)

  -- t is finite because it's affinely independent in a finite-dimensional space
  have ht_finite : t.Finite := finite_set_of_fin_dim_affineIndependent k ht_indep

  exact ⟨t, ht_finite, ht_sub, by rwa [AffineSubspace.affineSpan_coe] at ht_span, ht_indep⟩

/-- Affine subspaces of the same dimension can be mapped to each other by an affine
automorphism of the ambient space.

This corresponds to Rockafellar's "Convex Analysis" (1970), Corollary 1.6.1.

An m-dimensional affine set can be expressed as the affine hull of an affinely independent
set of m+1 points. Since affine hulls are preserved by affine transformations, applying
the main theorem gives the result. -/
theorem AffineSubspace.exists_affineEquiv_of_affineDim_eq
    {k : Type*} {V : Type*}
    [DivisionRing k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (M₁ M₂ : AffineSubspace k V)
    (h_nonempty₁ : (M₁ : Set V).Nonempty)
    (h_nonempty₂ : (M₂ : Set V).Nonempty)
    (h_dim : affineDim k (M₁ : Set V) = affineDim k (M₂ : Set V)) :
    ∃ T : V ≃ᵃ[k] V, M₁.map T = M₂ := by
  classical
  obtain ⟨s₁, hs₁_finite, hs₁_sub, hs₁_span, hs₁_indep⟩ :=
    exists_affineIndependent_of_affineSubspace M₁

  obtain ⟨s₂, hs₂_finite, hs₂_sub, hs₂_span, hs₂_indep⟩ :=
    exists_affineIndependent_of_affineSubspace M₂

  haveI : Fintype s₁ := hs₁_finite.fintype
  haveI : Fintype s₂ := hs₂_finite.fintype

  let f₁ : s₁ → V := Subtype.val
  let f₂ : s₂ → V := Subtype.val

  have hf₁_span : affineSpan k (Set.range f₁) = M₁ := by
    rw [Subtype.range_coe]; exact hs₁_span
  have hf₂_span : affineSpan k (Set.range f₂) = M₂ := by
    rw [Subtype.range_coe]; exact hs₂_span

  haveI : Nonempty s₁ := Nonempty.of_affineSpan_range f₁ M₁ hf₁_span h_nonempty₁
  haveI : Nonempty s₂ := Nonempty.of_affineSpan_range f₂ M₂ hf₂_span h_nonempty₂

  have h_card_eq : Fintype.card s₁ = Fintype.card s₂ :=
    affineIndependent_card_eq_of_affineDim_eq
      hf₁_span hf₂_span hs₁_indep hs₂_indep h_dim

  let e : s₁ ≃ s₂ := Fintype.equivOfCardEq h_card_eq
  let g : s₁ → V := f₂ ∘ e

  have hg_indep : AffineIndependent k g :=
    hs₂_indep.comp_embedding e.toEmbedding

  have h_range_e : Set.range (⇑e) = Set.univ := e.surjective.range_eq
  have h_range_g : Set.range g = Set.range f₂ := by
    unfold g
    rw [Set.range_comp, h_range_e, Set.image_univ]
  have hg_span : affineSpan k (Set.range g) = M₂ := by
    rw [h_range_g, hf₂_span]

  obtain ⟨T, hT⟩ := AffineIndependent.exists_affineEquiv s₁ f₁ g hs₁_indep hg_indep

  use T
  calc M₁.map T
      = (affineSpan k (Set.range f₁)).map T := by
          rw [← hf₁_span]
    _ = affineSpan k (T '' Set.range f₁) := by
          exact AffineSubspace.map_span T.toAffineMap (Set.range f₁)
    _ = affineSpan k (Set.range g) := by
          congr 1
          ext x
          simp only [Set.mem_image, Set.mem_range]
          constructor
          · intro ⟨y, ⟨i, hy⟩, hTy⟩
            use i
            rw [← hTy, ← hy]
            show g i = T (f₁ i)
            have := congrFun hT i
            simp only [Function.comp_apply] at this
            exact this.symm
          · intro ⟨i, hx⟩
            use f₁ i, ⟨i, rfl⟩
            rw [← hx]
            show T (f₁ i) = g i
            have := congrFun hT i
            simp only [Function.comp_apply] at this
            exact this
    _ = M₂ := by
          rw [hg_span]

end AffineIndependenceAutomorphisms

section DivisionRing

variable {k : Type*} {V : Type*} {P : Type*}

open AffineSubspace Module Module

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- Adding a point to a finite-dimensional subspace increases the dimension by at most one. -/
theorem finrank_vectorSpan_insert_le (s : AffineSubspace k P) (p : P) :
    finrank k (vectorSpan k (insert p (s : Set P))) ≤ finrank k s.direction + 1 := by
  by_cases hf : FiniteDimensional k s.direction; swap
  · have hf' : ¬FiniteDimensional k (vectorSpan k (insert p (s : Set P))) := by
      intro h
      have h' : s.direction ≤ vectorSpan k (insert p (s : Set P)) := by
        conv_lhs => rw [← affineSpan_coe s, direction_affineSpan]
        exact vectorSpan_mono k (Set.subset_insert _ _)
      exact hf (Submodule.finiteDimensional_of_le h')
    rw [finrank_of_infinite_dimensional hf, finrank_of_infinite_dimensional hf', zero_add]
    exact zero_le_one
  rw [← direction_affineSpan, ← affineSpan_insert_affineSpan]
  rcases (s : Set P).eq_empty_or_nonempty with (hs | ⟨p₀, hp₀⟩)
  · rw [coe_eq_bot_iff] at hs
    rw [hs, bot_coe, span_empty, bot_coe, direction_affineSpan, direction_bot, finrank_bot,
      zero_add]
    convert zero_le_one' ℕ
    rw [← finrank_bot k V]
    convert rfl <;> simp
  · rw [affineSpan_coe, direction_affineSpan_insert hp₀, add_comm]
    refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (add_le_add_right ?_ _)
    refine finrank_le_one ⟨p -ᵥ p₀, Submodule.mem_span_singleton_self _⟩ fun v => ?_
    have h := v.property
    rw [Submodule.mem_span_singleton] at h
    rcases h with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    ext
    exact hc

variable (k) in
/-- Adding a point to a set with a finite-dimensional span increases the dimension by at most
one. -/
theorem finrank_vectorSpan_insert_le_set (s : Set P) (p : P) :
    finrank k (vectorSpan k (insert p s)) ≤ finrank k (vectorSpan k s) + 1 := by
  rw [← direction_affineSpan, ← affineSpan_insert_affineSpan, direction_affineSpan,
    ← direction_affineSpan _ s]
  exact finrank_vectorSpan_insert_le ..

/-- Adding a point to a collinear set produces a coplanar set. -/
theorem Collinear.coplanar_insert {s : Set P} (h : Collinear k s) (p : P) :
    Coplanar k (insert p s) := by
  have : FiniteDimensional k { x // x ∈ vectorSpan k s } := h.finiteDimensional_vectorSpan
  grw [coplanar_iff_finrank_le_two, finrank_vectorSpan_insert_le_set, h.finrank_le_one]

/-- A set of points in a two-dimensional space is coplanar. -/
theorem coplanar_of_finrank_eq_two (s : Set P) (h : finrank k V = 2) : Coplanar k s := by
  have : FiniteDimensional k V := .of_finrank_eq_succ h
  rw [coplanar_iff_finrank_le_two, ← h]
  exact Submodule.finrank_le _

/-- A set of points in a two-dimensional space is coplanar. -/
theorem coplanar_of_fact_finrank_eq_two (s : Set P) [h : Fact (finrank k V = 2)] : Coplanar k s :=
  coplanar_of_finrank_eq_two s h.out

variable (k)

/-- Three points are coplanar. -/
theorem coplanar_triple (p₁ p₂ p₃ : P) : Coplanar k ({p₁, p₂, p₃} : Set P) :=
  (collinear_pair k p₂ p₃).coplanar_insert p₁

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

protected theorem finite [FiniteDimensional k V] (b : AffineBasis ι k P) : Finite ι :=
  finite_of_fin_dim_affineIndependent k b.ind

protected theorem finite_set [FiniteDimensional k V] {s : Set ι} (b : AffineBasis s k P) :
    s.Finite :=
  finite_set_of_fin_dim_affineIndependent k b.ind

theorem card_eq_finrank_add_one [Fintype ι] (b : AffineBasis ι k P) :
    Fintype.card ι = Module.finrank k V + 1 :=
  have : FiniteDimensional k V := b.finiteDimensional
  b.ind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp b.tot

theorem exists_affineBasis_of_finiteDimensional [Fintype ι] [FiniteDimensional k V]
    (h : Fintype.card ι = Module.finrank k V + 1) : Nonempty (AffineBasis ι k P) := by
  obtain ⟨s, b, hb⟩ := AffineBasis.exists_affineBasis k V P
  lift s to Finset P using b.finite_set
  refine ⟨b.reindex <| Fintype.equivOfCardEq ?_⟩
  rw [h, ← b.card_eq_finrank_add_one]

end DivisionRing

end AffineBasis
