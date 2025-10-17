/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Combinatorics.Matroid.Rank.Finite
import Mathlib.Combinatorics.Matroid.Loop
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic.TautoSet

/-!
# `ℕ∞`-valued rank

If the 'cardinality' of `s : Set α` is taken to mean the `ℕ∞`-valued term `Set.encard s`,
then all bases of any `M : Matroid α` have the same cardinality,
and for each `X : Set α` with `X ⊆ M.E`, all `M`-bases for `X` have the same cardinality.
The 'rank' of a matroid is the cardinality of all its bases,
and the 'rank' of a set `X` in a matroid `M` is the cardinality of each `M`-basis of `X`.
This file defines these two concepts as a term `Matroid.eRank M : ℕ∞`
and a function `Matroid.eRk M : Set α → ℕ∞` respectively.

The rank function `Matroid.eRk` satisfies three properties, often known as (R1), (R2), (R3):
* `M.eRk X ≤ Set.encard X`,
* `M.eRk X ≤ M.eRk Y` for all `X ⊆ Y`,
* `M.eRk X + M.eRk Y ≥ M.eRk (X ∪ Y) + M.eRk (X ∩ Y)` for all `X, Y`.

In fact, if `α` is finite, then any function `Set α → ℕ∞` satisfying these properties
is the rank function of a `Matroid α`; in other words, properties (R1) - (R3) give an alternative
definition of finite matroids, and a finite matroid is determined by its rank function.
Because of this, and the convenient quantitative language of these axioms,
the rank function is often the preferred perspective on matroids in the literature.
(The above doesn't work as well for infinite matroids,
which is why mathlib defines matroids using bases/independence. )

# Main Declarations

* `Matroid.eRank M` is the `ℕ∞`-valued cardinality of each base of `M`.
* `Matroid.eRk M X` is the `ℕ∞`-valued cardinality of each `M`-basis of `X`.
* `Matroid.eRk_inter_add_eRk_union_le` : the function `M.eRk` is submodular.
* `Matroid.dual_eRk_add_eRank` : a subtraction-free formula for the dual rank of a set.

# Notes

It is natural to ask if equicardinality of bases holds if 'cardinality' refers to
a term in `Cardinal` instead of `ℕ∞`, but the answer is that it doesn't.
The cardinal-valued rank functions `Matroid.cRank` and `Matroid.cRk` are defined in
`Mathlib/Data/Matroid/Rank/Cardinal.lean`, but have less desirable properties in general.
See the module docstring of that file for a discussion.

# Implementation Details

It would be equivalent to define `Matroid.eRank (M : Matroid α) := (Matroid.cRank M).toENat`
and similar for `Matroid.eRk`, and some of the API for `cRank`/`cRk` would carry over
in a way that shortens certain proofs in this file (though not substantially).
Although this file transitively imports `Cardinal` via `Set.encard`,
there are plans to refactor the latter to be independent of the former,
which would carry over to the current version of this file.
-/

open Set ENat

namespace Matroid

variable {α : Type*} {M : Matroid α} {I B X Y : Set α} {n : ℕ∞} {e f : α}

section Basic

/-- The rank `Matroid.eRank M` of `M` is the `ℕ∞`-valued cardinality of each base of `M`.
(See `Matroid.cRank` for a worse-behaved cardinal-valued version) -/
noncomputable def eRank (M : Matroid α) : ℕ∞ := ⨆ B : {B // M.IsBase B}, B.1.encard

/-- The rank `Matroid.eRk M X` of a set `X` is the `ℕ∞`-valued cardinality of each basis of `X`.
(See `Matroid.cRk` for a worse-behaved cardinal-valued version) -/
noncomputable def eRk (M : Matroid α) (X : Set α) : ℕ∞ := (M ↾ X).eRank

lemma eRank_def (M : Matroid α) : M.eRank = M.eRk M.E := by
  rw [eRk, restrict_ground_eq_self]

@[simp]
lemma eRk_ground (M : Matroid α) : M.eRk M.E = M.eRank :=
  M.eRank_def.symm

@[simp]
lemma eRank_restrict (M : Matroid α) (X : Set α) : (M ↾ X).eRank = M.eRk X := rfl

lemma IsBase.encard_eq_eRank (hB : M.IsBase B) : B.encard = M.eRank := by
  simp [eRank, show ∀ B' : {B // M.IsBase B}, B'.1.encard = B.encard from
    fun B' ↦ B'.2.encard_eq_encard_of_isBase hB]

lemma IsBasis'.encard_eq_eRk (hI : M.IsBasis' I X) : I.encard = M.eRk X :=
  hI.isBase_restrict.encard_eq_eRank

lemma IsBasis.encard_eq_eRk (hI : M.IsBasis I X) : I.encard = M.eRk X :=
  hI.isBasis'.encard_eq_eRk

lemma eq_eRk_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.eRk X = n ↔ ∃ I, M.IsBasis I X ∧ I.encard = n :=
  ⟨fun h ↦ (M.exists_isBasis X).elim (fun I hI ↦ ⟨I, hI, by rw [hI.encard_eq_eRk, ← h]⟩),
    fun ⟨I, hI, hIc⟩ ↦ by rw [← hI.encard_eq_eRk, hIc]⟩

lemma Indep.eRk_eq_encard (hI : M.Indep I) : M.eRk I = I.encard :=
  (eq_eRk_iff hI.subset_ground).mpr ⟨I, hI.isBasis_self, rfl⟩

lemma IsBasis'.eRk_eq_eRk (hIX : M.IsBasis' I X) : M.eRk I = M.eRk X := by
  rw [← hIX.encard_eq_eRk, hIX.indep.eRk_eq_encard]

lemma IsBasis.eRk_eq_eRk (hIX : M.IsBasis I X) : M.eRk I = M.eRk X := by
  rw [← hIX.encard_eq_eRk, hIX.indep.eRk_eq_encard]

lemma IsBasis'.eRk_eq_encard (hIX : M.IsBasis' I X) : M.eRk X = I.encard := by
  rw [← hIX.eRk_eq_eRk, hIX.indep.eRk_eq_encard]

lemma IsBasis.eRk_eq_encard (hIX : M.IsBasis I X) : M.eRk X = I.encard := by
  rw [← hIX.eRk_eq_eRk, hIX.indep.eRk_eq_encard]

lemma IsBase.eRk_eq_eRank (hB : M.IsBase B) : M.eRk B = M.eRank := by
  rw [hB.indep.eRk_eq_encard, eRank_def, hB.isBasis_ground.encard_eq_eRk]

@[simp]
lemma eRk_inter_ground (M : Matroid α) (X : Set α) : M.eRk (X ∩ M.E) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.eRk_eq_eRk, hI.isBasis_inter_ground.eRk_eq_eRk]

@[simp]
lemma eRk_ground_inter (M : Matroid α) (X : Set α) : M.eRk (M.E ∩ X) = M.eRk X := by
  rw [inter_comm, eRk_inter_ground]

@[simp]
lemma eRk_union_ground (M : Matroid α) (X : Set α) : M.eRk (X ∪ M.E) = M.eRank := by
  rw [← eRk_inter_ground, inter_eq_self_of_subset_right subset_union_right, eRank_def]

@[simp]
lemma eRk_ground_union (M : Matroid α) (X : Set α) : M.eRk (M.E ∪ X) = M.eRank := by
  rw [union_comm, eRk_union_ground]

lemma eRk_insert_of_notMem_ground (X : Set α) (he : e ∉ M.E) : M.eRk (insert e X) = M.eRk X := by
  rw [← eRk_inter_ground, insert_inter_of_notMem he, eRk_inter_ground]

@[deprecated (since := "2025-05-23")]
alias eRk_insert_of_not_mem_ground := eRk_insert_of_notMem_ground

lemma eRk_eq_eRank (hX : M.E ⊆ X) : M.eRk X = M.eRank := by
  rw [← eRk_inter_ground, inter_eq_self_of_subset_right hX, eRank_def]

lemma eRk_compl_union_of_disjoint (M : Matroid α) (hXY : Disjoint X Y) :
    M.eRk (M.E \ X ∪ Y) = M.eRk (M.E \ X) := by
  rw [← eRk_inter_ground, union_inter_distrib_right, inter_eq_self_of_subset_left diff_subset,
    union_eq_self_of_subset_right
      (subset_diff.2 ⟨inter_subset_right, hXY.symm.mono_left inter_subset_left⟩)]

lemma one_le_eRank (M : Matroid α) [RankPos M] : 1 ≤ M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, one_le_encard_iff_nonempty]
  exact hB.nonempty

@[simp]
lemma eRk_univ_eq (M : Matroid α) : M.eRk univ = M.eRank := by
  rw [← eRk_inter_ground, univ_inter, eRank_def]

@[simp]
lemma eRk_empty (M : Matroid α) : M.eRk ∅ = 0 := by
  rw [← M.empty_indep.isBasis_self.encard_eq_eRk, encard_empty]

@[simp]
lemma eRk_closure_eq (M : Matroid α) (X : Set α) : M.eRk (M.closure X) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.closure_eq_closure, ← hI.indep.isBasis_closure.encard_eq_eRk, hI.encard_eq_eRk]

@[simp]
lemma eRk_union_closure_right_eq (M : Matroid α) (X Y : Set α) :
    M.eRk (X ∪ M.closure Y) = M.eRk (X ∪ Y) := by
  rw [← eRk_closure_eq, closure_union_closure_right_eq, eRk_closure_eq]

@[simp]
lemma eRk_union_closure_left_eq (M : Matroid α) (X Y : Set α) :
    M.eRk (M.closure X ∪ Y) = M.eRk (X ∪ Y) := by
  rw [← eRk_closure_eq, closure_union_closure_left_eq, eRk_closure_eq]

@[simp]
lemma eRk_insert_closure_eq (M : Matroid α) (e : α) (X : Set α) :
    M.eRk (insert e (M.closure X)) = M.eRk (insert e X) := by
  rw [← union_singleton, eRk_union_closure_left_eq, union_singleton]

/-- A version of `Matroid.restrict_eRk_eq` with no `X ⊆ R` hypothesis and thus a less simple RHS. -/
@[simp]
lemma restrict_eRk_eq' (M : Matroid α) (R X : Set α) : (M ↾ R).eRk X = M.eRk (X ∩ R) := by
  obtain ⟨I, hI⟩ := (M ↾ R).exists_isBasis' X
  rw [hI.eRk_eq_encard]
  rw [isBasis'_iff_isBasis_inter_ground, isBasis_restrict_iff', restrict_ground_eq] at hI
  rw [← eRk_inter_ground, ← hI.1.eRk_eq_encard]

lemma restrict_eRk_eq (M : Matroid α) {R : Set α} (h : X ⊆ R) : (M ↾ R).eRk X = M.eRk X := by
  rw [restrict_eRk_eq', inter_eq_self_of_subset_left h]

lemma IsBasis'.eRk_eq_eRk_union (hIX : M.IsBasis' I X) (Y : Set α) :
    M.eRk (I ∪ Y) = M.eRk (X ∪ Y) := by
  rw [← eRk_union_closure_left_eq, hIX.closure_eq_closure, eRk_union_closure_left_eq]

lemma IsBasis'.eRk_eq_eRk_insert (hIX : M.IsBasis' I X) (e : α) :
    M.eRk (insert e I) = M.eRk (insert e X) := by
  rw [← union_singleton, hIX.eRk_eq_eRk_union, union_singleton]

lemma IsBasis.eRk_eq_eRk_union (hIX : M.IsBasis I X) (Y : Set α) : M.eRk (I ∪ Y) = M.eRk (X ∪ Y) :=
  hIX.isBasis'.eRk_eq_eRk_union Y

lemma IsBasis.eRk_eq_eRk_insert (hIX : M.IsBasis I X) (e : α) :
    M.eRk (insert e I) = M.eRk (insert e X) := by
  rw [← union_singleton, hIX.eRk_eq_eRk_union, union_singleton]

lemma eRk_le_encard (M : Matroid α) (X : Set α) : M.eRk X ≤ X.encard := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eRk_eq_encard]
  exact encard_mono hI.subset

lemma eRank_le_encard_ground (M : Matroid α) : M.eRank ≤ M.E.encard :=
  M.eRank_def.trans_le <| M.eRk_le_encard M.E

lemma eRk_mono (M : Matroid α) : Monotone M.eRk := by
  rintro X Y (hXY : X ⊆ Y)
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans hXY)
  rw [hI.eRk_eq_encard, hJ.eRk_eq_encard]
  exact encard_mono hIJ

lemma eRk_le_eRank (M : Matroid α) (X : Set α) : M.eRk X ≤ M.eRank := by
  rw [eRank_def, ← eRk_inter_ground]; exact M.eRk_mono inter_subset_right

lemma eRk_eq_eRk_of_subset_of_le (hXY : X ⊆ Y) (hYX : M.eRk Y ≤ M.eRk X) : M.eRk X = M.eRk Y :=
  (M.eRk_mono hXY).antisymm hYX

lemma le_eRk_iff : n ≤ M.eRk X ↔ ∃ I, I ⊆ X ∧ M.Indep I ∧ I.encard = n := by
  refine ⟨fun h ↦ ?_, fun ⟨I, hIX, hI, hIc⟩ ↦ ?_⟩
  · obtain ⟨J, hJ⟩ := M.exists_isBasis' X
    rw [← hJ.encard_eq_eRk] at h
    obtain ⟨I, hIJ, rfl⟩ :=  exists_subset_encard_eq h
    exact ⟨_, hIJ.trans hJ.subset, hJ.indep.subset hIJ, rfl⟩
  rw [← hIc, ← hI.eRk_eq_encard]
  exact M.eRk_mono hIX

lemma eRk_le_iff : M.eRk X ≤ n ↔ ∀ ⦃I⦄, I ⊆ X → M.Indep I → I.encard ≤ n := by
  refine ⟨fun h I hIX hI ↦ (hI.eRk_eq_encard.symm.trans_le ((M.eRk_mono hIX).trans h)), fun h ↦ ?_⟩
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.encard_eq_eRk]
  exact h hI.subset hI.indep

lemma Indep.encard_le_eRk_of_subset (hI : M.Indep I) (hIX : I ⊆ X) : I.encard ≤ M.eRk X :=
  hI.eRk_eq_encard ▸ M.eRk_mono hIX

lemma Indep.encard_le_eRank (hI : M.Indep I) : I.encard ≤ M.eRank := by
  rw [← hI.eRk_eq_encard, eRank_def]
  exact M.eRk_mono hI.subset_ground

/-- A version of `erk_eq_zero_iff'` with no supportedness hypothesis. -/
lemma eRk_eq_zero_iff' : M.eRk X = 0 ↔ X ∩ M.E ⊆ M.loops := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (X ∩ M.E)
  rw [← eRk_inter_ground, ← hI.encard_eq_eRk, encard_eq_zero]
  refine ⟨fun h ↦ by simpa [h] using hI, fun h ↦ eq_empty_iff_forall_notMem.2 fun e heI ↦ ?_⟩
  exact (hI.indep.isNonloop_of_mem heI).not_isLoop (h (hI.subset heI))

@[deprecated (since := "2025-05-14")]
alias erk_eq_zero_iff' := eRk_eq_zero_iff'

@[simp]
lemma eRk_eq_zero_iff (hX : X ⊆ M.E := by aesop_mat) : M.eRk X = 0 ↔ X ⊆ M.loops := by
  rw [eRk_eq_zero_iff', inter_eq_self_of_subset_left hX]

@[deprecated (since := "2025-05-14")]
alias erk_eq_zero_iff := eRk_eq_zero_iff

@[simp]
lemma eRk_loops : M.eRk M.loops = 0 := by
  simp [eRk_eq_zero_iff']

/-! ### Submodularity -/

/-- The `ℕ∞`-valued rank function is submodular. -/
lemma eRk_inter_add_eRk_union_le (M : Matroid α) (X Y : Set α) :
    M.eRk (X ∩ Y) + M.eRk (X ∪ Y) ≤ M.eRk X + M.eRk Y := by
  obtain ⟨Ii, hIi⟩ := M.exists_isBasis' (X ∩ Y)
  obtain ⟨IX, hIX, hIX'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_left)
  obtain ⟨IY, hIY, hIY'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_right)
  rw [← hIX.eRk_eq_eRk_union, union_comm, ← hIY.eRk_eq_eRk_union, ← hIi.encard_eq_eRk,
    ← hIX.encard_eq_eRk, ← hIY.encard_eq_eRk, union_comm, ← encard_union_add_encard_inter, add_comm]
  exact add_le_add (eRk_le_encard _ _) (encard_mono (subset_inter hIX' hIY'))

alias eRk_submod := eRk_inter_add_eRk_union_le

/-- A version of submodularity applied to the insertion of some `e` into two sets. -/
lemma eRk_insert_inter_add_eRk_insert_union_le (M : Matroid α) (X Y : Set α) :
    M.eRk (insert e (X ∩ Y)) + M.eRk (insert e (X ∪ Y))
      ≤ M.eRk (insert e X) + M.eRk (insert e Y) := by
  rw [insert_inter_distrib, insert_union_distrib]
  apply M.eRk_submod

/-- A version of submodularity applied to the complements of two sets. -/
lemma eRk_compl_union_add_eRk_compl_inter_le (M : Matroid α) (X Y : Set α) :
    M.eRk (M.E \ (X ∪ Y)) + M.eRk (M.E \ (X ∩ Y)) ≤ M.eRk (M.E \ X) + M.eRk (M.E \ Y) := by
  rw [← diff_inter_diff, diff_inter]
  apply M.eRk_submod

/-- A version of submodularity applied to the complements of two insertions. -/
lemma eRk_compl_insert_union_add_eRk_compl_insert_inter_le (M : Matroid α) (X Y : Set α) :
    M.eRk (M.E \ insert e (X ∪ Y)) + M.eRk (M.E \ insert e (X ∩ Y)) ≤
      M.eRk (M.E \ insert e X) + M.eRk (M.E \ insert e Y) := by
  rw [insert_union_distrib, insert_inter_distrib]
  exact M.eRk_compl_union_add_eRk_compl_inter_le (insert e X) (insert e Y)

lemma eRk_union_le_eRk_add_eRk (M : Matroid α) (X Y : Set α) : M.eRk (X ∪ Y) ≤ M.eRk X + M.eRk Y :=
  le_add_self.trans (M.eRk_submod X Y)

lemma eRk_eq_eRk_union_eRk_le_zero (X : Set α) (hY : M.eRk Y ≤ 0) : M.eRk (X ∪ Y) = M.eRk X :=
  (((M.eRk_union_le_eRk_add_eRk X Y).trans (by gcongr)).trans_eq (add_zero _)).antisymm
    (M.eRk_mono subset_union_left)

lemma eRk_eq_eRk_diff_eRk_le_zero (X : Set α) (hY : M.eRk Y ≤ 0) : M.eRk (X \ Y) = M.eRk X := by
  rw [← eRk_eq_eRk_union_eRk_le_zero (X \ Y) hY, diff_union_self, eRk_eq_eRk_union_eRk_le_zero _ hY]

lemma eRk_le_eRk_inter_add_eRk_diff (M : Matroid α) (X Y : Set α) :
    M.eRk X ≤ M.eRk (X ∩ Y) + M.eRk (X \ Y) := by
  nth_rw 1 [← inter_union_diff X Y]; apply eRk_union_le_eRk_add_eRk

lemma eRk_le_eRk_add_eRk_diff (M : Matroid α) (h : Y ⊆ X) :
    M.eRk X ≤ M.eRk Y + M.eRk (X \ Y) := by
  nth_rw 1 [← union_diff_cancel h]; apply eRk_union_le_eRk_add_eRk

lemma eRk_union_le_encard_add_eRk (M : Matroid α) (X Y : Set α) :
    M.eRk (X ∪ Y) ≤ X.encard + M.eRk Y :=
  (M.eRk_union_le_eRk_add_eRk X Y).trans <| by grw [M.eRk_le_encard]

lemma eRk_union_le_eRk_add_encard (M : Matroid α) (X Y : Set α) :
    M.eRk (X ∪ Y) ≤ M.eRk X + Y.encard :=
  (M.eRk_union_le_eRk_add_eRk X Y).trans <| by grw [← M.eRk_le_encard]

lemma eRank_le_encard_add_eRk_compl (M : Matroid α) (X : Set α) :
    M.eRank ≤ X.encard + M.eRk (M.E \ X) :=
  le_trans (by rw [← eRk_inter_ground, eRank_def, union_diff_self,
    union_inter_cancel_right]) (M.eRk_union_le_encard_add_eRk X (M.E \ X))

end Basic

/-! ### Finiteness -/

lemma eRank_ne_top_iff (M : Matroid α) : M.eRank ≠ ⊤ ↔ M.RankFinite := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, encard_ne_top_iff]
  exact ⟨fun h ↦ hB.rankFinite_of_finite h, fun h ↦ hB.finite⟩

@[deprecated (since := "2025-04-13")] alias rankFinite_iff_eRk_ne_top := eRank_ne_top_iff

@[simp]
lemma eRank_eq_top_iff (M : Matroid α) : M.eRank = ⊤ ↔ M.RankInfinite := by
  rw [← not_rankFinite_iff, ← eRank_ne_top_iff, not_not]

@[deprecated (since := "2025-04-13")] alias rankInfinite_iff_eRk_eq_top := eRank_eq_top_iff

@[simp]
lemma eRank_lt_top_iff : M.eRank < ⊤ ↔ M.RankFinite := by
  simp [lt_top_iff_ne_top]

@[simp]
lemma eRank_eq_top [RankInfinite M] : M.eRank = ⊤ :=
  (eRank_eq_top_iff _).2 <| by assumption

@[simp]
lemma eRk_eq_top_iff : M.eRk X = ⊤ ↔ ¬ M.IsRkFinite X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eRk_eq_encard, encard_eq_top_iff, ← hI.finite_iff_isRkFinite, Set.Infinite]

lemma eRk_ne_top_iff : M.eRk X ≠ ⊤ ↔ M.IsRkFinite X := by
  simp

@[simp]
lemma eRk_lt_top_iff : M.eRk X < ⊤ ↔ M.IsRkFinite X := by
  rw [lt_top_iff_ne_top, eRk_ne_top_iff]

lemma IsRkFinite.eRk_lt_top (h : M.IsRkFinite X) : M.eRk X < ⊤ :=
  eRk_lt_top_iff.2 h

@[deprecated (since := "2025-04-13")] alias eRk_lt_top_of_finite := IsRkFinite.eRk_lt_top

/-- If `X` is a finite-rank set, and `I` is a subset of `X` of cardinality
no larger than the rank of `X` that spans `X`, then `I` is a basis for `X`. -/
lemma IsRkFinite.isBasis_of_subset_closure_of_subset_of_encard_le (hX : M.IsRkFinite X)
    (hXI : X ⊆ M.closure I) (hIX : I ⊆ X) (hI : I.encard ≤ M.eRk X) : M.IsBasis I X := by
  obtain ⟨J, hJ⟩ := M.exists_isBasis (I ∩ M.E)
  have hIJ := hJ.subset.trans inter_subset_left
  rw [← closure_inter_ground] at hXI
  replace hXI := hXI.trans <| M.closure_subset_closure_of_subset_closure hJ.subset_closure
  have hJX := hJ.indep.isBasis_of_subset_of_subset_closure (hIJ.trans hIX) hXI
  rw [← hJX.encard_eq_eRk] at hI
  rwa [← Finite.eq_of_subset_of_encard_le (hX.finite_of_isBasis hJX) hIJ hI]

/-- If `X` is a finite-rank set, and `Y` is a superset of `X` of rank no larger than that of `X`,
then `X` and `Y` have the same closure. -/
lemma IsRkFinite.closure_eq_closure_of_subset_of_eRk_ge_eRk (hX : M.IsRkFinite X) (hXY : X ⊆ Y)
    (hr : M.eRk Y ≤ M.eRk X) : M.closure X = M.closure Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans hXY)
  rw [hI.eRk_eq_encard, hJ.eRk_eq_encard] at hr
  rw [← closure_inter_ground, ← M.closure_inter_ground Y,
    ← hI.isBasis_inter_ground.closure_eq_closure,
    ← hJ.isBasis_inter_ground.closure_eq_closure, Finite.eq_of_subset_of_encard_le
      (hI.indep.finite_of_subset_isRkFinite hI.subset hX) hIJ hr]

/-! ### Insertion -/

lemma eRk_insert_le_add_one (M : Matroid α) (e : α) (X : Set α) :
    M.eRk (insert e X) ≤ M.eRk X + 1 :=
  union_singleton ▸ (M.eRk_union_le_eRk_add_eRk _ _).trans <| by
    gcongr; simpa using M.eRk_le_encard {e}

lemma eRk_insert_eq_add_one (he : e ∈ M.E \ M.closure X) : M.eRk (insert e X) = M.eRk X + 1 := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.closure_eq_closure, mem_diff, hI.indep.mem_closure_iff', not_and] at he
  rw [← eRk_closure_eq, ← closure_insert_congr_right hI.closure_eq_closure, hI.eRk_eq_encard,
    eRk_closure_eq, Indep.eRk_eq_encard (by tauto), encard_insert_of_notMem (by tauto)]

lemma exists_eRk_insert_eq_add_one_of_lt (h : M.eRk X < M.eRk Y) :
    ∃ y ∈ Y \ X, M.eRk (insert y X) = M.eRk X + 1 := by
  have hz : ¬ Y ∩ M.E ⊆ M.closure X := by
    contrapose! h
    simpa using M.eRk_mono h
  obtain ⟨e, ⟨heZ, heE⟩, heX⟩ := not_subset.1 hz
  refine ⟨e, ⟨heZ, fun heX' ↦ heX (mem_closure_of_mem' _ heX')⟩, eRk_insert_eq_add_one ⟨heE, heX⟩⟩

lemma IsRkFinite.closure_eq_closure_of_subset_of_forall_insert (hX : M.IsRkFinite X) (hXY : X ⊆ Y)
    (hY : ∀ e ∈ Y \ X, M.eRk (Insert.insert e X) ≤ M.eRk X) : M.closure X = M.closure Y := by
  refine hX.closure_eq_closure_of_subset_of_eRk_ge_eRk hXY <| not_lt.1 fun hlt ↦ ?_
  obtain ⟨z, hz, hr⟩ := exists_eRk_insert_eq_add_one_of_lt hlt
  simpa [hr, ENat.add_one_le_iff hX.eRk_lt_top.ne] using hY z hz

lemma eRk_eq_of_eRk_insert_le_forall (hXY : X ⊆ Y)
    (hY : ∀ e ∈ Y \ X, M.eRk (insert e X) ≤ M.eRk X) : M.eRk X = M.eRk Y := by
  by_cases hX : M.IsRkFinite X
  · rw [← eRk_closure_eq, hX.closure_eq_closure_of_subset_of_forall_insert hXY hY, eRk_closure_eq]
  rw [eRk_eq_top_iff.2 hX, eRk_eq_top_iff.2 (mt (fun h ↦ h.subset hXY) hX)]

/-! ### Independence -/

lemma indep_iff_eRk_eq_encard_of_finite (hI : I.Finite) : M.Indep I ↔ M.eRk I = I.encard := by
  refine ⟨fun h ↦ by rw [h.eRk_eq_encard], fun h ↦ ?_⟩
  obtain ⟨J, hJ⟩ := M.exists_isBasis' I
  rw [← hI.eq_of_subset_of_encard_le' hJ.subset]
  · exact hJ.indep
  rw [← h, ← hJ.eRk_eq_encard]

/-- In a matroid known to have finite rank, `Matroid.indep_iff_eRk_eq_encard_of_finite`
is true without the finiteness assumption. -/
lemma indep_iff_eRk_eq_encard [M.RankFinite] : M.Indep I ↔ M.eRk I = I.encard := by
  refine ⟨Indep.eRk_eq_encard, fun h ↦ ?_⟩
  obtain hfin | hinf := I.finite_or_infinite
  · rwa [indep_iff_eRk_eq_encard_of_finite hfin]
  rw [hinf.encard_eq] at h
  exact False.elim <| (M.isRkFinite_set I).eRk_lt_top.ne h

lemma IsRkFinite.indep_of_encard_le_eRk (hX : M.IsRkFinite I) (h : encard I ≤ M.eRk I) :
    M.Indep I := by
  rw [indep_iff_eRk_eq_encard_of_finite _]
  · exact (M.eRk_le_encard I).antisymm h
  simpa using h.trans_lt hX.eRk_lt_top

lemma eRk_lt_encard_of_dep_of_finite (h : X.Finite) (hX : M.Dep X) : M.eRk X < X.encard :=
  lt_of_le_of_ne (M.eRk_le_encard X) fun h' ↦
    ((indep_iff_eRk_eq_encard_of_finite h).mpr h').not_dep hX

lemma eRk_lt_encard_iff_dep_of_finite (hX : X.Finite) (hXE : X ⊆ M.E := by aesop_mat) :
    M.eRk X < X.encard ↔ M.Dep X := by
  refine ⟨fun h ↦ ?_, fun h ↦ eRk_lt_encard_of_dep_of_finite hX h⟩
  rw [← not_indep_iff, indep_iff_eRk_eq_encard_of_finite hX]
  exact h.ne

lemma Dep.eRk_lt_encard [M.RankFinite] (hX : M.Dep X) : M.eRk X < X.encard := by
  refine (M.eRk_le_encard X).lt_of_ne ?_
  rw [ne_eq, ← indep_iff_eRk_eq_encard]
  exact hX.not_indep

lemma eRk_lt_encard_iff_dep [M.RankFinite] (hXE : X ⊆ M.E := by aesop_mat) :
    M.eRk X < X.encard ↔ M.Dep X :=
  ⟨fun h ↦ (not_indep_iff).1 fun hi ↦ h.ne hi.eRk_eq_encard, Dep.eRk_lt_encard⟩

lemma Indep.exists_insert_of_encard_lt {I J : Set α} (hI : M.Indep I) (hJ : M.Indep J)
    (hcard : I.encard < J.encard) : ∃ e ∈ J \ I, M.Indep (insert e I) :=
  augment hI hJ hcard

lemma isBasis'_iff_indep_encard_eq_of_finite (hIfin : I.Finite) :
    M.IsBasis' I X ↔ I ⊆ X ∧ M.Indep I ∧ I.encard = M.eRk X := by
  refine ⟨fun h ↦ ⟨h.subset,h.indep, h.eRk_eq_encard.symm⟩, fun ⟨hIX, hI, hcard⟩ ↦ ?_⟩
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis'_of_subset hIX
  rwa [hIfin.eq_of_subset_of_encard_le hIJ (hJ.encard_eq_eRk.trans hcard.symm).le]

lemma isBasis_iff_indep_encard_eq_of_finite (hIfin : I.Finite) (hX : X ⊆ M.E := by aesop_mat) :
    M.IsBasis I X ↔ I ⊆ X ∧ M.Indep I ∧ I.encard = M.eRk X := by
  rw [← isBasis'_iff_isBasis, isBasis'_iff_indep_encard_eq_of_finite hIfin]

/-- If `I` is a finite independent subset of `X` for which `M.eRk X ≤ M.eRk I`,
then `I` is a `Basis'` for `X`. -/
lemma Indep.isBasis'_of_eRk_ge (hI : M.Indep I) (hIfin : I.Finite) (hIX : I ⊆ X)
    (h : M.eRk X ≤ M.eRk I) : M.IsBasis' I X :=
  (isBasis'_iff_indep_encard_eq_of_finite hIfin).2
    ⟨hIX, hI, by rw [h.antisymm (M.eRk_mono hIX), hI.eRk_eq_encard]⟩

lemma Indep.isBasis_of_eRk_ge (hI : M.Indep I) (hIfin : I.Finite) (hIX : I ⊆ X)
    (h : M.eRk X ≤ M.eRk I) (hX : X ⊆ M.E := by aesop_mat) : M.IsBasis I X :=
  (hI.isBasis'_of_eRk_ge hIfin hIX h).isBasis

lemma Indep.isBase_of_eRk_ge (hI : M.Indep I) (hIfin : I.Finite) (h : M.eRank ≤ M.eRk I) :
    M.IsBase I := by
  simpa using hI.isBasis_of_eRk_ge hIfin hI.subset_ground (M.eRk_ground.trans_le h)

lemma IsCircuit.eRk_add_one_eq {C : Set α} (hC : M.IsCircuit C) : M.eRk C + 1 = C.encard := by
  obtain ⟨I, hI⟩ := M.exists_isBasis C
  obtain ⟨e, ⟨heC, heI⟩, rfl⟩ := hC.isBasis_iff_insert_eq.1 hI
  rw [hI.eRk_eq_encard, encard_insert_of_notMem heI]

/-! ### Singletons -/

lemma IsLoop.eRk_eq (he : M.IsLoop e) : M.eRk {e} = 0 := by
  rw [← eRk_closure_eq, he.closure, loops, eRk_closure_eq, eRk_empty]

lemma IsNonloop.eRk_eq (he : M.IsNonloop e) : M.eRk {e} = 1 := by
  rw [← he.indep.isBasis_self.encard_eq_eRk, encard_singleton]

lemma eRk_singleton_eq [Loopless M] (he : e ∈ M.E := by aesop_mat) :
    M.eRk {e} = 1 :=
  (M.isNonloop_of_loopless he).eRk_eq

@[simp]
lemma eRk_singleton_le (M : Matroid α) (e : α) : M.eRk {e} ≤ 1 :=
  (M.eRk_le_encard {e}).trans_eq <| encard_singleton e

@[simp]
lemma eRk_singleton_eq_one_iff {e : α} : M.eRk {e} = 1 ↔ M.IsNonloop e := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.eRk_eq⟩
  rwa [← indep_singleton, indep_iff_eRk_eq_encard_of_finite (by simp), encard_singleton]

lemma eRk_eq_one_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.eRk X = 1 ↔ ∃ e ∈ X, M.IsNonloop e ∧ X ⊆ M.closure {e} := by
  refine ⟨?_, fun ⟨e, heX, he, hXe⟩ ↦ ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_isBasis X
    rw [hI.eRk_eq_encard, encard_eq_one]
    rintro ⟨e, rfl⟩
    exact ⟨e, singleton_subset_iff.1 hI.subset, indep_singleton.1 hI.indep, hI.subset_closure⟩
  rw [← he.eRk_eq]
  exact ((M.eRk_mono hXe).trans (M.eRk_closure_eq _).le).antisymm
    (M.eRk_mono (singleton_subset_iff.2 heX))

lemma eRk_le_one_iff [M.Nonempty] (hX : X ⊆ M.E := by aesop_mat) :
    M.eRk X ≤ 1 ↔ ∃ e ∈ M.E, X ⊆ M.closure {e} := by
  refine ⟨fun h ↦ ?_, fun ⟨e, _, he⟩ ↦ ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_isBasis X
    rw [hI.eRk_eq_encard, encard_le_one_iff_eq] at h
    obtain (rfl | ⟨e, rfl⟩) := h
    · obtain ⟨e, he⟩ := M.ground_nonempty
      exact ⟨e, he, hI.subset_closure.trans ((M.closure_subset_closure (empty_subset _)))⟩
    exact ⟨e, hI.indep.subset_ground rfl,  hI.subset_closure⟩
  refine (M.eRk_mono he).trans ?_
  rw [eRk_closure_eq, ← encard_singleton e]
  exact M.eRk_le_encard {e}

/-! ### Spanning Sets -/

lemma Spanning.eRk_eq (hX : M.Spanning X) : M.eRk X = M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBasis X
  exact (M.eRk_le_eRank X).antisymm <| by
    rw [← hB.encard_eq_eRk, ← (hB.isBase_of_spanning hX).encard_eq_eRank]

lemma spanning_iff_eRk_le' [RankFinite M] : M.Spanning X ↔ M.eRank ≤ M.eRk X ∧ X ⊆ M.E := by
  refine ⟨fun h ↦ ⟨h.eRk_eq.symm.le, h.subset_ground⟩, fun ⟨h, hX⟩ ↦ ?_⟩
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  exact (hI.indep.isBase_of_eRk_ge
    hI.indep.finite (h.trans hI.eRk_eq_eRk.symm.le)).spanning_of_superset hI.subset

lemma spanning_iff_eRk_le [RankFinite M] (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning X ↔ M.eRank ≤ M.eRk X := by
  rw [spanning_iff_eRk_le', and_iff_left hX]

lemma Spanning.eRank_restrict (hX : M.Spanning X) : (M ↾ X).eRank = M.eRank := by
  rw [eRank_def, restrict_ground_eq, restrict_eRk_eq _ rfl.subset, hX.eRk_eq]

/-! ### Constructions -/

@[simp]
lemma eRank_map {β : Type*} {f : α → β} (M : Matroid α) (hf : InjOn f M.E) :
    (M.map f hf).eRank = M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← (hB.map hf).encard_eq_eRank, ← hB.encard_eq_eRank, (hf.mono hB.subset_ground).encard_image]

@[simp]
lemma eRk_map {β : Type*} {f : α → β} (M : Matroid α) (hf : InjOn f M.E)
    (hX : X ⊆ M.E := by aesop_mat) : (M.map f hf).eRk (f '' X) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  rw [hI.eRk_eq_encard, (hI.map hf).eRk_eq_encard, (hf.mono hI.indep.subset_ground).encard_image]

@[simp]
lemma eRk_comap {β : Type*} {f : α → β} (M : Matroid β) (X : Set α) :
    (M.comap f).eRk X = M.eRk (f '' X) := by
  obtain ⟨I, hI⟩ := (M.comap f).exists_isBasis' X
  obtain ⟨hI', hinj, -⟩ := comap_isBasis'_iff.1 hI
  rw [← hI.encard_eq_eRk, ← hI'.encard_eq_eRk, hinj.encard_image]

@[simp]
lemma eRk_loopyOn (X Y : Set α) : (loopyOn Y).eRk X = 0 := by
  obtain ⟨I, hI⟩ := (loopyOn Y).exists_isBasis' X
  rw [hI.eRk_eq_encard, loopyOn_indep_iff.1 hI.indep, encard_empty]

@[simp]
lemma eRank_loopyOn (X : Set α) : (loopyOn X).eRank = 0 := by
  rw [eRank_def, eRk_loopyOn]

lemma eRank_eq_zero_iff : M.eRank = 0 ↔ M = loopyOn M.E := by
  refine ⟨fun h ↦ closure_empty_eq_ground_iff.1 ?_, fun h ↦ by rw [h, eRank_loopyOn]⟩
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, encard_eq_zero] at h
  rw [← h, hB.closure_eq]

lemma exists_of_eRank_eq_zero (h : M.eRank = 0) : ∃ X, M = loopyOn X :=
  ⟨M.E, by simpa [eRank_eq_zero_iff] using h⟩

@[simp]
lemma eRank_emptyOn (α : Type*) : (emptyOn α).eRank = 0 := by
  rw [eRank_eq_zero_iff, emptyOn_ground, loopyOn_empty]

lemma eq_loopyOn_iff_eRank : M = loopyOn X ↔ M.eRank = 0 ∧ M.E = X :=
  ⟨fun h ↦ by rw [h]; simp, fun ⟨h,h'⟩ ↦ by rw [← h', ← eRank_eq_zero_iff, h]⟩

@[simp]
lemma eRank_freeOn (X : Set α) : (freeOn X).eRank = X.encard := by
  rw [eRank_def, freeOn_ground, (freeOn_indep_iff.2 rfl.subset).eRk_eq_encard]

lemma eRk_freeOn (hXY : X ⊆ Y) : (freeOn Y).eRk X = X.encard := by
  obtain ⟨I, hI⟩ := (freeOn Y).exists_isBasis X
  rw [hI.eRk_eq_encard, (freeOn_indep hXY).eq_of_isBasis hI]

/-! ### Duality -/

lemma IsBase.encard_compl_eq (hB : M.IsBase B) : (M.E \ B).encard = M✶.eRank :=
  (hB.compl_isBase_dual).encard_eq_eRank

/-- A subtraction-free formula for the rank of a set in the dual matroid. -/
lemma eRk_dual_add_eRank (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M✶.eRk X + M.eRank = M.eRk (M.E \ X) + X.encard := by
  obtain ⟨I, hI⟩ := M✶.exists_isBasis X
  obtain ⟨B, hB, rfl⟩ := hI.exists_isBasis_inter_eq_of_superset hX
  have hB' : M✶.IsBase B := isBasis_ground_iff.1 hB
  have hd : M.IsBasis (M.E \ B ∩ (M.E \ X)) (M.E \ X) := by
    simpa using hB'.inter_isBasis_iff_compl_inter_isBasis_dual.1 hI
  rw [← hB'.compl_isBase_of_dual.encard_eq_eRank, hI.eRk_eq_encard, hd.eRk_eq_encard,
    ← encard_union_eq (by tauto_set), ← encard_union_eq (by tauto_set)]
  exact congr_arg _ (by tauto_set)

/-- A version of `Matroid.dual_eRk_add_eRank` for non-subsets of the ground set. -/
lemma eRk_dual_add_eRank' (M : Matroid α) (X : Set α) :
    M✶.eRk X + M.eRank = M.eRk (M.E \ X) + (X ∩ M.E).encard := by
  rw [← diff_inter_self_eq_diff, ← eRk_dual_add_eRank .., ← dual_ground, eRk_inter_ground]

@[simp]
lemma eRank_add_eRank_dual (M : Matroid α) : M.eRank + M✶.eRank = M.E.encard := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, ← hB.compl_isBase_dual.encard_eq_eRank,
    ← encard_union_eq disjoint_sdiff_right, union_diff_cancel hB.subset_ground]

end Matroid
