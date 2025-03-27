/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Matroid.Rank.Finite
import Mathlib.Data.Matroid.Loop

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
In fact, if `α` is finite, then any function `Set α → ℕ∞` satisfying these these properties
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

# Notes

It is natural to ask if equicardinality of bases holds if 'cardinality' refers to
a term in `Cardinal` instead of `ℕ∞`, but the answer is that it doesn't.
The cardinal-valued rank functions `Matroid.cRank` and `Matroid.cRk`
are defined in `Data.Matroid.Rank.Cardinal`, but have less desirable properties in general.
See the module docstring of this file for a discussion.

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
lemma eRank_map {β : Type*} (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    (M.map f hf).eRank = M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← (hB.map hf).encard_eq_eRank, ← hB.encard_eq_eRank, (hf.mono hB.subset_ground).encard_image]

@[simp]
lemma eRank_loopyOn (E : Set α) : (loopyOn E).eRank = 0 := by
  simp [← (show (loopyOn E).IsBase ∅ by simp).encard_eq_eRank]

@[simp]
lemma eRank_emptyOn (α : Type*) : (emptyOn α).eRank = 0 := by
  simp [← (show (emptyOn α).IsBase ∅ by simp).encard_eq_eRank]

@[simp]
lemma eRk_ground (M : Matroid α) : M.eRk M.E = M.eRank :=
  M.eRank_def.symm

@[simp]
lemma eRk_inter_ground (M : Matroid α) (X : Set α) : M.eRk (X ∩ M.E) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.eRk_eq_eRk, hI.isBasis_inter_ground.eRk_eq_eRk]

@[simp]
lemma eRk_ground_inter (M : Matroid α) (X : Set α) : M.eRk (M.E ∩ X) = M.eRk X := by
  rw [inter_comm, eRk_inter_ground]

lemma eRk_eq_eRank (hX : M.E ⊆ X) : M.eRk X = M.eRank := by
  rw [← eRk_inter_ground, inter_eq_self_of_subset_right hX, eRank_def]

@[simp]
lemma eRk_union_ground (M : Matroid α) (X : Set α) : M.eRk (X ∪ M.E) = M.eRank := by
  rw [← eRk_inter_ground, inter_eq_self_of_subset_right subset_union_right, eRank_def]

@[simp]
lemma eRk_ground_union (M : Matroid α) (X : Set α) : M.eRk (M.E ∪ X) = M.eRank := by
  rw [union_comm, eRk_union_ground]

lemma eRk_insert_of_not_mem_ground (X : Set α) (he : e ∉ M.E) : M.eRk (insert e X) = M.eRk X := by
  rw [← eRk_inter_ground, insert_inter_of_not_mem he, eRk_inter_ground]

lemma eRk_compl_union_of_disjoint (M : Matroid α) (hXY : Disjoint X Y) :
    M.eRk (M.E \ X ∪ Y) = M.eRk (M.E \ X) := by
  rw [← eRk_inter_ground, union_inter_distrib_right, inter_eq_self_of_subset_left diff_subset,
    union_eq_self_of_subset_right
      (subset_diff.2 ⟨inter_subset_right, hXY.symm.mono_left inter_subset_left⟩)]

lemma one_le_eRank (M : Matroid α) [RankPos M] : 1 ≤ M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, one_le_encard_iff_nonempty]
  exact hB.nonempty

lemma rankFinite_iff_eRank_ne_top (M : Matroid α) : M.RankFinite ↔ M.eRank ≠ ⊤ := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, encard_ne_top_iff]
  exact ⟨fun h ↦ hB.finite, fun h ↦ hB.rankFinite_of_finite h⟩

lemma rankInfinite_iff_eRank_eq_top (M : Matroid α) : M.RankInfinite ↔ M.eRank = ⊤ := by
  rw [← not_rankFinite_iff, rankFinite_iff_eRank_ne_top, not_not]

@[simp]
lemma eRank_eq_top [RankInfinite M] : M.eRank = ⊤ := by
  simpa using (rankFinite_iff_eRank_ne_top M).not.1 M.not_rankFinite

@[simp]
lemma eRk_map_eq {β : Type*} {f : α → β} (M : Matroid α) (hf : InjOn f M.E)
    (hX : X ⊆ M.E := by aesop_mat) : (M.map f hf).eRk (f '' X) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  rw [hI.eRk_eq_encard, (hI.map hf).eRk_eq_encard, (hf.mono hI.indep.subset_ground).encard_image]

@[simp]
lemma eRk_comap_eq {β : Type*} {f : α → β} (M : Matroid β) (X : Set α) :
    (M.comap f).eRk X = M.eRk (f '' X) := by
  obtain ⟨I, hI⟩ := (M.comap f).exists_isBasis' X
  obtain ⟨hI', hinj, -⟩ := comap_isBasis'_iff.1 hI
  rw [← hI.encard_eq_eRk, ← hI'.encard_eq_eRk, hinj.encard_image]

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
    M.eRk (X ∪ M.closure Y) = M.eRk (X ∪ Y) :=
  by rw [← eRk_closure_eq, closure_union_closure_right_eq, eRk_closure_eq]

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

lemma eRk_lt_top_of_finite (M : Matroid α) (hX : X.Finite) : M.eRk X < ⊤ := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eRk_eq_encard, encard_lt_top_iff]
  exact hX.subset hI.subset

lemma IsBasis'.eRk_eq_eRk_union (hIX : M.IsBasis' I X) (Y : Set α) :
    M.eRk (I ∪ Y) = M.eRk (X ∪ Y) := by
  rw [← eRk_union_closure_left_eq, hIX.closure_eq_closure, eRk_union_closure_left_eq]

lemma IsBasis'.eRk_eq_eRk_insert (hIX : M.IsBasis' I X) (e : α) :
    M.eRk (insert e I) = M.eRk (insert e X) := by
  rw [← union_singleton, hIX.eRk_eq_eRk_union, union_singleton]

lemma IsBasis.eRk_eq_eRk_union (hIX : M.IsBasis I X) (Y : Set α) : M.eRk (I ∪ Y) = M.eRk (X ∪ Y) :=
  hIX.isBasis'.eRk_eq_eRk_union Y

lemma IsBasis.eRk_eq_eRk_insert (hIX : M.IsBasis I X) (e : α) :
    M.eRk (insert e I) = M.eRk (insert e X) :=
  by rw [← union_singleton, hIX.eRk_eq_eRk_union, union_singleton]

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

end Basic

end Matroid
