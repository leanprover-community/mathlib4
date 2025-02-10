/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Matroid.Closure

/-!
# Finite-rank sets

For `M : Matroid α` and `X : Set α`,
`Matroid.RkFin M X`  means that every basis of `X` in `M` is finite,
or equivalently that the restriction to `X` is `Matroid.RankFinite`.
`RkFin` sets in a matroid are the largest class of sets for which one can do nontrivial
integer arithmetic involving the rank function.

# Implementation Details

Unlike most set predicates on matroids, a set `X` with `M.RkFin X` need not satisfy `X ⊆ M.E`,
so may contain junk elements. This seems to be what makes the definition easiest to use.
-/

variable {α : Type*} {M : Matroid α} {X Y I : Set α} {e : α}

open Set

namespace Matroid

/-- a `RkFin` set in `M` is one whose bases are all finite. -/
def RkFin (M : Matroid α) (X : Set α) := (M ↾ X).RankFinite

lemma RkFin.rankFinite (hX : M.RkFin X) : (M ↾ X).RankFinite :=
  hX

/-- A `Basis'` of a `RkFin` set is finite. -/
lemma RkFin.finite_of_basis' (h : M.RkFin X) (hI : M.Basis' I X) : I.Finite :=
  have := h.rankFinite
  (base_restrict_iff'.2 hI).finite

lemma RkFin.finite_of_basis (h : M.RkFin X) (hI : M.Basis I X) : I.Finite :=
  h.finite_of_basis' hI.basis'

lemma Basis'.finite_of_rkFin (hI : M.Basis' I X) (h : M.RkFin X) : I.Finite :=
  h.finite_of_basis' hI

lemma Basis.finite_of_rkFin (hI : M.Basis I X) (h : M.RkFin X) : I.Finite :=
  h.finite_of_basis hI

lemma Basis'.rkFin_of_finite (hI : M.Basis' I X) (hIfin : I.Finite) : M.RkFin X :=
  ⟨I, hI, hIfin⟩

lemma Basis.rkFin_of_finite (hI : M.Basis I X) (hIfin : I.Finite) : M.RkFin X :=
  ⟨I, hI.basis', hIfin⟩

lemma Basis'.finite_iff_rkFin (hI : M.Basis' I X) : I.Finite ↔ M.RkFin X :=
  ⟨hI.rkFin_of_finite, fun h ↦ h.finite_of_basis' hI⟩

lemma Basis.finite_iff_rkFin (hI : M.Basis I X) : I.Finite ↔ M.RkFin X :=
  hI.basis'.finite_iff_rkFin

/-- A `RkFin` set has a finite `Basis'`-/
lemma RkFin.exists_finite_basis' (h : M.RkFin X) : ∃ I, M.Basis' I X ∧ I.Finite :=
  h.exists_finite_base

/-- A `RkFin` set has a finset `Basis'` -/
lemma RkFin.exists_finset_basis' (h : M.RkFin X) : ∃ (I : Finset α), M.Basis' I X :=
  let ⟨I, hI, hIfin⟩ := h.exists_finite_basis'
  ⟨hIfin.toFinset, by simpa⟩

/-- A set is `RkFin` iff it has a finite `Basis'` -/
lemma rkFin_iff_exists_basis' : M.RkFin X ↔ ∃ I, M.Basis' I X ∧ I.Finite :=
  ⟨RkFin.exists_finite_basis', fun ⟨_, hIX, hI⟩ ↦ hIX.rkFin_of_finite hI⟩

lemma RkFin.subset (h : M.RkFin X) (hXY : Y ⊆ X) : M.RkFin Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' Y
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans hXY)
  exact hI.rkFin_of_finite <| (hJ.finite_of_rkFin h).subset hIJ

@[simp]
lemma rkFin_inter_ground_iff : M.RkFin (X ∩ M.E) ↔ M.RkFin X :=
  let ⟨_I, hI⟩ := M.exists_basis' X
  ⟨fun h ↦ hI.rkFin_of_finite (hI.basis_inter_ground.finite_of_rkFin h),
    fun h ↦ h.subset inter_subset_left⟩

lemma RkFin.to_inter_ground (h : M.RkFin X) : M.RkFin (X ∩ M.E) :=
  rkFin_inter_ground_iff.2 h

lemma rkFin_iff (hX : X ⊆ M.E := by aesop_mat) : M.RkFin X ↔ ∃ I, M.Basis I X ∧ I.Finite := by
  simp_rw [rkFin_iff_exists_basis', M.basis'_iff_basis hX]

lemma Indep.rkFin_iff_finite (hI : M.Indep I) : M.RkFin I ↔ I.Finite :=
  hI.basis_self.finite_iff_rkFin.symm

lemma Indep.finite_of_rkFin (hI : M.Indep I) (hfin : M.RkFin I) : I.Finite :=
  hI.basis_self.finite_of_rkFin hfin

lemma rkFin_of_finite (M : Matroid α) (hX : X.Finite) : M.RkFin X :=
  let ⟨_, hI⟩ := M.exists_basis' X
  hI.rkFin_of_finite (hX.subset hI.subset)

lemma Indep.subset_finite_basis'_of_subset_of_rkFin (hI : M.Indep I) (hIX : I ⊆ X)
    (hX : M.RkFin X) : ∃ J, M.Basis' J X ∧ I ⊆ J ∧ J.Finite :=
  (hI.subset_basis'_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_rkFin hX⟩

lemma Indep.subset_finite_basis_of_subset_of_rkFin (hI : M.Indep I) (hIX : I ⊆ X)
    (hX : M.RkFin X) (hXE : X ⊆ M.E := by aesop_mat) : ∃ J, M.Basis J X ∧ I ⊆ J ∧ J.Finite :=
  (hI.subset_basis_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_rkFin hX⟩

lemma rkFin_singleton (M : Matroid α) (e : α) : M.RkFin {e} :=
  rkFin_of_finite M (finite_singleton e)

@[simp]
lemma RkFin.empty (M : Matroid α) : M.RkFin ∅ :=
  rkFin_of_finite M finite_empty

lemma not_rkFin_superset (h : ¬M.RkFin X) (hXY : X ⊆ Y) : ¬M.RkFin Y :=
  fun h' ↦ h (h'.subset hXY)

lemma RkFin.finite_of_indep_subset (hX : M.RkFin X) (hI : M.Indep I) (hIX : I ⊆ X) : I.Finite :=
  hI.finite_of_rkFin (hX.subset hIX)

@[simp]
lemma rkFin_ground_iff_rankFinite : M.RkFin M.E ↔ M.RankFinite := by
  rw [RkFin, restrict_ground_eq_self]

lemma rkFin_ground (M : Matroid α) [RankFinite M] : M.RkFin M.E := by
  rwa [rkFin_ground_iff_rankFinite]

lemma Indep.finite_of_subset_rkFin (hI : M.Indep I) (hIX : I ⊆ X) (hX : M.RkFin X) : I.Finite :=
  hX.finite_of_indep_subset hI hIX

lemma RkFin.closure (h : M.RkFin X) : M.RkFin (M.closure X) :=
  let ⟨_, hI⟩ := M.exists_basis' X
  hI.basis_closure_right.rkFin_of_finite <| hI.finite_of_rkFin h

@[simp]
lemma rkFin_closure_iff : M.RkFin (M.closure X) ↔ M.RkFin X := by
  rw [← rkFin_inter_ground_iff (X := X)]
  exact ⟨fun h ↦ h.subset <| M.inter_ground_subset_closure X, fun h ↦ by simpa using h.closure⟩

lemma RkFin.union (hX : M.RkFin X) (hY : M.RkFin Y) : M.RkFin (X ∪ Y) := by
  obtain ⟨I, hI, hIfin⟩ := hX.exists_finite_basis'
  obtain ⟨J, hJ, hJfin⟩ := hY.exists_finite_basis'
  rw [← rkFin_inter_ground_iff]
  refine (M.rkFin_of_finite (hIfin.union hJfin)).closure.subset ?_
  rw [closure_union_congr_left hI.closure_eq_closure,
    closure_union_congr_right hJ.closure_eq_closure]
  exact inter_ground_subset_closure M (X ∪ Y)

lemma RkFin.rkFin_union_iff (hX : M.RkFin X) : M.RkFin (X ∪ Y) ↔ M.RkFin Y :=
  ⟨fun h ↦ h.subset subset_union_right, fun h ↦ hX.union h⟩

lemma RkFin.rkFin_diff_iff (hX : M.RkFin X) : M.RkFin (Y \ X) ↔ M.RkFin Y := by
  rw [← hX.rkFin_union_iff, union_diff_self, hX.rkFin_union_iff]

lemma RkFin.inter_right (hX : M.RkFin X) : M.RkFin (X ∩ Y) :=
  hX.subset inter_subset_left

lemma RkFin.inter_left (hX : M.RkFin X) : M.RkFin (Y ∩ X) :=
  hX.subset inter_subset_right

lemma RkFin.diff (hX : M.RkFin X) : M.RkFin (X \ Y) :=
  hX.subset diff_subset

lemma RkFin.insert (hX : M.RkFin X) (e : α) : M.RkFin (insert e X) := by
  rw [← union_singleton]; exact hX.union (M.rkFin_singleton e)

@[simp]
lemma rkFin_insert_iff {e : α} : M.RkFin (insert e X) ↔ M.RkFin X := by
  rw [← singleton_union, (M.rkFin_singleton e).rkFin_union_iff]

@[simp]
lemma RkFin.diff_singleton_iff : M.RkFin (X \ {e}) ↔ M.RkFin X := by
  rw [(M.rkFin_singleton e).rkFin_diff_iff]

lemma to_rkFin (M : Matroid α) [RankFinite M] (X : Set α) : M.RkFin X :=
  let ⟨_, hI⟩ := M.exists_basis' X
  hI.rkFin_of_finite hI.indep.finite

/-- A union of finitely many `RkFin` sets is `RkFin`. -/
lemma RkFin.iUnion {ι : Type*} [Fintype ι] {Xs : ι → Set α} (h : ∀ i, M.RkFin (Xs i)) :
    M.RkFin (⋃ i, Xs i) := by
  choose Is hIs using fun i ↦ M.exists_basis' (Xs i)
  have hfin : (⋃ i, Is i).Finite := finite_iUnion <| fun i ↦ (h i).finite_of_basis' (hIs i)
  refine rkFin_inter_ground_iff.1 <| (M.rkFin_of_finite hfin).closure.subset ?_
  rw [iUnion_inter, iUnion_subset_iff]
  exact fun i ↦ (hIs i).basis_inter_ground.subset_closure.trans <| M.closure_subset_closure <|
    subset_iUnion ..

end Matroid
