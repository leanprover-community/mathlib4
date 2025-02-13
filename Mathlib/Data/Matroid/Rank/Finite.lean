/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Matroid.Closure

/-!
# Finite-rank sets

`Matroid.IsRkFinite M X`  means that every basis of the set `X` in the matroid `M` is finite,
or equivalently that the restriction of `M` to `X` is `Matroid.RankFinite`.
Sets in a matroid with `IsRkFinite` are the largest class of sets for which one can do nontrivial
integer arithmetic involving the rank function.

# Implementation Details

Unlike most set predicates on matroids, a set `X` with `M.IsRkFinite X` need not satisfy `X ⊆ M.E`,
so may contain junk elements. This seems to be what makes the definition easiest to use.
-/

variable {α : Type*} {M : Matroid α} {X Y I : Set α} {e : α}

open Set

namespace Matroid

/-- `Matroid.IsRkFinite M X` means that every basis of `X` in `M` is finite. -/
def IsRkFinite (M : Matroid α) (X : Set α) : Prop := (M ↾ X).RankFinite

lemma IsRkFinite.rankFinite (hX : M.IsRkFinite X) : (M ↾ X).RankFinite :=
  hX

lemma Basis'.finite_iff_isRkFinite (hI : M.Basis' I X) : I.Finite ↔ M.IsRkFinite X :=
  ⟨fun h ↦ ⟨I, hI, h⟩, fun (_ : (M ↾ X).RankFinite) ↦ hI.base_restrict.finite⟩

alias ⟨_, Basis'.finite_of_isRkFinite⟩ := Basis'.finite_iff_isRkFinite

lemma Basis.finite_iff_isRkFinite (hI : M.Basis I X) : I.Finite ↔ M.IsRkFinite X :=
  hI.basis'.finite_iff_isRkFinite

alias ⟨_, Basis.finite_of_isRkFinite⟩ := Basis.finite_iff_isRkFinite

lemma Basis'.isRkFinite_of_finite (hI : M.Basis' I X) (hIfin : I.Finite) : M.IsRkFinite X :=
  ⟨I, hI, hIfin⟩

lemma Basis.isRkFinite_of_finite (hI : M.Basis I X) (hIfin : I.Finite) : M.IsRkFinite X :=
  ⟨I, hI.basis', hIfin⟩

/-- A `Basis'` of an `IsRkFinite` set is finite. -/
lemma IsRkFinite.finite_of_basis' (h : M.IsRkFinite X) (hI : M.Basis' I X) : I.Finite :=
  have := h.rankFinite
  (base_restrict_iff'.2 hI).finite

lemma IsRkFinite.finite_of_basis (h : M.IsRkFinite X) (hI : M.Basis I X) : I.Finite :=
  h.finite_of_basis' hI.basis'

/-- An `IsRkFinite` set has a finite `Basis'`-/
lemma IsRkFinite.exists_finite_basis' (h : M.IsRkFinite X) : ∃ I, M.Basis' I X ∧ I.Finite :=
  h.exists_finite_base

/-- An `IsRkFinite` set has a finset `Basis'` -/
lemma IsRkFinite.exists_finset_basis' (h : M.IsRkFinite X) : ∃ (I : Finset α), M.Basis' I X :=
  let ⟨I, hI, hIfin⟩ := h.exists_finite_basis'
  ⟨hIfin.toFinset, by simpa⟩

/-- A set satisfies `IsRkFinite` iff it has a finite `Basis'` -/
lemma isRkFinite_iff_exists_basis' : M.IsRkFinite X ↔ ∃ I, M.Basis' I X ∧ I.Finite :=
  ⟨IsRkFinite.exists_finite_basis', fun ⟨_, hIX, hI⟩ ↦ hIX.isRkFinite_of_finite hI⟩

lemma IsRkFinite.subset (h : M.IsRkFinite X) (hXY : Y ⊆ X) : M.IsRkFinite Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' Y
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans hXY)
  exact hI.isRkFinite_of_finite <| (hJ.finite_of_isRkFinite h).subset hIJ

@[simp]
lemma isRkFinite_inter_ground_iff : M.IsRkFinite (X ∩ M.E) ↔ M.IsRkFinite X :=
  let ⟨_I, hI⟩ := M.exists_basis' X
  ⟨fun h ↦ hI.isRkFinite_of_finite (hI.basis_inter_ground.finite_of_isRkFinite h),
    fun h ↦ h.subset inter_subset_left⟩

lemma IsRkFinite.inter_ground (h : M.IsRkFinite X) : M.IsRkFinite (X ∩ M.E) :=
  isRkFinite_inter_ground_iff.2 h

lemma isRkFinite_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.IsRkFinite X ↔ ∃ I, M.Basis I X ∧ I.Finite := by
  simp_rw [isRkFinite_iff_exists_basis', M.basis'_iff_basis hX]

lemma Indep.isRkFinite_iff_finite (hI : M.Indep I) : M.IsRkFinite I ↔ I.Finite :=
  hI.basis_self.finite_iff_isRkFinite.symm

alias ⟨Indep.finite_of_isRkFinite, _⟩ := Indep.isRkFinite_iff_finite

lemma isRkFinite_of_finite (M : Matroid α) (hX : X.Finite) : M.IsRkFinite X :=
  let ⟨_, hI⟩ := M.exists_basis' X
  hI.isRkFinite_of_finite (hX.subset hI.subset)

lemma Indep.subset_finite_basis'_of_subset_of_isRkFinite (hI : M.Indep I) (hIX : I ⊆ X)
    (hX : M.IsRkFinite X) : ∃ J, M.Basis' J X ∧ I ⊆ J ∧ J.Finite :=
  (hI.subset_basis'_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_isRkFinite hX⟩

lemma Indep.subset_finite_basis_of_subset_of_isRkFinite (hI : M.Indep I) (hIX : I ⊆ X)
    (hX : M.IsRkFinite X) (hXE : X ⊆ M.E := by aesop_mat) : ∃ J, M.Basis J X ∧ I ⊆ J ∧ J.Finite :=
  (hI.subset_basis_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_isRkFinite hX⟩

lemma isRkFinite_singleton : M.IsRkFinite {e} :=
  isRkFinite_of_finite M (finite_singleton e)

@[simp]
lemma IsRkFinite.empty (M : Matroid α) : M.IsRkFinite ∅ :=
  isRkFinite_of_finite M finite_empty

lemma IsRkFinite.finite_of_indep_subset (hX : M.IsRkFinite X) (hI : M.Indep I) (hIX : I ⊆ X) :
    I.Finite :=
  hI.finite_of_isRkFinite <| hX.subset hIX

@[simp]
lemma isRkFinite_ground_iff_rankFinite : M.IsRkFinite M.E ↔ M.RankFinite := by
  rw [IsRkFinite, restrict_ground_eq_self]

lemma isRkFinite_ground (M : Matroid α) [RankFinite M] : M.IsRkFinite M.E := by
  rwa [isRkFinite_ground_iff_rankFinite]

lemma Indep.finite_of_subset_isRkFinite (hI : M.Indep I) (hIX : I ⊆ X) (hX : M.IsRkFinite X) :
    I.Finite :=
  hX.finite_of_indep_subset hI hIX

lemma IsRkFinite.closure (h : M.IsRkFinite X) : M.IsRkFinite (M.closure X) :=
  let ⟨_, hI⟩ := M.exists_basis' X
  hI.basis_closure_right.isRkFinite_of_finite <| hI.finite_of_isRkFinite h

@[simp]
lemma isRkFinite_closure_iff : M.IsRkFinite (M.closure X) ↔ M.IsRkFinite X := by
  rw [← isRkFinite_inter_ground_iff (X := X)]
  exact ⟨fun h ↦ h.subset <| M.inter_ground_subset_closure X, fun h ↦ by simpa using h.closure⟩

lemma IsRkFinite.union (hX : M.IsRkFinite X) (hY : M.IsRkFinite Y) : M.IsRkFinite (X ∪ Y) := by
  obtain ⟨I, hI, hIfin⟩ := hX.exists_finite_basis'
  obtain ⟨J, hJ, hJfin⟩ := hY.exists_finite_basis'
  rw [← isRkFinite_inter_ground_iff]
  refine (M.isRkFinite_of_finite (hIfin.union hJfin)).closure.subset ?_
  rw [closure_union_congr_left hI.closure_eq_closure,
    closure_union_congr_right hJ.closure_eq_closure]
  exact inter_ground_subset_closure M (X ∪ Y)

lemma IsRkFinite.isRkFinite_union_iff (hX : M.IsRkFinite X) :
    M.IsRkFinite (X ∪ Y) ↔ M.IsRkFinite Y :=
  ⟨fun h ↦ h.subset subset_union_right, fun h ↦ hX.union h⟩

lemma IsRkFinite.isRkFinite_diff_iff (hX : M.IsRkFinite X) :
    M.IsRkFinite (Y \ X) ↔ M.IsRkFinite Y := by
  rw [← hX.isRkFinite_union_iff, union_diff_self, hX.isRkFinite_union_iff]

lemma IsRkFinite.inter_right (hX : M.IsRkFinite X) : M.IsRkFinite (X ∩ Y) :=
  hX.subset inter_subset_left

lemma IsRkFinite.inter_left (hX : M.IsRkFinite X) : M.IsRkFinite (Y ∩ X) :=
  hX.subset inter_subset_right

lemma IsRkFinite.diff (hX : M.IsRkFinite X) : M.IsRkFinite (X \ Y) :=
  hX.subset diff_subset

lemma IsRkFinite.insert (hX : M.IsRkFinite X) (e : α) : M.IsRkFinite (insert e X) := by
  rw [← union_singleton]
  exact hX.union M.isRkFinite_singleton

@[simp]
lemma isRkFinite_insert_iff {e : α} : M.IsRkFinite (insert e X) ↔ M.IsRkFinite X := by
  rw [← singleton_union, isRkFinite_singleton.isRkFinite_union_iff]

@[simp]
lemma IsRkFinite.diff_singleton_iff : M.IsRkFinite (X \ {e}) ↔ M.IsRkFinite X := by
  rw [isRkFinite_singleton.isRkFinite_diff_iff]

lemma isRkFinite_set (M : Matroid α) [RankFinite M] (X : Set α) : M.IsRkFinite X :=
  let ⟨_, hI⟩ := M.exists_basis' X
  hI.isRkFinite_of_finite hI.indep.finite

/-- A union of finitely many `IsRkFinite` sets is `IsRkFinite`. -/
lemma IsRkFinite.iUnion {ι : Type*} [Fintype ι] {Xs : ι → Set α} (h : ∀ i, M.IsRkFinite (Xs i)) :
    M.IsRkFinite (⋃ i, Xs i) := by
  choose Is hIs using fun i ↦ M.exists_basis' (Xs i)
  have hfin : (⋃ i, Is i).Finite := finite_iUnion <| fun i ↦ (h i).finite_of_basis' (hIs i)
  refine isRkFinite_inter_ground_iff.1 <| (M.isRkFinite_of_finite hfin).closure.subset ?_
  rw [iUnion_inter, iUnion_subset_iff]
  exact fun i ↦ (hIs i).basis_inter_ground.subset_closure.trans <| M.closure_subset_closure <|
    subset_iUnion ..

end Matroid
