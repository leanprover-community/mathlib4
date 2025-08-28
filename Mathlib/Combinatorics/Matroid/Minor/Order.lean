/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Combinatorics.Matroid.Minor.Contract

/-!
# Matroid Minors

A matroid `N = M ／ C ＼ D` obtained from a matroid `M` by a contraction then a delete,
(or equivalently, by any number of contractions/deletions in any order) is a *minor* of `M`.
This gives a partial order on `Matroid α` that is ubiquitous in matroid theory,
and interacts nicely with duality and linear representations.

Although we provide a `PartialOrder` instance on `Matroid α` corresponding to the minor order,
we do not use the `M ≤ N` / `N < M` notation directly,
instead writing `N ≤m M` and `N <m M` for more convenient dot notation.

# Main Declarations

* `Matroid.IsMinor N M`, written `N ≤m M`, means that `N = M ／ C ＼ D` for some
  subset `C` and `D` of `M.E`.
* `Matroid.IsStrictMinor N M`, written `N <m M`, means that `N = M ／ C ＼ D`
  for some subsets `C` and `D` of `M.E` that are not both nonempty.
* `Matroid.IsMinor.exists_eq_contract_delete_disjoint` : we can choose `C` and `D` disjoint.

-/

namespace Matroid

open Set

section Minor

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I C D : Set α}

/-! ### Minors -/

/-- `N` is a minor of `M` if `N = M ／ C ＼ D` for some `C` and `D`.
The definition itself does not require `C` and `D` to be disjoint,
or even to be subsets of the ground set. See `Matroid.IsMinor.exists_eq_contract_delete_disjoint`
for the fact that we can choose `C` and `D` with these properties. -/
def IsMinor (N M : Matroid α) : Prop := ∃ C D, N = M ／ C ＼ D

/-- `≤m` denotes the minor relation on matroids. -/
infixl:50 " ≤m " => Matroid.IsMinor

@[simp]
lemma contract_delete_isMinor (M : Matroid α) (C D : Set α) : M ／ C ＼ D ≤m M :=
  ⟨C, D, rfl⟩

lemma IsMinor.exists_eq_contract_delete_disjoint (h : N ≤m M) :
    ∃ (C D : Set α), C ⊆ M.E ∧ D ⊆ M.E ∧ Disjoint C D ∧ N = M ／ C ＼ D := by
  obtain ⟨C, D, rfl⟩ := h
  exact ⟨C ∩ M.E, (D ∩ M.E) \ C, inter_subset_right, diff_subset.trans inter_subset_right,
    disjoint_sdiff_right.mono_left inter_subset_left,
    by simp [delete_eq_delete_iff, inter_assoc, inter_diff_assoc]⟩

/-- `N` is a strict minor of `M` if `N` is a minor of `M` and `N ≠ M`.
Equivalently, `N` is obtained from `M` by deleting/contracting subsets of the ground set
that are not both empty. -/
def IsStrictMinor (N M : Matroid α) : Prop := N ≤m M ∧ ¬ M ≤m N

/-- `<m` denotes the strict minor relation on matroids. -/
infixl:50 " <m " => Matroid.IsStrictMinor

lemma IsMinor.subset (h : N ≤m M) : N.E ⊆ M.E := by
  obtain ⟨C, D, rfl⟩ := h
  exact diff_subset.trans diff_subset

lemma IsMinor.refl {M : Matroid α} : M ≤m M := ⟨∅, ∅, by simp⟩

lemma IsMinor.trans {M₁ M₂ M₃ : Matroid α} (h : M₁ ≤m M₂) (h' : M₂ ≤m M₃) : M₁ ≤m M₃ := by
  obtain ⟨C₁, D₁, rfl⟩ := h
  obtain ⟨C₂, D₂, rfl⟩ := h'
  exact ⟨C₂ ∪ C₁ \ D₂, D₂ ∪ D₁, by rw [contract_delete_contract_delete']⟩

lemma IsMinor.eq_of_ground_subset (h : N ≤m M) (hE : M.E ⊆ N.E) : M = N := by
  obtain ⟨C, D, rfl⟩ := h
  rw [delete_ground, contract_ground, subset_diff, subset_diff] at hE
  rw [← contract_inter_ground_eq, hE.1.2.symm.inter_eq, contract_empty, ← delete_inter_ground_eq,
    hE.2.symm.inter_eq, delete_empty]

lemma IsMinor.antisymm (h : N ≤m M) (h' : M ≤m N) : N = M :=
  h'.eq_of_ground_subset h.subset

/-- The minor order is a `PartialOrder` on `Matroid α`.
We prefer the spelling `N ≤m M` over `N ≤ M` for the dot notation. -/
instance (α : Type*) : PartialOrder (Matroid α) where
  le N M := N ≤m M
  lt N M := N <m M
  le_refl _ := IsMinor.refl
  le_trans _ _ _ := IsMinor.trans
  le_antisymm _ _ := IsMinor.antisymm

lemma IsMinor.le (h : N ≤m M) : N ≤ M := h

lemma IsStrictMinor.lt (h : N <m M) : N < M := h

@[simp]
lemma le_eq_isMinor : (fun M M' : Matroid α ↦ M ≤ M') = Matroid.IsMinor := rfl

@[simp]
lemma lt_eq_isStrictMinor : (fun M M' : Matroid α ↦ M < M') = Matroid.IsStrictMinor := rfl

lemma isStrictMinor_iff_isMinor_ne : N <m M ↔ N ≤m M ∧ N ≠ M :=
  lt_iff_le_and_ne (α := Matroid α)

lemma IsStrictMinor.ne (h : N <m M) : N ≠ M :=
  h.lt.ne

lemma isStrictMinor_irrefl (M : Matroid α) : ¬ (M <m M) :=
  lt_irrefl M

lemma IsStrictMinor.isMinor (h : N <m M) : N ≤m M :=
  h.lt.le

lemma IsStrictMinor.not_isMinor (h : N <m M) : ¬ (M ≤m N) :=
  h.lt.not_ge

lemma IsStrictMinor.ssubset (h : N <m M) : N.E ⊂ M.E :=
  h.isMinor.subset.ssubset_of_ne (fun hE ↦ h.ne (h.isMinor.eq_of_ground_subset hE.symm.subset).symm)

lemma isStrictMinor_iff_isMinor_ssubset : N <m M ↔ N ≤m M ∧ N.E ⊂ M.E :=
  ⟨fun h ↦ ⟨h.isMinor, h.ssubset⟩, fun ⟨h, hss⟩ ↦ ⟨h, fun h' ↦ hss.ne <| by rw [h'.antisymm h]⟩⟩

lemma IsStrictMinor.trans_isMinor (h : N <m M) (h' : M ≤m M') : N <m M' :=
  h.lt.trans_le h'

lemma IsMinor.trans_isStrictMinor (h : N ≤m M) (h' : M <m M') : N <m M' :=
  h.le.trans_lt h'

lemma IsStrictMinor.trans (h : N <m M) (h' : M <m M') : N <m M' :=
  h.lt.trans h'

lemma Indep.of_isMinor (hI : N.Indep I) (hNM : N ≤m M) : M.Indep I := by
  obtain ⟨C, D, rfl⟩ := hNM
  exact hI.of_delete.of_contract

lemma IsNonloop.of_isMinor (h : N.IsNonloop e) (hNM : N ≤m M) : M.IsNonloop e := by
  obtain ⟨C, D, rfl⟩ := hNM
  exact h.of_delete.of_contract

lemma Dep.of_isMinor {D : Set α} (hD : M.Dep D) (hDN : D ⊆ N.E) (hNM : N ≤m M) : N.Dep D :=
  ⟨fun h ↦ hD.not_indep <| h.of_isMinor hNM, hDN⟩

lemma IsLoop.of_isMinor (he : M.IsLoop e) (heN : e ∈ N.E) (hNM : N ≤m M) : N.IsLoop e := by
  rw [← singleton_dep] at he ⊢
  exact he.of_isMinor (by simpa) hNM

end Minor

end Matroid
