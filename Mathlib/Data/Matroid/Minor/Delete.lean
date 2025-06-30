/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Matroid.Loop

/-!
# Matroid Deletion

For `M : Matroid α` and `X : Set α`, the *deletion* of `X` from `M` is the matroid `M ＼ X`
with ground set `M.E \ X`, in which a subset of `M.E \ X` is independent if and only if it is
independent in `M`.

The deletion `M ＼ X` is equal to the restriction `M ↾ (M.E \ X)`, but is of special importance
in the theory because it is the dual notion of *contraction*, and thus plays a more central
and natural role than restriction in many contexts.

Because of the implementation of the restriction `M ↾ R` allowing `R` to not be a subset of `M.E`,
the relation `M ↾ R ≤r M` holds only with the assumption `R ⊆ M.E`,
whereas `M ＼ D`, being defined as `M ↾ (M.E \ D)`, satisfies `M ＼ D ≤r M` unconditionally.
This is often quite convenient.

# Main Declarations

* `Matroid.delete M D`, written `M ＼ D`, is the restriction of `M` to the set `M.E \ D`,
  or equivalently the matroid on `M.E \ D` whose independent sets are the `M`-independent sets.

# Naming conventions

We use the abbreviation `deleteElem` in lemma names to refer to the deletion `M ＼ {e}`
of a single element `e : α` from `M : Matroid α`.
-/

open Set

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I B D R X : Set α}

namespace Matroid

/-! ## Deletion -/

section Delete

/-- The deletion `M ＼ D` is the restriction of a matroid `M` to `M.E \ D`.
Its independent sets are the `M`-independent subsets of `M.E \ D`. -/
def delete (M : Matroid α) (D : Set α) : Matroid α := M ↾ (M.E \ D)

/-- `M ＼ D` refers to the deletion of a set `D` from the matroid `M`. -/
scoped infixl:75 " ＼ " => Matroid.delete

lemma delete_eq_restrict (M : Matroid α) (D : Set α) : M ＼ D = M ↾ (M.E \ D) := rfl

lemma restrict_compl (M : Matroid α) (D : Set α) : M ↾ (M.E \ D) = M ＼ D := rfl

@[simp]
lemma delete_compl (hR : R ⊆ M.E := by aesop_mat) : M ＼ (M.E \ R) = M ↾ R := by
  rw [← restrict_compl, diff_diff_cancel_left hR]

@[simp]
lemma delete_isRestriction (M : Matroid α) (D : Set α) : M ＼ D ≤r M :=
  restrict_isRestriction _ _ diff_subset

lemma IsRestriction.exists_eq_delete (hNM : N ≤r M) : ∃ D ⊆ M.E, N = M ＼ D :=
  ⟨M.E \ N.E, diff_subset, by obtain ⟨R, hR, rfl⟩ := hNM; rw [delete_compl, restrict_ground_eq]⟩

lemma isRestriction_iff_exists_eq_delete : N ≤r M ↔ ∃ D ⊆ M.E, N = M ＼ D :=
  ⟨IsRestriction.exists_eq_delete, by rintro ⟨D, -, rfl⟩; apply delete_isRestriction⟩

@[simp]
lemma delete_ground (M : Matroid α) (D : Set α) : (M ＼ D).E = M.E \ D := rfl

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma delete_subset_ground (M : Matroid α) (D : Set α) : (M ＼ D).E ⊆ M.E :=
  diff_subset

@[simp]
lemma delete_eq_self_iff : M ＼ D = M ↔ Disjoint D M.E := by
  rw [← restrict_compl, restrict_eq_self_iff, sdiff_eq_left, disjoint_comm]

alias ⟨_, delete_eq_self⟩ := delete_eq_self_iff

lemma deleteElem_eq_self (he : e ∉ M.E) : M ＼ {e} = M := by
  simpa

@[simp]
lemma delete_delete (M : Matroid α) (D₁ D₂ : Set α) : M ＼ D₁ ＼ D₂ = M ＼ (D₁ ∪ D₂) := by
  rw [← restrict_compl, ← restrict_compl, ← restrict_compl, restrict_restrict_eq,
    restrict_ground_eq, diff_diff]
  simp [diff_subset]

lemma delete_comm (M : Matroid α) (D₁ D₂ : Set α) : M ＼ D₁ ＼ D₂ = M ＼ D₂ ＼ D₁ := by
  rw [delete_delete, union_comm, delete_delete]

lemma delete_inter_ground_eq (M : Matroid α) (D : Set α) : M ＼ (D ∩ M.E) = M ＼ D := by
  rw [← restrict_compl, ← restrict_compl, diff_inter_self_eq_diff]

lemma delete_eq_delete_iff {D₁ D₂ : Set α} : M ＼ D₁ = M ＼ D₂ ↔ D₁ ∩ M.E = D₂ ∩ M.E := by
  rw [← delete_inter_ground_eq, ← M.delete_inter_ground_eq D₂]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  apply_fun (M.E \ Matroid.E ·) at h
  simp_rw [delete_ground, diff_diff_cancel_left inter_subset_right] at h
  assumption

@[simp]
lemma delete_empty (M : Matroid α) : M ＼ ∅ = M := by
  rw [delete_eq_self_iff]
  exact empty_disjoint _

lemma delete_delete_eq_delete_diff (M : Matroid α) (D₁ D₂ : Set α) :
    M ＼ D₁ ＼ D₂ = M ＼ D₁ ＼ (D₂ \ D₁) := by
  simp

lemma IsRestriction.restrict_delete_of_disjoint (h : N ≤r M) (hX : Disjoint X N.E) :
    N ≤r (M ＼ X) := by
  obtain ⟨D, hD, rfl⟩ := isRestriction_iff_exists_eq_delete.1 h
  refine isRestriction_iff_exists_eq_delete.2 ⟨D \ X, diff_subset_diff_left hD, ?_⟩
  rwa [delete_delete, union_diff_self, union_comm, ← delete_delete, eq_comm,
    delete_eq_self_iff]

lemma IsRestriction.isRestriction_deleteElem (h : N ≤r M) (he : e ∉ N.E) : N ≤r M ＼ {e} :=
  h.restrict_delete_of_disjoint (by simpa)

/-! ### Independence and Bases -/

@[simp]
lemma delete_indep_iff : (M ＼ D).Indep I ↔ M.Indep I ∧ Disjoint I D := by
  rw [← restrict_compl, restrict_indep_iff, subset_diff, ← and_assoc,
    and_iff_left_of_imp Indep.subset_ground]

lemma deleteElem_indep_iff : (M ＼ {e}).Indep I ↔ M.Indep I ∧ e ∉ I := by
  simp

lemma Indep.of_delete (h : (M ＼ D).Indep I) : M.Indep I :=
  (delete_indep_iff.mp h).1

lemma Indep.indep_delete_of_disjoint (h : M.Indep I) (hID : Disjoint I D) : (M ＼ D).Indep I :=
  delete_indep_iff.mpr ⟨h, hID⟩

lemma indep_iff_delete_of_disjoint (hID : Disjoint I D) : M.Indep I ↔ (M ＼ D).Indep I :=
  ⟨fun h ↦ h.indep_delete_of_disjoint hID, fun h ↦ h.of_delete⟩

@[simp]
lemma delete_dep_iff : (M ＼ D).Dep X ↔ M.Dep X ∧ Disjoint X D := by
  rw [dep_iff, dep_iff, delete_indep_iff, delete_ground, subset_diff]; tauto

@[simp]
lemma delete_isBase_iff : (M ＼ D).IsBase B ↔ M.IsBasis B (M.E \ D) := by
  rw [← restrict_compl, isBase_restrict_iff]

@[simp]
lemma delete_isBasis_iff : (M ＼ D).IsBasis I X ↔ M.IsBasis I X ∧ Disjoint X D := by
  rw [← restrict_compl, isBasis_restrict_iff, subset_diff, ← and_assoc,
    and_iff_left_of_imp IsBasis.subset_ground]

@[simp]
lemma delete_isBasis'_iff : (M ＼ D).IsBasis' I X ↔ M.IsBasis' I (X \ D) := by
  rw [isBasis'_iff_isBasis_inter_ground, delete_isBasis_iff, delete_ground, diff_eq, inter_comm M.E,
    ← inter_assoc, ← diff_eq, ← isBasis'_iff_isBasis_inter_ground, and_iff_left_iff_imp,
    inter_comm, ← inter_diff_assoc]
  exact fun _ ↦ disjoint_sdiff_left

lemma IsBasis.of_delete (h : (M ＼ D).IsBasis I X) : M.IsBasis I X :=
  (delete_isBasis_iff.mp h).1

lemma IsBasis.delete (h : M.IsBasis I X) (hX : Disjoint X D) : (M ＼ D).IsBasis I X := by
  rw [delete_isBasis_iff]; exact ⟨h, hX⟩

lemma Coindep.delete_isBase_iff (hD : M.Coindep D) :
    (M ＼ D).IsBase B ↔ M.IsBase B ∧ Disjoint B D := by
  rw [Matroid.delete_isBase_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hss := h.subset
    rw [subset_diff] at hss
    have hcl := h.isBasis_closure_right
    rw [hD.closure_compl, isBasis_ground_iff] at hcl
    exact ⟨hcl, hss.2⟩
  exact h.1.isBasis_ground.isBasis_subset (by simp [subset_diff, h.1.subset_ground, h.2])
    diff_subset

lemma Coindep.delete_rankPos [M.RankPos] (hD : M.Coindep D) : (M ＼ D).RankPos := by
  rw [rankPos_iff, hD.delete_isBase_iff]
  simp [M.empty_not_isBase]

lemma Coindep.delete_spanning_iff {S : Set α} (hD : M.Coindep D) :
    (M ＼ D).Spanning S ↔ M.Spanning S ∧ Disjoint S D := by
  simp only [spanning_iff_exists_isBase_subset', hD.delete_isBase_iff, and_assoc, delete_ground,
    subset_diff, and_congr_left_iff, and_imp]
  refine fun hSE hSD ↦ ⟨fun ⟨B, hB, hBD, hBS⟩ ↦ ⟨B, hB, hBS⟩, fun ⟨B, hB, hBS⟩ ↦ ⟨B, hB, ?_, hBS⟩⟩
  exact hSD.mono_left hBS

/-! ### Loops, circuits and closure -/

@[simp]
lemma delete_isLoop_iff : (M ＼ D).IsLoop e ↔ M.IsLoop e ∧ e ∉ D := by
  rw [← singleton_dep, delete_dep_iff, disjoint_singleton_left, singleton_dep]

@[simp]
lemma delete_isNonloop_iff : (M ＼ D).IsNonloop e ↔ M.IsNonloop e ∧ e ∉ D := by
  rw [← indep_singleton, delete_indep_iff, disjoint_singleton_left, indep_singleton]

lemma IsNonloop.of_delete (h : (M ＼ D).IsNonloop e) : M.IsNonloop e :=
  (delete_isNonloop_iff.1 h).1

lemma isNonloop_iff_delete_of_notMem (he : e ∉ D) : M.IsNonloop e ↔ (M ＼ D).IsNonloop e :=
  ⟨fun h ↦ delete_isNonloop_iff.2 ⟨h, he⟩, fun h ↦ h.of_delete⟩

@[deprecated (since := "2025-05-23")]
alias isNonloop_iff_delete_of_not_mem := isNonloop_iff_delete_of_notMem

lemma delete_loops_eq_removeLoops (M : Matroid α) : M ＼ M.loops = M.removeLoops := by
  rw [removeLoops, delete_eq_restrict, compl_loops_eq]

@[simp]
lemma delete_isCircuit_iff {C : Set α} :
    (M ＼ D).IsCircuit C ↔ M.IsCircuit C ∧ Disjoint C D := by
  rw [delete_eq_restrict, restrict_isCircuit_iff, and_congr_right_iff, subset_diff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ h.subset_ground

lemma IsCircuit.of_delete {C : Set α} (h : (M ＼ D).IsCircuit C) : M.IsCircuit C :=
  (delete_isCircuit_iff.1 h).1

lemma circuit_iff_delete_of_disjoint {C : Set α} (hCD : Disjoint C D) :
    M.IsCircuit C ↔ (M ＼ D).IsCircuit C :=
  ⟨fun h ↦ delete_isCircuit_iff.2 ⟨h, hCD⟩, fun h ↦ h.of_delete⟩

@[simp]
lemma delete_closure_eq (M : Matroid α) (D X : Set α) :
    (M ＼ D).closure X = M.closure (X \ D) \ D := by
  rw [← restrict_compl, restrict_closure_eq', sdiff_sdiff_self, bot_eq_empty, union_empty,
    diff_eq, inter_comm M.E, ← inter_assoc X, ← diff_eq, closure_inter_ground,
    ← inter_assoc, ← diff_eq, inter_eq_left]
  exact diff_subset.trans (M.closure_subset_ground _)

lemma delete_closure_eq_of_disjoint (M : Matroid α) {D X : Set α} (hXD : Disjoint X D) :
    (M ＼ D).closure X = M.closure X \ D := by
  rw [delete_closure_eq, hXD.sdiff_eq_left]

@[simp]
lemma delete_loops_eq (M : Matroid α) (D : Set α) : (M ＼ D).loops = M.loops \ D := by
  simp [loops]

lemma delete_isColoop_iff (M : Matroid α) (D : Set α) :
    (M ＼ D).IsColoop e ↔ e ∉ M.closure ((M.E \ D) \ {e}) ∧ e ∈ M.E ∧ e ∉ D := by
  rw [delete_eq_restrict, restrict_isColoop_iff diff_subset, mem_diff, and_congr_left_iff, and_imp]
  simp

/-! ### Finiteness -/

instance delete_finitary (M : Matroid α) [Finitary M] (D : Set α) : Finitary (M ＼ D) :=
  inferInstanceAs <| Finitary (M ↾ (M.E \ D))

instance delete_finite [M.Finite] : (M ＼ D).Finite :=
  ⟨M.ground_finite.diff⟩

instance delete_rankFinite [RankFinite M] : RankFinite (M ＼ D) :=
  restrict_rankFinite _

end Delete

end Matroid
