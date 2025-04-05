/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Matroid.Loop
import Mathlib.Tactic.TautoSet

/-!
# Matroid Minors

For `M : Matroid α` and `X : Set α`, we can remove the elements of `X` from `M`
to obtain a matroid with ground set `M.E \ X` in two different  ways: 'deletion' and 'contraction'.
The *deletion* of `X` from `M`, denoted `M ＼ X`, is the matroid whose independent sets are the
independent sets of `M` that are disjoint from `X`. The *contraction* of `X` is the matroid `M ／ X`
in which a set `I` is independent if and only if `I ∪ J` is independent in `M`,
where `J` is an arbitrarily chosen basis for `X`.

We also have `M ＼ X = M ↾ (M.E \ X)` and (a little more cryptically) `M ／ X = (M✶ ＼ X)✶`.
We use these as the definitions, and prove that the independent sets are the same as those just
specified.

A matroid obtained from `M` by a sequence of deletions/contractions
(or equivalently, by a single deletion and a single contraction) is a *minor* of `M`.
This gives a partial order on `Matroid α` that is ubiquitous in matroid theory,
and interacts nicely with duality and linear representations.

# Main Declarations

* `Matroid.delete M D`, written `M ＼ D`, is the restriction of `M` to the set `M.E \ D`.
* `Matroid.contract M C`, written `M ／ C`, is the matroid on ground set `M.E \ C` in which a set
  `I ⊆ M.E \ C` is independent if and only if `I ∪ J` is independent in `M`,
  where `J` is an arbitrary basis for `C`.
* `Matroid.contract_dual M C : (M ／ X)✶ = M✶ ＼ X`; the dual of contraction is deletion.
* `Matroid.delete_dual M C : (M ＼ X)✶ = M✶ ／ X`; the dual of deletion is contraction.
* `Matroid.IsBasis.contract_indep_iff`; if `I` is a basis for `C`, then the independent
  sets of `M ／ C` are exactly the `J ⊆ M.E \ C` for which `I ∪ J` is independent in `M`.

# Naming conventions

We use the abbreviations `deleteElem` and `contractElem` in lemma names to refer to the
deletion `M ＼ {e}` or contraction `M ／ {e}` of a single element `e : α` from `M : Matroid α`.

-/

open Set

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I J R B X Y Z K S : Set α}

namespace Matroid

/-! ## Deletion -/

section Delete

variable {D D₁ D₂ R : Set α}

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

lemma delete_eq_delete_iff : M ＼ D₁ = M ＼ D₂ ↔ D₁ ∩ M.E = D₂ ∩ M.E := by
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
    M ＼ D₁ ＼ D₂ = M ＼ D₁ ＼ (D₂ \ D₁) :=
  by simp

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

lemma Coindep.delete_spanning_iff (hD : M.Coindep D) :
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

lemma isNonloop_iff_delete_of_not_mem (he : e ∉ D) : M.IsNonloop e ↔ (M ＼ D).IsNonloop e :=
  ⟨fun h ↦ delete_isNonloop_iff.2 ⟨h, he⟩, fun h ↦ h.of_delete⟩

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

/-! ## Contraction -/

section Contract

variable {C C₁ C₂ : Set α}

/-- The contraction `M ／ C` is the matroid on `M.E \ C` in which a set `I ⊆ M.E \ C` is independent
if and only if `I ∪ J` is independent, where `J` is an arbitrarily chosen basis for `C`.
It is also equal by definition to `(M✶ ＼ C)✶`; see `Matroid.IsBasis.contract_indep_iff` for
a proof that its independent sets are the claimed ones. -/
def contract (M : Matroid α) (C : Set α) : Matroid α := (M✶ ＼ C)✶

/-- `M ／ C` refers to the contraction of a set `C` from the matroid `M`. -/
infixl:75 " ／ " => Matroid.contract

@[simp] lemma contract_ground (M : Matroid α) (C : Set α) : (M ／ C).E = M.E \ C := rfl

lemma dual_delete_dual (M : Matroid α) (X : Set α) : (M✶ ＼ X)✶ = M ／ X := rfl

@[simp]
lemma dual_delete (M : Matroid α) (X : Set α) : (M ＼ X)✶ = M✶ ／ X := by
  rw [← dual_dual M, dual_delete_dual, dual_dual]

@[simp]
lemma dual_contract (M : Matroid α) (X : Set α) : (M ／ X)✶ = M✶ ＼ X := by
  rw [← dual_delete_dual, dual_dual]

lemma dual_contract_dual (M : Matroid α) (X : Set α) : (M✶ ／ X)✶ = M ＼ X := by
  simp

@[simp]
lemma contract_contract (M : Matroid α) (C₁ C₂ : Set α) : M ／ C₁ ／ C₂ = M ／ (C₁ ∪ C₂) := by
  simp [← dual_inj]

lemma contract_comm (M : Matroid α) (C₁ C₂ : Set α) : M ／ C₁ ／ C₂ = M ／ C₂ ／ C₁ := by
  simp [union_comm]

lemma dual_contract_delete (M : Matroid α) (X Y : Set α) : (M ／ X ＼ Y)✶ = M✶ ＼ X ／ Y := by
  simp

lemma dual_delete_contract (M : Matroid α) (X Y : Set α) : (M ＼ X ／ Y)✶ = M✶ ／ X ＼ Y := by
  simp

lemma contract_eq_self_iff : M ／ C = M ↔ Disjoint C M.E := by
  rw [← dual_delete_dual, ← dual_inj, dual_dual, delete_eq_self_iff, dual_ground]

lemma contractElem_eq_self (he : e ∉ M.E) : M ／ {e} = M := by
  rw [← dual_delete_dual, deleteElem_eq_self (by simpa), dual_dual]

@[simp] lemma contract_empty (M : Matroid α) : M ／ ∅ = M := by
  rw [← dual_delete_dual, delete_empty, dual_dual]

lemma contract_contract_eq_contract_diff (M : Matroid α) (C₁ C₂ : Set α) :
    M ／ C₁ ／ C₂ = M ／ C₁ ／ (C₂ \ C₁) := by
  simp

lemma contract_eq_contract_iff : M ／ C₁ = M ／ C₂ ↔ C₁ ∩ M.E = C₂ ∩ M.E := by
  rw [← dual_delete_dual, ← dual_delete_dual, dual_inj, delete_eq_delete_iff, dual_ground]

@[simp] lemma contract_inter_ground_eq (M : Matroid α) (C : Set α) : M ／ (C ∩ M.E) = M ／ C := by
  rw [← dual_delete_dual, (show M.E = M✶.E from rfl), delete_inter_ground_eq]
  rfl

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma contract_ground_subset_ground (M : Matroid α) (C : Set α) : (M ／ C).E ⊆ M.E :=
  (M.contract_ground C).trans_subset diff_subset

/-! ### Independence and Coindependence -/

lemma coindep_contract_iff : (M ／ C).Coindep X ↔ M.Coindep X ∧ Disjoint X C := by
  rw [coindep_def, dual_contract, delete_indep_iff, ← coindep_def]

lemma Coindep.coindep_contract_of_disjoint (hX : M.Coindep X) (hXC : Disjoint X C) :
    (M ／ C).Coindep X :=
  coindep_contract_iff.2 ⟨hX, hXC⟩

@[simp] lemma contract_isCocircuit_iff :
    (M ／ C).IsCocircuit K ↔ M.IsCocircuit K ∧ Disjoint K C := by
  rw [isCocircuit_def, dual_contract, delete_isCircuit_iff]

lemma Indep.contract_isBase_iff (hI : M.Indep I) :
    (M ／ I).IsBase B ↔ M.IsBase (B ∪ I) ∧ Disjoint B I := by
  rw [← dual_delete_dual, dual_isBase_iff', delete_ground, dual_ground, delete_isBase_iff,
    subset_diff, ← and_assoc, and_congr_left_iff, ← dual_dual M, dual_isBase_iff', dual_dual,
    dual_dual, union_comm, dual_ground, union_subset_iff, and_iff_right hI.subset_ground,
    and_congr_left_iff, ← isBase_restrict_iff, diff_diff, Spanning.isBase_restrict_iff,
    and_iff_left (diff_subset_diff_right subset_union_left)]
  · simp
  rwa [← dual_ground, ← coindep_iff_compl_spanning, dual_coindep_iff]

lemma Indep.contract_indep_iff (hI : M.Indep I) :
    (M ／ I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I) := by
  simp_rw [indep_iff, hI.contract_isBase_iff, union_subset_iff]
  exact ⟨fun ⟨B, ⟨hBI, hdj⟩, hJB⟩ ↦ ⟨disjoint_of_subset_left hJB hdj, _, hBI,
    hJB.trans subset_union_left, subset_union_right⟩,
    fun ⟨hdj, B, hB, hJB, hIB⟩ ↦ ⟨B \ I,⟨by simpa [union_eq_self_of_subset_right hIB],
      disjoint_sdiff_left⟩, subset_diff.2 ⟨hJB, hdj⟩ ⟩⟩

lemma IsNonloop.contractElem_indep_iff (he : M.IsNonloop e) :
    (M ／ {e}).Indep I ↔ e ∉ I ∧ M.Indep (insert e I) := by
  simp [he.indep.contract_indep_iff]

lemma Indep.union_indep_iff_contract_indep (hI : M.Indep I) :
    M.Indep (I ∪ J) ↔ (M ／ I).Indep (J \ I) := by
  rw [hI.contract_indep_iff, and_iff_right disjoint_sdiff_left, diff_union_self, union_comm]

lemma Indep.diff_indep_contract_of_subset (hJ : M.Indep J) (hIJ : I ⊆ J) :
    (M ／ I).Indep (J \ I) := by
  rwa [← (hJ.subset hIJ).union_indep_iff_contract_indep, union_eq_self_of_subset_left hIJ]

lemma Indep.contract_dep_iff (hI : M.Indep I) :
    (M ／ I).Dep J ↔ Disjoint J I ∧ M.Dep (J ∪ I) := by
  rw [dep_iff, hI.contract_indep_iff, dep_iff, contract_ground, subset_diff, disjoint_comm,
    union_subset_iff, and_iff_left hI.subset_ground]
  tauto

/-! ### Bases -/

/-- Contracting a set is the same as contracting a basis for the set, and deleting the rest. -/
lemma IsBasis.contract_eq_contract_delete (hI : M.IsBasis I X) : M ／ X = M ／ I ＼ (X \ I) := by
  nth_rw 1 [← diff_union_of_subset hI.subset, ← dual_inj, dual_contract_delete, dual_contract,
    union_comm, ← delete_delete, ext_iff_indep]
  refine ⟨rfl, fun J hJ ↦ ?_⟩
  have hss : X \ I ⊆ (M✶ ＼ I).coloops := fun e he ↦ by
    rw [← dual_contract, dual_coloops, ← IsLoop, ← singleton_dep, hI.indep.contract_dep_iff,
      singleton_union, and_iff_right (by simpa using he.2), hI.indep.insert_dep_iff,
      hI.closure_eq_closure]
    exact diff_subset_diff_left (M.subset_closure X) he
  rw [((coloops_indep _).subset hss).contract_indep_iff, delete_indep_iff,
    union_indep_iff_indep_of_subset_coloops hss, and_comm]

lemma Indep.union_isBasis_union_of_contract_isBasis (hI : M.Indep I) (hB : (M ／ I).IsBasis J X) :
    M.IsBasis (J ∪ I) (X ∪ I) := by
  simp_rw [IsBasis, hI.contract_indep_iff, contract_ground, subset_diff,
    maximal_subset_iff, and_imp] at hB
  refine hB.1.1.1.2.isBasis_of_maximal_subset (union_subset_union_left _ hB.1.1.2)
    fun K hK hKJ hKX ↦ ?_
  rw [union_subset_iff] at hKJ
  rw [hB.1.2 (t := K \ I) disjoint_sdiff_left (by simpa [diff_union_of_subset hKJ.2])
    (diff_subset_iff.2 (by rwa [union_comm])) (subset_diff.2 ⟨hKJ.1, hB.1.1.1.1⟩),
    diff_union_of_subset hKJ.2]

lemma IsBasis'.contract_isBasis'_diff_diff_of_subset (hIX : M.IsBasis' I X) (hJI : J ⊆ I) :
    (M ／ J).IsBasis' (I \ J) (X \ J) := by
  suffices ∀ ⦃K⦄, Disjoint K J → M.Indep (K ∪ J) → K ⊆ X → I ⊆ K ∪ J → K ⊆ I by
    simpa +contextual [IsBasis', (hIX.indep.subset hJI).contract_indep_iff,
      subset_diff, maximal_subset_iff, disjoint_sdiff_left,
      union_eq_self_of_subset_right hJI, hIX.indep, diff_subset.trans hIX.subset,
      diff_subset_iff, subset_antisymm_iff, union_comm J]
  exact fun K hJK hKJi hKX hIJK ↦ by
    simp [hIX.eq_of_subset_indep hKJi hIJK (union_subset hKX (hJI.trans hIX.subset))]

lemma IsBasis'.contract_isBasis'_diff_of_subset (hIX : M.IsBasis' I X) (hJI : J ⊆ I) :
    (M ／ J).IsBasis' (I \ J) X := by
  simpa [isBasis'_iff_isBasis_inter_ground, inter_diff_assoc, ← diff_inter_distrib_right] using
    (hIX.contract_isBasis'_diff_diff_of_subset hJI).isBasis_inter_ground

lemma IsBasis.contract_isBasis_diff_diff_of_subset (hIX : M.IsBasis I X) (hJI : J ⊆ I) :
    (M ／ J).IsBasis (I \ J) (X \ J) := by
  have h := (hIX.isBasis'.contract_isBasis'_diff_of_subset hJI).isBasis_inter_ground
  rwa [contract_ground, ← inter_diff_assoc, inter_eq_self_of_subset_left hIX.subset_ground] at h

lemma IsBasis.contract_diff_isBasis_diff (hIX : M.IsBasis I X) (hJY : M.IsBasis J Y) (hIJ : I ⊆ J) :
    (M ／ I).IsBasis (J \ I) (Y \ X) := by
  refine (hJY.contract_isBasis_diff_diff_of_subset hIJ).isBasis_subset ?_ ?_
  · rw [subset_diff, and_iff_right (diff_subset.trans hJY.subset),
      hIX.eq_of_subset_indep (hJY.indep.inter_right X) (subset_inter hIJ hIX.subset)
      inter_subset_right, diff_self_inter]
    exact disjoint_sdiff_left
  refine diff_subset_diff_right hIX.subset

lemma IsBasis'.contract_isBasis_union_union (h : M.IsBasis' (J ∪ I) (X ∪ I))
    (hJI : Disjoint J I) (hXI : Disjoint X I) : (M ／ I).IsBasis' J X := by
  simpa [hJI.sdiff_eq_left, hXI.sdiff_eq_left] using
    h.contract_isBasis'_diff_diff_of_subset subset_union_right

lemma IsBasis.contract_isBasis_union_union (h : M.IsBasis (J ∪ I) (X ∪ I))
    (hJI : Disjoint J I) (hXI : Disjoint X I) : (M ／ I).IsBasis J X := by
  refine (isBasis'_iff_isBasis ?_).1 <| h.isBasis'.contract_isBasis_union_union hJI hXI
  rw [contract_ground, subset_diff, and_iff_left hXI]
  exact subset_union_left.trans h.subset_ground

lemma IsBasis'.contract_eq_contract_delete (hI : M.IsBasis' I X) : M ／ X = M ／ I ＼ (X \ I) := by
  rw [← contract_inter_ground_eq, hI.isBasis_inter_ground.contract_eq_contract_delete, eq_comm,
    ← delete_inter_ground_eq, contract_ground, diff_eq, diff_eq, ← inter_inter_distrib_right,
    ← diff_eq]

lemma IsBasis'.contract_indep_iff (hI : M.IsBasis' I X) :
    (M ／ X).Indep J ↔ M.Indep (J ∪ I) ∧ Disjoint X J := by
  rw [hI.contract_eq_contract_delete, delete_indep_iff, hI.indep.contract_indep_iff,
    and_comm, ← and_assoc, ← disjoint_union_right, diff_union_self,
    union_eq_self_of_subset_right hI.subset, and_comm, disjoint_comm]

lemma IsBasis.contract_indep_iff (hI : M.IsBasis I X) :
    (M ／ X).Indep J ↔ M.Indep (J ∪ I) ∧ Disjoint X J :=
  hI.isBasis'.contract_indep_iff

lemma IsBasis'.contract_dep_iff (hI : M.IsBasis' I X) {D : Set α} :
    (M ／ X).Dep D ↔ M.Dep (D ∪ I) ∧ Disjoint X D := by
  rw [hI.contract_eq_contract_delete, delete_dep_iff, hI.indep.contract_dep_iff, and_comm,
    ← and_assoc, ← disjoint_union_right, diff_union_of_subset hI.subset, disjoint_comm, and_comm]

lemma IsBasis.contract_dep_iff (hI : M.IsBasis I X) {D : Set α} :
    (M ／ X).Dep D ↔ M.Dep (D ∪ I) ∧ Disjoint X D :=
  hI.isBasis'.contract_dep_iff

lemma IsBasis.contract_indep_iff_of_disjoint (hI : M.IsBasis I X) (hdj : Disjoint X J) :
    (M ／ X).Indep J ↔ M.Indep (J ∪ I) := by
  rw [hI.contract_indep_iff, and_iff_left hdj]

lemma IsBasis.contract_indep_diff_iff (hI : M.IsBasis I X) :
    (M ／ X).Indep (J \ X) ↔ M.Indep ((J \ X) ∪ I) := by
  rw [hI.contract_indep_iff, and_iff_left disjoint_sdiff_right]

lemma IsBasis'.contract_indep_diff_iff (hI : M.IsBasis' I X) :
    (M ／ X).Indep (J \ X) ↔ M.Indep ((J \ X) ∪ I) := by
  rw [hI.contract_indep_iff, and_iff_left disjoint_sdiff_right]

lemma IsBasis.contract_isBasis_of_isBasis' (h : M.IsBasis I X) (hJC : M.IsBasis' J C)
    (h_ind : M.Indep (I \ C ∪ J)) : (M ／ C).IsBasis (I \ C) (X \ C) := by
  have hIX := h.subset
  have hJCss := hJC.subset
  rw [hJC.contract_eq_contract_delete, delete_isBasis_iff]
  refine ⟨contract_isBasis_union_union (h_ind.isBasis_of_subset_of_subset_closure ?_ ?_) ?_ ?_, ?_⟩
  rotate_left
  · rw [closure_union_congr_right hJC.closure_eq_closure, diff_union_self,
      closure_union_congr_left h.closure_eq_closure]
    exact subset_closure_of_subset' _ (by tauto_set)
      (union_subset (diff_subset.trans h.subset_ground) hJC.indep.subset_ground)
  all_goals tauto_set

lemma IsBasis'.contract_isBasis' (h : M.IsBasis' I X) (hJC : M.IsBasis' J C)
    (h_ind : M.Indep (I \ C ∪ J)) : (M ／ C).IsBasis' (I \ C) (X \ C) := by
  rw [isBasis'_iff_isBasis_inter_ground, contract_ground, ← diff_inter_distrib_right]
  exact h.isBasis_inter_ground.contract_isBasis_of_isBasis' hJC h_ind

lemma IsBasis.contract_isBasis (h : M.IsBasis I X) (hJC : M.IsBasis J C)
    (h_ind : M.Indep (I \ C ∪ J)) : (M ／ C).IsBasis (I \ C) (X \ C) :=
  h.contract_isBasis_of_isBasis' hJC.isBasis' h_ind

lemma IsBasis.contract_isBasis_of_disjoint (h : M.IsBasis I X) (hJC : M.IsBasis J C)
    (hdj : Disjoint C X) (h_ind : M.Indep (I ∪ J)) : (M ／ C).IsBasis I X := by
  have h' := h.contract_isBasis hJC
  rwa [(hdj.mono_right h.subset).sdiff_eq_right, hdj.sdiff_eq_right, imp_iff_right h_ind] at h'

lemma IsBasis'.contract_isBasis_of_indep (h : M.IsBasis' I X) (h_ind : M.Indep (I ∪ J)) :
    (M ／ J).IsBasis' (I \ J) (X \ J) :=
  h.contract_isBasis' (h_ind.subset subset_union_right).isBasis_self.isBasis' (by simpa)

lemma IsBasis.contract_isBasis_of_indep (h : M.IsBasis I X) (h_ind : M.Indep (I ∪ J)) :
    (M ／ J).IsBasis (I \ J) (X \ J) :=
  h.contract_isBasis (h_ind.subset subset_union_right).isBasis_self (by simpa)

lemma IsBasis.contract_isBasis_of_disjoint_indep (h : M.IsBasis I X) (hdj : Disjoint J X)
    (h_ind : M.Indep (I ∪ J)) : (M ／ J).IsBasis I X := by
  rw [← hdj.sdiff_eq_right, ← (hdj.mono_right h.subset).sdiff_eq_right]
  exact h.contract_isBasis_of_indep h_ind

lemma Indep.of_contract (hI : (M ／ C).Indep I) : M.Indep I :=
  ((M.exists_isBasis' C).choose_spec.contract_indep_iff.1 hI).1.subset subset_union_left

lemma Dep.of_contract (h : (M ／ C).Dep X) (hC : C ⊆ M.E := by aesop_mat) : M.Dep (C ∪ X) := by
  rw [Dep, and_iff_left (union_subset hC (h.subset_ground.trans diff_subset))]
  intro hi
  rw [Dep, (hi.subset subset_union_left).contract_indep_iff, union_comm,
    and_iff_left hi] at h
  exact h.1 (subset_diff.1 h.2).2

end Contract

end Matroid
