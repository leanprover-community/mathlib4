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

section Delete

variable {D D₁ D₂ R : Set α}

/-- The deletion `M ＼ D` is the restriction of a matroid `M` to `M.E \ D`.
Its independent sets are the `M`-independent subsets of `M.E \ D`. -/
def delete (M : Matroid α) (D : Set α) : Matroid α := M ↾ (M.E \ D)

/-- `M ＼ D` refers to the deletion of a set `D` from the matroid `M`. -/
scoped infixl:75 " ＼ " => Matroid.delete

lemma delete_eq_restrict (M : Matroid α) (D : Set α) : M ＼ D = M ↾ (M.E \ D) := rfl

instance delete_finite [M.Finite] : (M ＼ D).Finite :=
  ⟨M.ground_finite.diff⟩

instance delete_rankFinite [RankFinite M] : RankFinite (M ＼ D) :=
  restrict_rankFinite _

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

lemma IsRestriction.restrict_delete_of_disjoint (h : N ≤r M) (hX : Disjoint X N.E) :
    N ≤r (M ＼ X) := by
  obtain ⟨D, hD, rfl⟩ := isRestriction_iff_exists_eq_delete.1 h
  refine isRestriction_iff_exists_eq_delete.2 ⟨D \ X, diff_subset_diff_left hD, ?_⟩
  rwa [delete_delete, union_diff_self, union_comm, ← delete_delete, eq_comm,
    delete_eq_self_iff]

lemma IsRestriction.isRestriction_deleteElem (h : N ≤r M) (he : e ∉ N.E) : N ≤r M ＼ {e} :=
  h.restrict_delete_of_disjoint (by simpa)

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

@[simp]
lemma delete_loops_eq (M : Matroid α) (D : Set α) : (M ＼ D).loops = M.loops \ D := by
  simp [loops]

lemma delete_isColoop_iff (M : Matroid α) (D : Set α) :
    (M ＼ D).IsColoop e ↔ e ∉ M.closure ((M.E \ D) \ {e}) ∧ e ∈ M.E ∧ e ∉ D := by
  rw [delete_eq_restrict, restrict_isColoop_iff diff_subset, mem_diff, and_congr_left_iff, and_imp]
  simp

@[simp]
lemma delete_empty (M : Matroid α) : M ＼ ∅ = M := by
  rw [delete_eq_self_iff]
  exact empty_disjoint _

lemma delete_delete_eq_delete_diff (M : Matroid α) (D₁ D₂ : Set α) :
    M ＼ D₁ ＼ D₂ = M ＼ D₁ ＼ (D₂ \ D₁) :=
  by simp

instance delete_finitary (M : Matroid α) [Finitary M] (D : Set α) : Finitary (M ＼ D) :=
  inferInstanceAs <| Finitary (M ↾ (M.E \ D))

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

end Delete

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

instance contract_finite [M.Finite] : (M ／ C).Finite := by
  rw [← dual_delete_dual]
  infer_instance

/-! ### Independence and Coindependence -/

section Indep

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

end Indep

/-! ### Loops and Coloops -/

-- lemma contract_eq_delete_of_subset_coloops (hX : X ⊆ M.coloops) : M ／ X = M ＼ X := by
--   refine ext_indep rfl fun I _ ↦ ?_
--   rw [(M.coloops_indep.subset hX).contract_indep_iff, delete_indep_iff, and_comm,
--     union_indep_iff_indep_of_subset_coloops hX]

-- lemma contract_eq_delete_of_subset_loops (hX : X ⊆ M.loops) : M ／ X = M ＼ X := by
--   rw [← dual_inj, dual_contract, dual_delete, eq_comm, contract_eq_delete_of_subset_coloops]
--   rwa [dual_coloops]

/-! ### Bases -/

section IsBasis

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

/-- Contracting a set is the same as contracting a basis for the set, and deleting the rest. -/
lemma IsBasis.contract_eq_contract_delete (hI : M.IsBasis I X) : M ／ X = M ／ I ＼ (X \ I) := by
  nth_rw 1 [← diff_union_of_subset hI.subset, ← dual_inj]
  -- rw [← dual_inj, dual_contract, dual_contract_delete]
  have hss : X \ I ⊆ (M ／ I)✶.coloops := sorry
  simp_rw [union_comm, ← contract_contract, dual_contract, dual_delete, ext_iff_indep,
    delete_ground, delete_indep_iff]
  refine ⟨rfl, fun J hJ ↦ ?_⟩

  rw [Indep.contract_indep_iff, dual_contract, delete_indep_iff]
  refine ext_indep rfl fun J hJ ↦ ?_
  rw [delete_indep_iff, hI.indep.contract_indep_iff]

  refine contract_eq_delete_of_subset_loops fun e he ↦ ?_
  rw [← isLoop_iff, ← singleton_dep, hI.indep.contract_dep_iff,
    disjoint_singleton_left, and_iff_right he.2, singleton_union,
    ← hI.indep.mem_closure_iff_of_not_mem he.2]
  exact hI.subset_closure he.1

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

end IsBasis

/-- Contracting the closure of a set is the same as contracting the set,
and then deleting the rest of its elements. -/
lemma contract_closure_eq_contract_delete (M : Matroid α) (C : Set α) :
    M ／ M.closure C = M ／ C ＼ (M.closure C \ C) := by
  wlog hCE : C ⊆ M.E with aux
  · rw [← M.contract_inter_ground_eq C, ← closure_inter_ground, aux _ _ inter_subset_right,
      diff_inter, diff_eq_empty.2 (M.closure_subset_ground _), union_empty]
  obtain ⟨I, hI⟩ := M.exists_isBasis C
  rw [hI.isBasis_closure_right.contract_eq_contract_delete, hI.contract_eq_contract_delete,
    delete_delete, union_comm, diff_union_diff_cancel (M.subset_closure C) hI.subset]

lemma exists_eq_contract_indep_delete (M : Matroid α) (C : Set α) :
    ∃ I D : Set α, M.IsBasis I (C ∩ M.E) ∧ D ⊆ (M ／ I).E ∧ D ⊆ C ∧ M ／ C = M ／ I ＼ D := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (C ∩ M.E)
  use I, C \ I ∩ M.E, hI
  rw [contract_ground, and_iff_right (inter_subset_left.trans diff_subset), diff_eq,
    diff_eq, inter_right_comm, inter_assoc, and_iff_right inter_subset_right,
    ← contract_inter_ground_eq, hI.contract_eq_contract_delete, diff_eq, inter_assoc]

lemma Indep.of_contract (hI : (M ／ C).Indep I) : M.Indep I :=
  ((M.exists_isBasis' C).choose_spec.contract_indep_iff.1 hI).1.subset subset_union_left

instance contract_rankFinite [RankFinite M] : RankFinite (M ／ C) :=
  let ⟨B, hB⟩ := (M ／ C).exists_isBase
  ⟨B, hB, hB.indep.of_contract.finite⟩

instance contract_finitary [Finitary M] : Finitary (M ／ C) := by
  obtain ⟨J, hJ⟩ := M.exists_isBasis' C
  suffices h : (M ／ J).Finitary by
    rw [hJ.contract_eq_contract_delete]
    infer_instance
  exact ⟨fun I hI ↦ hJ.indep.contract_indep_iff.2  ⟨disjoint_left.2 fun e heI ↦
    ((hI {e} (by simpa) (by simp)).subset_ground rfl).2,
    indep_of_forall_finite_subset_indep _ fun K hK hKfin ↦
      (hJ.indep.contract_indep_iff.1 <| hI (K ∩ I)
      inter_subset_right (hKfin.inter_of_left _)).2.subset (by tauto_set)⟩⟩

@[simp]
lemma contract_isLoop_iff_mem_closure : (M ／ C).IsLoop e ↔ e ∈ M.closure C ∧ e ∉ C := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' C
  rw [hI.contract_eq_contract_delete, delete_isLoop_iff, ← singleton_dep,
    hI.indep.contract_dep_iff, singleton_union, hI.indep.insert_dep_iff, hI.closure_eq_closure]
  by_cases heI : e ∈ I
  · simp [heI, hI.subset heI]
  simp [heI, and_comm]

@[simp]
lemma contract_loops_eq (M : Matroid α) (C : Set α) : (M ／ C).loops = M.closure C \ C := by
  simp [Set.ext_iff, ← isLoop_iff, contract_isLoop_iff_mem_closure]

@[simp]
lemma contract_coloops_eq (M : Matroid α) (C : Set α) : (M ／ C).coloops = M.coloops \ C := by
  rw [← dual_delete_dual, dual_coloops, delete_loops_eq, dual_loops]

@[simp]
lemma contract_isColoop_iff : (M ／ C).IsColoop e ↔ M.IsColoop e ∧ e ∉ C := by
  simp [isColoop_iff_mem_coloops]

@[simp]
lemma contract_closure_eq (M : Matroid α) (C X : Set α) :
    (M ／ C).closure X = M.closure (X ∪ C) \ C := by
  rw [← diff_union_inter (M.closure (X ∪ C) \ C) X, diff_diff, union_comm C, ← contract_loops_eq,
    union_comm X, ← contract_contract, contract_loops_eq, subset_antisymm_iff, union_subset_iff,
    and_iff_right diff_subset, ← diff_subset_iff]
  simp only [sdiff_sdiff_right_self, inf_eq_inter, subset_inter_iff, inter_subset_right, and_true]
  refine ⟨fun e ⟨he, he'⟩ ↦ ⟨mem_closure_of_mem' _ (.inr he') (mem_ground_of_mem_closure he).1,
    (closure_subset_ground _ _ he).2⟩, fun e ⟨⟨he, heC⟩, he'⟩ ↦
    mem_closure_of_mem' _ he' ⟨M.closure_subset_ground _ he, heC⟩⟩

lemma IsCircuit.contract_isCircuit (hK : M.IsCircuit K) (hC : C ⊂ K) :
    (M ／ C).IsCircuit (K \ C) := by
  suffices ∀ e ∈ K, e ∉ C → M.Indep (K \ {e} ∪ C) by
    simpa [isCircuit_iff_dep_forall_diff_singleton_indep, diff_diff_comm (s := K) (t := C),
    dep_iff, (hK.ssubset_indep hC).contract_indep_iff, diff_subset_diff_left hK.subset_ground,
    disjoint_sdiff_left, diff_union_of_subset hC.subset, hK.not_indep]
  exact fun e heK heC ↦ (hK.diff_singleton_indep heK).subset <| by
    simp [subset_diff_singleton hC.subset heC]

lemma IsCircuit.contractElem_isCircuit (hC : M.IsCircuit C) (hnt : C.Nontrivial) (heC : e ∈ C) :
    (M ／ {e}).IsCircuit (C \ {e}) :=
  hC.contract_isCircuit (ssubset_of_ne_of_subset hnt.ne_singleton.symm (by simpa))

lemma IsCircuit.contract_dep (hK : M.IsCircuit K) (hCK : Disjoint C K) : (M ／ C).Dep K := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (C ∩ M.E)
  rw [← contract_inter_ground_eq, Dep, hI.contract_indep_iff,
    and_iff_left (hCK.mono_left inter_subset_left), contract_ground, subset_diff,
    and_iff_left (hCK.symm.mono_right inter_subset_left), and_iff_left hK.subset_ground]
  exact fun hi ↦ hK.dep.not_indep (hi.subset subset_union_left)

lemma IsCircuit.contract_dep_of_not_subset (hK : M.IsCircuit K) {C : Set α} (hKC : ¬ K ⊆ C) :
    (M ／ C).Dep (K \ C) := by
  have h' := hK.contract_isCircuit (C := C ∩ K) (inter_subset_right.ssubset_of_ne (by simpa))
  simp only [diff_inter_self_eq_diff] at h'
  have hwin := h'.contract_dep (C := C \ K) disjoint_sdiff_sdiff
  rwa [contract_contract, inter_union_diff] at hwin

lemma IsCircuit.contract_diff_isCircuit (hC : M.IsCircuit C) (hK : K.Nonempty) (hKC : K ⊆ C) :
    (M ／ (C \ K)).IsCircuit K := by
  simpa [inter_eq_self_of_subset_right hKC] using hC.contract_isCircuit (C := C \ K) <|
    by rwa [diff_ssubset_left_iff, inter_eq_self_of_subset_right hKC]

/-- If `C` is a circuit of `M ／ K`, then `M` has a circuit in the interval `[C, C ∪ K]`. -/
lemma IsCircuit.exists_subset_isCircuit_of_contract (hC : (M ／ K).IsCircuit C) :
    ∃ C', M.IsCircuit C' ∧ C ⊆ C' ∧ C' ⊆ C ∪ K := by
  wlog hKi : M.Indep K generalizing K with aux
  · obtain ⟨I, hI⟩ := M.exists_isBasis' K
    rw [hI.contract_eq_contract_delete, delete_isCircuit_iff] at hC
    obtain ⟨C', hC', hCC', hC'ss⟩ := aux hC.1 hI.indep
    exact ⟨C', hC', hCC', hC'ss.trans (union_subset_union_right _ hI.subset)⟩
  obtain ⟨hCE : C ⊆ M.E, hCK : Disjoint C K⟩ := subset_diff.1 hC.subset_ground
  obtain ⟨C', hC'ss, hC'⟩ := (hKi.contract_dep_iff.1 hC.dep).2.exists_isCircuit_subset
  refine ⟨C', hC', ?_, hC'ss⟩
  have hdep2 : (M ／ K).Dep (C' \ K) := by
    rw [hKi.contract_dep_iff, and_iff_right disjoint_sdiff_left]
    refine hC'.dep.superset (by simp)
  rw [← (hC.eq_of_dep_subset hdep2 (diff_subset_iff.2 (union_comm _ _ ▸ hC'ss)))]
  exact diff_subset

lemma Dep.of_contract (h : (M ／ C).Dep X) (hC : C ⊆ M.E := by aesop_mat) : M.Dep (C ∪ X) := by
  rw [Dep, and_iff_left (union_subset hC (h.subset_ground.trans diff_subset))]
  intro hi
  rw [Dep, (hi.subset subset_union_left).contract_indep_iff, union_comm,
    and_iff_left hi] at h
  exact h.1 (subset_diff.1 h.2).2

lemma IsBasis.diff_subset_loops_contract (hIX : M.IsBasis I X) : X \ I ⊆ (M ／ I).loops := by
  rw [diff_subset_iff, contract_loops_eq, union_diff_self,
    union_eq_self_of_subset_left (M.subset_closure I)]
  exact hIX.subset_closure

lemma contract_spanning_iff (hC : C ⊆ M.E := by aesop_mat) :
    (M ／ C).Spanning X ↔ M.Spanning (X ∪ C) ∧ Disjoint X C := by
  rw [spanning_iff, contract_closure_eq, contract_ground, spanning_iff, union_subset_iff,
    subset_diff, ← and_assoc, and_congr_left_iff, and_comm (a := X ⊆ _), ← and_assoc,
    and_congr_left_iff]
  refine fun hdj hX ↦ ⟨fun h ↦ ⟨?_, hC⟩, fun h ↦ by simp [h]⟩
  rwa [← union_diff_cancel (M.subset_closure_of_subset' subset_union_right hC), h,
    union_diff_cancel]

/-- A version of `Matroid.contract_spanning_iff` without the supportedness hypothesis. -/
lemma contract_spanning_iff' :(M ／ C).Spanning X ↔ M.Spanning (X ∪ (C ∩ M.E)) ∧ Disjoint X C := by
  rw [← contract_inter_ground_eq, contract_spanning_iff, and_congr_right_iff]
  refine fun h ↦ ⟨fun hdj ↦ ?_, Disjoint.mono_right inter_subset_left⟩
  rw [← diff_union_inter C M.E, disjoint_union_right, and_iff_left hdj]
  exact disjoint_sdiff_right.mono_left (subset_union_left.trans h.subset_ground)

lemma Spanning.contract (hX : M.Spanning X) (C : Set α) : (M ／ C).Spanning (X \ C) := by
  have hXE := hX.subset_ground
  rw [contract_spanning_iff', and_iff_left disjoint_sdiff_left]
  exact hX.superset (by tauto_set) (by tauto_set)

lemma Spanning.contract_eq_loopyOn (hX : M.Spanning X) : M ／ X = loopyOn (M.E \ X) := by
  rw [eq_loopyOn_iff_loops_eq]
  simp [hX.closure_eq]

lemma IsNonloop.of_contract (h : (M ／ C).IsNonloop e) : M.IsNonloop e := by
  rw [← indep_singleton] at h ⊢
  exact h.of_contract

@[simp]
lemma contract_isNonloop_iff : (M ／ C).IsNonloop e ↔ e ∈ M.E \ M.closure C := by
  rw [isNonloop_iff_mem_compl_loops, contract_ground, contract_loops_eq]
  refine ⟨fun ⟨he,heC⟩ ↦ ⟨he.1, fun h ↦ heC ⟨h, he.2⟩⟩,
    fun h ↦ ⟨⟨h.1, fun heC ↦ h.2 ?_⟩, fun h' ↦ h.2 h'.1⟩⟩
  rw [← closure_inter_ground]
  exact (M.subset_closure (C ∩ M.E)) ⟨heC, h.1⟩

lemma IsCocircuit.of_contract (hK : (M ／ C).IsCocircuit K) : M.IsCocircuit K := by
  rw [isCocircuit_def, dual_contract] at hK
  exact hK.of_delete

lemma IsCocircuit.delete_isCocircuit {D : Set α} (hK : M.IsCocircuit K) (hD : D ⊂ K) :
    (M ＼ D).IsCocircuit (K \ D) := by
  rw [isCocircuit_def, dual_delete]
  exact hK.isCircuit.contract_isCircuit hD

lemma IsCocircuit.delete_diff_isCocircuit {X : Set α} (hK : M.IsCocircuit K) (hXK : X ⊆ K)
    (hX : X.Nonempty) : (M ＼ (K \ X)).IsCocircuit X := by
  rw [isCocircuit_def, dual_delete]
  exact hK.isCircuit.contract_diff_isCircuit hX hXK

end Contract

end Matroid
