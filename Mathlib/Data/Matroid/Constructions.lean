/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Matroid.Restrict

/-!
# Some constructions of matroids
This file defines some very elementary examples of matroids, namely those with at most one base.

## Main definitions

* `emptyOn α` is the matroid on `α` with empty ground set.

For `E : Set α`, ...

* `loopyOn E` is the matroid on `E` whose elements are all loops, or equivalently in which `∅`
  is the only base.
* `freeOn E` is the 'free matroid' whose ground set `E` is the only base.
* For `I ⊆ E`, `uniqueBaseOn I E` is the matroid with ground set `E` in which `I` is the only base.

## Implementation details

To avoid the tedious process of certifying the matroid axioms for each of these easy examples,
we bootstrap the definitions starting with `emptyOn α` (which `simp` can prove is a matroid)
and then construct the other examples using duality and restriction.

-/

variable {α : Type*} {M : Matroid α} {E B I X R J : Set α}

namespace Matroid

open Set

section EmptyOn

/-- The `Matroid α` with empty ground set-/
def emptyOn (α : Type*) : Matroid α :=
  Matroid.ofBaseOfFinite finite_empty (· = ∅) ⟨_, rfl⟩ (by rintro _ _ rfl; simp) (by simp)

@[simp] theorem emptyOn_ground : (emptyOn α).E = ∅ := rfl

@[simp] theorem emptyOn_base_iff : (emptyOn α).Base B ↔ B = ∅ := by
  simp [emptyOn]

@[simp] theorem emptyOn_indep_iff : (emptyOn α).Indep B ↔ B = ∅ := by
  simp [indep_iff_subset_base, subset_empty_iff]

@[simp] theorem ground_eq_empty_iff : (M.E = ∅) ↔ M = emptyOn α := by
  refine' ⟨fun h ↦ eq_of_base_iff_base_forall (by simp [h]) _, fun h ↦ by simp [h]⟩
  simp only [h, subset_empty_iff, emptyOn_base_iff, forall_eq, iff_true]
  obtain ⟨B', hB'⟩ := M.exists_base
  rwa [← eq_empty_of_subset_empty (hB'.subset_ground.trans_eq h)]

@[simp] theorem emptyOn_dual_eq : (emptyOn α)﹡ = emptyOn α := by
  rw [← ground_eq_empty_iff]; rfl

@[simp] theorem restrict_to_empty (M : Matroid α) : M ↾ (∅ : Set α) = emptyOn α := by
  simp [← ground_eq_empty_iff]

theorem eq_emptyOn_or_nonempty (M : Matroid α) : M = emptyOn α ∨ Matroid.Nonempty M := by
  rw [← ground_eq_empty_iff]
  exact M.E.eq_empty_or_nonempty.elim Or.inl (fun h ↦ Or.inr ⟨h⟩)

theorem ground_nonempty_iff (M : Matroid α) : M.E.Nonempty ↔ M.Nonempty :=
  ⟨fun h ↦ ⟨h⟩, fun ⟨h⟩ ↦ h⟩

theorem eq_emptyOn [IsEmpty α] (M : Matroid α) : M = emptyOn α := by
  rw [← ground_eq_empty_iff]
  exact M.E.eq_empty_of_isEmpty

instance finite_emptyOn (α : Type*) : (emptyOn α).Finite :=
  ⟨finite_empty⟩

end EmptyOn

section LoopyOn

/-- The `Matroid α` with ground set `E` whose only base is `∅` -/
def loopyOn (E : Set α) : Matroid α := (emptyOn α ↾ E)

@[simp] theorem loopyOn_ground (E : Set α) : (loopyOn E).E = E := rfl

@[simp] theorem loopyOn_empty (α : Type*) : loopyOn (∅ : Set α) = emptyOn α := by
  rw [← ground_eq_empty_iff, loopyOn_ground]

@[simp] theorem loopyOn_indep_iff : (loopyOn E).Indep I ↔ I = ∅ := by
  simp only [loopyOn, restrict_indep_iff, emptyOn_indep_iff, and_iff_left_iff_imp]
  rintro rfl; apply empty_subset

@[simp] theorem eq_loopyOn_iff : (M = loopyOn E) ↔ M.E = E ∧ ∀ X ⊆ M.E, M.Indep X → X = ∅ := by
  simp_rw [eq_iff_indep_iff_indep_forall]
  simp only [loopyOn_ground, loopyOn_indep_iff, and_congr_right_iff]
  rintro rfl
  refine ⟨fun h I hI ↦ (h I hI).1, fun h I hIE ↦ ⟨h I hIE, by rintro rfl; simp⟩⟩

@[simp] theorem loopyOn_base_iff : (loopyOn E).Base B ↔ B = ∅ := by
  simp only [base_iff_maximal_indep, loopyOn_indep_iff, forall_eq, and_iff_left_iff_imp]
  exact fun h _ ↦ h

@[simp] theorem loopyOn_basis_iff : (loopyOn E).Basis I X ↔ I = ∅ ∧ X ⊆ E :=
  ⟨fun h ↦⟨loopyOn_indep_iff.mp h.indep, h.subset_ground⟩,
    by rintro ⟨rfl, hX⟩; rw [basis_iff]; simp⟩

instance : FiniteRk (loopyOn E) :=
  ⟨⟨∅, loopyOn_base_iff.2 rfl, finite_empty⟩⟩

theorem Finite.loopyOn_finite (hE : E.Finite) : Matroid.Finite (loopyOn E) :=
  ⟨hE⟩

@[simp] theorem loopyOn_restrict (E R : Set α) : (loopyOn E) ↾ R = loopyOn R := by
  refine eq_of_indep_iff_indep_forall rfl ?_
  simp only [restrict_ground_eq, restrict_indep_iff, loopyOn_indep_iff, and_iff_left_iff_imp]
  exact fun _ h _ ↦ h

@[simp] theorem empty_base_iff : M.Base ∅ ↔ M = loopyOn M.E := by
  simp_rw [eq_iff_indep_iff_indep_forall, and_iff_right (show M.E = (loopyOn M.E).E from rfl),
    loopyOn_indep_iff]
  refine ⟨fun h I hIE ↦ ⟨fun hI ↦ ?_, ?_⟩, fun h ↦ ?_⟩
  · rw [h.eq_of_subset_indep hI <| empty_subset _]
  · rintro rfl
    exact h.indep.subset <| empty_subset _
  refine base_iff_maximal_indep.2 ⟨M.empty_indep, fun I hI _ ↦ ?_⟩
  rwa [eq_comm, ← h I hI.subset_ground]

theorem eq_loopyOn_or_rkPos (M : Matroid α) : M = loopyOn M.E ∨ RkPos M := by
  rw [← empty_base_iff, rkPos_iff_empty_not_base]; apply em

theorem not_rkPos_iff : ¬RkPos M ↔ M = loopyOn M.E := by
  rw [rkPos_iff_empty_not_base, not_iff_comm, empty_base_iff]

end LoopyOn

section FreeOn

/-- The `Matroid α` with ground set `E` whose only base is `E`. -/
def freeOn (E : Set α) : Matroid α := (loopyOn E)﹡

@[simp] theorem freeOn_ground : (freeOn E).E = E := rfl

@[simp] theorem freeOn_dual_eq : (freeOn E)﹡ = loopyOn E := by
  rw [freeOn, dual_dual]

@[simp] theorem loopyOn_dual_eq : (loopyOn E)﹡ = freeOn E := rfl

@[simp] theorem freeOn_empty (α : Type*) : freeOn (∅ : Set α) = emptyOn α := by
  simp [freeOn]

@[simp] theorem freeOn_base_iff : (freeOn E).Base B ↔ B = E := by
  simp only [freeOn, loopyOn_ground, dual_base_iff', loopyOn_base_iff, diff_eq_empty,
    ← subset_antisymm_iff, eq_comm (a := E)]

@[simp] theorem freeOn_indep_iff : (freeOn E).Indep I ↔ I ⊆ E := by
  simp [indep_iff_subset_base]

theorem freeOn_indep (hIE : I ⊆ E) : (freeOn E).Indep I :=
  freeOn_indep_iff.2 hIE

@[simp] theorem freeOn_basis_iff : (freeOn E).Basis I X ↔ I = X ∧ X ⊆ E := by
  use fun h ↦ ⟨(freeOn_indep h.subset_ground).eq_of_basis h ,h.subset_ground⟩
  rintro ⟨rfl, hIE⟩
  exact (freeOn_indep hIE).basis_self

@[simp] theorem freeOn_basis'_iff : (freeOn E).Basis' I X ↔ I = X ∩ E := by
  rw [basis'_iff_basis_inter_ground, freeOn_basis_iff, freeOn_ground,
    and_iff_left (inter_subset_right _ _)]

@[simp] theorem eq_freeOn_iff : M = freeOn E ↔ M.E = E ∧ M.Indep E := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro rfl; simp [Subset.rfl]
  simp only [eq_iff_indep_iff_indep_forall, freeOn_ground, freeOn_indep_iff, h.1, true_and]
  exact fun I hIX ↦ iff_of_true (h.2.subset hIX) hIX

theorem ground_indep_iff_eq_freeOn : M.Indep M.E ↔ M = freeOn M.E := by
  simp

theorem freeOn_restrict (h : R ⊆ E) : (freeOn E) ↾ R = freeOn R := by
  simp [h, Subset.rfl]

end FreeOn

section uniqueBaseOn

/-- The matroid on `E` whose unique base is the subset `I` of `E`.
Intended for use when `I ⊆ E`; if this not not the case, then the base is `I ∩ E`. -/
def uniqueBaseOn (I E : Set α) : Matroid α := (freeOn I) ↾ E

@[simp] theorem uniqueBaseOn_ground : (uniqueBaseOn I E).E = E :=
  rfl

theorem uniqueBaseOn_base_iff (hIE : I ⊆ E) : (uniqueBaseOn I E).Base B ↔ B = I := by
  rw [uniqueBaseOn, base_restrict_iff', freeOn_basis'_iff, inter_eq_self_of_subset_right hIE]

theorem uniqueBaseOn_inter_ground_eq (I E : Set α) :
    uniqueBaseOn (I ∩ E) E = uniqueBaseOn I E := by
  simp only [uniqueBaseOn, restrict_eq_restrict_iff, freeOn_indep_iff, subset_inter_iff,
    iff_self_and]
  tauto

@[simp] theorem uniqueBaseOn_indep_iff' : (uniqueBaseOn I E).Indep J ↔ J ⊆ I ∩ E := by
  rw [uniqueBaseOn, restrict_indep_iff, freeOn_indep_iff, subset_inter_iff]

theorem uniqueBaseOn_indep_iff (hIE : I ⊆ E) : (uniqueBaseOn I E).Indep J ↔ J ⊆ I := by
  rw [uniqueBaseOn, restrict_indep_iff, freeOn_indep_iff, and_iff_left_iff_imp]
  exact fun h ↦ h.trans hIE

theorem uniqueBaseOn_basis_iff (hI : I ⊆ E) (hX : X ⊆ E) :
    (uniqueBaseOn I E).Basis J X ↔ J = X ∩ I := by
  rw [basis_iff_mem_maximals]
  simp_rw [uniqueBaseOn_indep_iff', ← subset_inter_iff, ← le_eq_subset, Iic_def, maximals_Iic,
    mem_singleton_iff, inter_eq_self_of_subset_left hI, inter_comm I]

theorem uniqueBaseOn_inter_basis (hI : I ⊆ E) (hX : X ⊆ E) :
    (uniqueBaseOn I E).Basis (X ∩ I) X := by
  rw [uniqueBaseOn_basis_iff hI hX]

@[simp] theorem uniqueBaseOn_dual_eq (I E : Set α) :
    (uniqueBaseOn I E)﹡ = uniqueBaseOn (E \ I) E := by
  rw [← uniqueBaseOn_inter_ground_eq]
  refine eq_of_base_iff_base_forall rfl (fun B (hB : B ⊆ E) ↦ ?_)
  rw [dual_base_iff, uniqueBaseOn_base_iff (inter_subset_right _ _),
    uniqueBaseOn_base_iff (diff_subset _ _), uniqueBaseOn_ground]
  refine' ⟨fun h ↦ _, fun h ↦ _⟩
  · rw [← diff_diff_cancel_left hB, h, diff_inter_self_eq_diff]
  rw [h, inter_comm I]; simp

@[simp] theorem uniqueBaseOn_self (I : Set α) : (uniqueBaseOn I I) = freeOn I := by
  rw [uniqueBaseOn, freeOn_restrict rfl.subset]

@[simp] theorem uniqueBaseOn_empty (I : Set α) : (uniqueBaseOn ∅ I) = loopyOn I := by
  rw [← dual_inj, uniqueBaseOn_dual_eq, diff_empty, uniqueBaseOn_self, loopyOn_dual_eq]

@[simp] theorem uniqueBaseOn_restrict' (I E R : Set α) :
    (uniqueBaseOn I E) ↾ R = uniqueBaseOn (I ∩ R ∩ E) R := by
  simp_rw [eq_iff_indep_iff_indep_forall, restrict_ground_eq, uniqueBaseOn_ground, true_and,
    restrict_indep_iff, uniqueBaseOn_indep_iff', subset_inter_iff]
  tauto

theorem uniqueBaseOn_restrict (h : I ⊆ E) (R : Set α) :
    (uniqueBaseOn I E) ↾ R = uniqueBaseOn (I ∩ R) R := by
  rw [uniqueBaseOn_restrict', inter_right_comm, inter_eq_self_of_subset_left h]

end uniqueBaseOn
