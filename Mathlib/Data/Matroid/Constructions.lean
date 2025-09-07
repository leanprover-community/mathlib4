/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Matroid.Minor.Restrict

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

assert_not_exists Field

variable {α : Type*} {M : Matroid α} {E B I X R J : Set α}

namespace Matroid

open Set

section EmptyOn

/-- The `Matroid α` with empty ground set. -/
def emptyOn (α : Type*) : Matroid α where
  E := ∅
  IsBase := (· = ∅)
  Indep := (· = ∅)
  indep_iff' := by simp [subset_empty_iff]
  exists_isBase := ⟨∅, rfl⟩
  isBase_exchange := by rintro _ _ rfl; simp
  maximality := by rintro _ _ _ rfl -; exact ⟨∅, by simp [Maximal]⟩
  subset_ground := by simp

@[simp] theorem emptyOn_ground : (emptyOn α).E = ∅ := rfl

@[simp] theorem emptyOn_isBase_iff : (emptyOn α).IsBase B ↔ B = ∅ := Iff.rfl

@[simp] theorem emptyOn_indep_iff : (emptyOn α).Indep I ↔ I = ∅ := Iff.rfl

theorem ground_eq_empty_iff : (M.E = ∅) ↔ M = emptyOn α := by
  simp only [emptyOn, ext_iff_indep, iff_self_and]
  exact fun h ↦ by simp [h, subset_empty_iff]

@[simp] theorem emptyOn_dual_eq : (emptyOn α)✶ = emptyOn α := by
  rw [← ground_eq_empty_iff]; rfl

@[simp] theorem restrict_empty (M : Matroid α) : M ↾ (∅ : Set α) = emptyOn α := by
  simp [← ground_eq_empty_iff]

theorem eq_emptyOn_or_nonempty (M : Matroid α) : M = emptyOn α ∨ Matroid.Nonempty M := by
  rw [← ground_eq_empty_iff]
  exact M.E.eq_empty_or_nonempty.elim Or.inl (fun h ↦ Or.inr ⟨h⟩)

theorem eq_emptyOn [IsEmpty α] (M : Matroid α) : M = emptyOn α := by
  rw [← ground_eq_empty_iff]
  exact M.E.eq_empty_of_isEmpty

instance finite_emptyOn (α : Type*) : (emptyOn α).Finite :=
  ⟨finite_empty⟩

end EmptyOn

section LoopyOn

/-- The `Matroid α` with ground set `E` whose only base is `∅`.
The elements are all 'loops' - see `Matroid.IsLoop` and `Matroid.loopyOn_isLoop_iff`. -/
def loopyOn (E : Set α) : Matroid α := emptyOn α ↾ E

@[simp] theorem loopyOn_ground (E : Set α) : (loopyOn E).E = E := rfl

@[simp] theorem loopyOn_empty (α : Type*) : loopyOn (∅ : Set α) = emptyOn α := by
  rw [← ground_eq_empty_iff, loopyOn_ground]

@[simp] theorem loopyOn_indep_iff : (loopyOn E).Indep I ↔ I = ∅ := by
  simp only [loopyOn, restrict_indep_iff, emptyOn_indep_iff, and_iff_left_iff_imp]
  rintro rfl; apply empty_subset

theorem eq_loopyOn_iff : M = loopyOn E ↔ M.E = E ∧ ∀ X ⊆ M.E, M.Indep X → X = ∅ := by
  simp only [ext_iff_indep, loopyOn_ground, loopyOn_indep_iff, and_congr_right_iff]
  rintro rfl
  refine ⟨fun h I hI ↦ (h hI).1, fun h I hIE ↦ ⟨h I hIE, by rintro rfl; simp⟩⟩

@[simp] theorem loopyOn_isBase_iff : (loopyOn E).IsBase B ↔ B = ∅ := by
  simp [Maximal, isBase_iff_maximal_indep]

@[simp] theorem loopyOn_isBasis_iff : (loopyOn E).IsBasis I X ↔ I = ∅ ∧ X ⊆ E :=
  ⟨fun h ↦ ⟨loopyOn_indep_iff.mp h.indep, h.subset_ground⟩,
    by rintro ⟨rfl, hX⟩; rw [isBasis_iff]; simp⟩

instance loopyOn_rankFinite : RankFinite (loopyOn E) :=
  ⟨∅, by simp⟩

theorem Finite.loopyOn_finite (hE : E.Finite) : Matroid.Finite (loopyOn E) :=
  ⟨hE⟩

@[simp] theorem loopyOn_restrict (E R : Set α) : (loopyOn E) ↾ R = loopyOn R := by
  refine ext_indep rfl ?_
  simp only [restrict_ground_eq, restrict_indep_iff, loopyOn_indep_iff, and_iff_left_iff_imp]
  exact fun _ h _ ↦ h

theorem empty_isBase_iff : M.IsBase ∅ ↔ M = loopyOn M.E := by
  simp only [isBase_iff_maximal_indep, Maximal, empty_indep, le_eq_subset, empty_subset,
    subset_empty_iff, true_implies, true_and, ext_iff_indep, loopyOn_ground,
    loopyOn_indep_iff]
  exact ⟨fun h I _ ↦ ⟨@h _, fun hI ↦ by simp [hI]⟩, fun h I hI ↦ (h hI.subset_ground).1 hI⟩

theorem eq_loopyOn_or_rankPos (M : Matroid α) : M = loopyOn M.E ∨ RankPos M := by
  rw [← empty_isBase_iff, rankPos_iff]; apply em

theorem not_rankPos_iff : ¬RankPos M ↔ M = loopyOn M.E := by
  rw [rankPos_iff, not_iff_comm, empty_isBase_iff]

end LoopyOn

section FreeOn

/-- The `Matroid α` with ground set `E` whose only base is `E`. -/
def freeOn (E : Set α) : Matroid α := (loopyOn E)✶

@[simp] theorem freeOn_ground : (freeOn E).E = E := rfl

@[simp] theorem freeOn_dual_eq : (freeOn E)✶ = loopyOn E := by
  rw [freeOn, dual_dual]

@[simp] theorem loopyOn_dual_eq : (loopyOn E)✶ = freeOn E := rfl

@[simp] theorem freeOn_empty (α : Type*) : freeOn (∅ : Set α) = emptyOn α := by
  simp [freeOn]

@[simp] theorem freeOn_isBase_iff : (freeOn E).IsBase B ↔ B = E := by
  simp only [freeOn, loopyOn_ground, dual_isBase_iff', loopyOn_isBase_iff, diff_eq_empty,
    ← subset_antisymm_iff, eq_comm (a := E)]

@[simp] theorem freeOn_indep_iff : (freeOn E).Indep I ↔ I ⊆ E := by
  simp [indep_iff]

theorem freeOn_indep (hIE : I ⊆ E) : (freeOn E).Indep I :=
  freeOn_indep_iff.2 hIE

@[simp] theorem freeOn_isBasis_iff : (freeOn E).IsBasis I X ↔ I = X ∧ X ⊆ E := by
  use fun h ↦ ⟨(freeOn_indep h.subset_ground).eq_of_isBasis h ,h.subset_ground⟩
  rintro ⟨rfl, hIE⟩
  exact (freeOn_indep hIE).isBasis_self

@[simp] theorem freeOn_isBasis'_iff : (freeOn E).IsBasis' I X ↔ I = X ∩ E := by
  rw [isBasis'_iff_isBasis_inter_ground, freeOn_isBasis_iff, freeOn_ground,
    and_iff_left inter_subset_right]

theorem eq_freeOn_iff : M = freeOn E ↔ M.E = E ∧ M.Indep E := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro rfl; simp
  simp only [ext_iff_indep, freeOn_ground, freeOn_indep_iff, h.1, true_and]
  exact fun I hIX ↦ iff_of_true (h.2.subset hIX) hIX

theorem ground_indep_iff_eq_freeOn : M.Indep M.E ↔ M = freeOn M.E := by
  simp [eq_freeOn_iff]

theorem freeOn_restrict (h : R ⊆ E) : (freeOn E) ↾ R = freeOn R := by
  simp [h, eq_freeOn_iff]

theorem restrict_eq_freeOn_iff : M ↾ I = freeOn I ↔ M.Indep I := by
  rw [eq_freeOn_iff, and_iff_right M.restrict_ground_eq, restrict_indep_iff,
    and_iff_left Subset.rfl]

theorem Indep.restrict_eq_freeOn (hI : M.Indep I) : M ↾ I = freeOn I := by
  rwa [restrict_eq_freeOn_iff]

instance freeOn_finitary : Finitary (freeOn E) := by
  simp only [finitary_iff, freeOn_indep_iff]
  exact fun I h e heI ↦ by simpa using h {e} (by simpa)

lemma freeOn_rankPos (hE : E.Nonempty) : RankPos (freeOn E) := by
  simp [rankPos_iff, hE.ne_empty.symm]

end FreeOn

section uniqueBaseOn

/-- The matroid on `E` whose unique base is the subset `I` of `E`.
Intended for use when `I ⊆ E`; if this not not the case, then the base is `I ∩ E`. -/
def uniqueBaseOn (I E : Set α) : Matroid α := freeOn I ↾ E

@[simp] theorem uniqueBaseOn_ground : (uniqueBaseOn I E).E = E :=
  rfl

theorem uniqueBaseOn_isBase_iff (hIE : I ⊆ E) : (uniqueBaseOn I E).IsBase B ↔ B = I := by
  rw [uniqueBaseOn, isBase_restrict_iff', freeOn_isBasis'_iff, inter_eq_self_of_subset_right hIE]

theorem uniqueBaseOn_inter_ground_eq (I E : Set α) :
    uniqueBaseOn (I ∩ E) E = uniqueBaseOn I E := by
  simp only [uniqueBaseOn, restrict_eq_restrict_iff, freeOn_indep_iff, subset_inter_iff]
  tauto

@[simp] theorem uniqueBaseOn_indep_iff' : (uniqueBaseOn I E).Indep J ↔ J ⊆ I ∩ E := by
  rw [uniqueBaseOn, restrict_indep_iff, freeOn_indep_iff, subset_inter_iff]

theorem uniqueBaseOn_indep_iff (hIE : I ⊆ E) : (uniqueBaseOn I E).Indep J ↔ J ⊆ I := by
  rw [uniqueBaseOn, restrict_indep_iff, freeOn_indep_iff, and_iff_left_iff_imp]
  exact fun h ↦ h.trans hIE

theorem uniqueBaseOn_isBasis_iff (hX : X ⊆ E) : (uniqueBaseOn I E).IsBasis J X ↔ J = X ∩ I := by
  rw [isBasis_iff_maximal]
  exact maximal_iff_eq (by simp [inter_subset_left.trans hX])
    (by simp +contextual)

theorem uniqueBaseOn_inter_isBasis (hX : X ⊆ E) : (uniqueBaseOn I E).IsBasis (X ∩ I) X := by
  rw [uniqueBaseOn_isBasis_iff hX]

@[simp] theorem uniqueBaseOn_dual_eq (I E : Set α) :
    (uniqueBaseOn I E)✶ = uniqueBaseOn (E \ I) E := by
  rw [← uniqueBaseOn_inter_ground_eq]
  refine ext_isBase rfl (fun B (hB : B ⊆ E) ↦ ?_)
  rw [dual_isBase_iff, uniqueBaseOn_isBase_iff inter_subset_right,
    uniqueBaseOn_isBase_iff diff_subset, uniqueBaseOn_ground]
  exact ⟨fun h ↦ by rw [← diff_diff_cancel_left hB, h, diff_inter_self_eq_diff],
    fun h ↦ by rw [h, inter_comm I]; simp⟩

@[simp] theorem uniqueBaseOn_self (I : Set α) : uniqueBaseOn I I = freeOn I := by
  rw [uniqueBaseOn, freeOn_restrict rfl.subset]

@[simp] theorem uniqueBaseOn_empty (I : Set α) : uniqueBaseOn ∅ I = loopyOn I := by
  rw [← dual_inj, uniqueBaseOn_dual_eq, diff_empty, uniqueBaseOn_self, loopyOn_dual_eq]

theorem uniqueBaseOn_restrict' (I E R : Set α) :
    (uniqueBaseOn I E) ↾ R = uniqueBaseOn (I ∩ R ∩ E) R := by
  simp_rw [ext_iff_indep, restrict_ground_eq, uniqueBaseOn_ground, true_and,
    restrict_indep_iff, uniqueBaseOn_indep_iff', subset_inter_iff]
  tauto

theorem uniqueBaseOn_restrict (h : I ⊆ E) (R : Set α) :
    (uniqueBaseOn I E) ↾ R = uniqueBaseOn (I ∩ R) R := by
  rw [uniqueBaseOn_restrict', inter_right_comm, inter_eq_self_of_subset_left h]

lemma uniqueBaseOn_rankFinite (hI : I.Finite) : RankFinite (uniqueBaseOn I E) := by
  rw [← uniqueBaseOn_inter_ground_eq]
  refine ⟨I ∩ E, ?_⟩
  rw [uniqueBaseOn_isBase_iff inter_subset_right, and_iff_right rfl]
  exact hI.subset inter_subset_left

instance uniqueBaseOn_finitary : Finitary (uniqueBaseOn I E) := by
  refine ⟨fun K hK ↦ ?_⟩
  simp only [uniqueBaseOn_indep_iff'] at hK ⊢
  exact fun e heK ↦ singleton_subset_iff.1 <| hK _ (by simpa) (by simp)

lemma uniqueBaseOn_rankPos (hIE : I ⊆ E) (hI : I.Nonempty) : RankPos (uniqueBaseOn I E) where
  empty_not_isBase := by simpa [uniqueBaseOn_isBase_iff hIE] using Ne.symm <| hI.ne_empty

end uniqueBaseOn

end Matroid
