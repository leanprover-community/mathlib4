/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.RingTheory.FilteredAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Relations between graded rings and filtered rings

In this file, we introduce the filtered ring attached to a graded ring, when the grading is by an
ordered additive commutative monoid.

## TODO

* Define associated graded

-/

public section

noncomputable section

universe u v w

variable {ι : Type v} {R : Type w} {A : Type u}

section

variable [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι] [IsOrderedAddMonoid ι] [CommSemiring R]
  [Semiring A] [Algebra R A] (F : ι → Submodule R A) [GradedAlgebra F]

open DirectSum

lemma isRingFiltration_of_graded :
    IsRingFiltration (fun i ↦ ⨆ j ≤ i, F j) (fun i ↦ ⨆ j < i, F j) where
  mono _ j h := by
    simp only [iSup_le_iff]
    intro i hi
    refine le_iSup_of_le i ?_
    rw [le_iSup_iff]
    have : i ≤ j := hi.trans h
    tauto
  is_le {_ j} h := by
    simp only [iSup_le_iff]
    intro i hi
    refine le_iSup_of_le i ?_
    rw [le_iSup_iff]
    have : i < j := lt_of_le_of_lt hi h
    tauto
  is_sup _ _ h := by
    simp only [iSup_le_iff]
    intro i hi
    simp only [iSup_le_iff] at h
    exact h i hi i (Std.IsPreorder.le_refl i)
  one_mem := mem_of_le_of_mem (S := F 0)
    (le_iSup_iff.mpr fun _ h ↦ (by simpa using h 0)) (SetLike.one_mem_graded F)
  mul_mem {i j} gi gj hi hj := by
    classical
    obtain ⟨fgi, hgi⟩ := (Submodule.mem_biSup_iff_exists_dfinsupp R (fun k ↦ k ≤ i) F gi).mp hi
    obtain ⟨fgj, hgj⟩ := (Submodule.mem_biSup_iff_exists_dfinsupp R (fun k ↦ k ≤ j) F gj).mp hj
    rw [← hgi, ← hgj]
    simp only [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum,
      DFinsupp.support_filter, DFinsupp.filter_apply, LinearMap.toAddMonoidHom_coe,
      Submodule.subtype_apply, Finset.sum_mul_sum]
    refine sum_mem fun k hk ↦ sum_mem fun l hl ↦ ?_
    have hki : k ≤ i := by grind
    have hlj : l ≤ j := by grind
    simp only [hki, ↓reduceIte, hlj]
    refine Set.mem_of_subset_of_mem (SetLike.coe_subset_coe.mpr (le_sSup ?_)) <|
      SetLike.mul_mem_graded (Submodule.coe_mem (fgi k)) (Submodule.coe_mem (fgj l))
    use k + l
    simp [add_le_add hki hlj]

end
