/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.SetTheory.Cardinal.Cofinality.Club

/-!
# Dieudonné measure

write neat thing here
-/

@[expose] public section

open Cardinal MeasureTheory Order Set

variable {α : Type*} {x y : α} [LinearOrder α]

/-- A type alias which endows a well-order `α` with the Dieudonne measure. -/
def Dieudonne (α : Type*) : Type _ := α

namespace Dieudonne

instance : LinearOrder (Dieudonne α) := inferInstanceAs (LinearOrder α)

def of : α ≃o Dieudonne α := .refl _
def val : Dieudonne α ≃o α := .refl _

@[simp] theorem of_val (x : α) : of (val x) = x := rfl
@[simp] theorem val_of (x : Dieudonne α) : val (of x) = x := rfl

variable [WellFoundedLT α] [h₀ : Fact (cof α ≠ ℵ₀)]
include h₀

instance : MeasurableSpace (Dieudonne α) where
  MeasurableSet' s := ∃ t, IsClub t ∧ (t ⊆ (of ⁻¹' s) ∨ t ⊆ (of ⁻¹' s)ᶜ)
  measurableSet_empty := ⟨_, .univ, by simp⟩
  measurableSet_compl _ := by simp [or_comm]
  measurableSet_iUnion f hf := by
    by_cases! H : ∃ i t, IsClub t ∧ t ⊆ (of ⁻¹' f i)
    · obtain ⟨i, t, ht, htf⟩ := H
      exact ⟨t, ht, .inl (htf.trans (subset_iUnion f i))⟩
    choose g hg hgf using hf
    refine ⟨⋂ i, g i, ?_, ?_⟩
    · obtain hα | hα := h₀.out.lt_or_gt
      · rw [cof_lt_aleph0_iff] at hα
        exact .iInter_of_cof_le_one hα hg
      · exact .iInter hα.ne' (by simpa) hg
    · right
      rw [subset_compl_iff_disjoint_left, preimage_iUnion, disjoint_iUnion_left]
      refine fun i ↦ .mono_right (Set.iInter_subset g i) ?_
      rw [← subset_compl_iff_disjoint_left]
      exact (hgf i).resolve_left <| H _ _ (hg i)

def measure : Measure (Dieudonne α) where
  measureOf s := if IsStationary

end Dieudonne
