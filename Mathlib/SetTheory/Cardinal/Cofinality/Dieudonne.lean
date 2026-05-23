/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
public import Mathlib.SetTheory.Cardinal.Cofinality.Club

/-!
# Dieudonné measure

write neat thing here
-/

@[expose] public noncomputable section

open Cardinal MeasureTheory Order Set

variable {α : Type*} {x y : α} [LinearOrder α]

/-- A type alias which endows a well-order `α` with the Dieudonne measure. -/
def Dieudonne (α : Type*) : Type _ := α

namespace Dieudonne
variable {s : Set (Dieudonne α)}

instance : LinearOrder (Dieudonne α) := inferInstanceAs (LinearOrder α)
instance [h : Nonempty α] : Nonempty (Dieudonne α) := h
instance [h : WellFoundedLT α] : WellFoundedLT (Dieudonne α) := h

def of : α ≃o Dieudonne α := .refl _
def val : Dieudonne α ≃o α := .refl _

@[simp] theorem of_val (x : α) : of (val x) = x := rfl
@[simp] theorem val_of (x : Dieudonne α) : val (of x) = x := rfl

variable [WellFoundedLT α] [h₀ : Fact (cof α ≠ ℵ₀)]
include h₀

instance : MeasurableSpace (Dieudonne α) where
  MeasurableSet' s := ∃ t, IsClub t ∧ (t ⊆ s ∨ t ⊆ sᶜ)
  measurableSet_empty := ⟨_, .univ, by simp⟩
  measurableSet_compl _ := by simp [or_comm]
  measurableSet_iUnion f hf := by
    by_cases! H : ∃ i t, IsClub t ∧ t ⊆ f i
    · obtain ⟨i, t, ht, htf⟩ := H
      exact ⟨t, ht, .inl (htf.trans (subset_iUnion f i))⟩
    choose g hg hgf using hf
    refine ⟨⋂ i, g i, ?_, ?_⟩
    · obtain hα | hα := h₀.out.lt_or_gt
      · rw [cof_lt_aleph0_iff] at hα
        exact .iInter_of_cof_le_one hα hg
      · exact .iInter hα.ne' (by simpa) hg
    · right
      rw [subset_compl_iff_disjoint_left, disjoint_iUnion_left]
      refine fun i ↦ .mono_right (Set.iInter_subset g i) ?_
      rw [← subset_compl_iff_disjoint_left]
      exact (hgf i).resolve_left <| H _ _ (hg i)

theorem measurableSet_def : MeasurableSet s ↔ ∃ t, IsClub t ∧ (t ⊆ s ∨ t ⊆ sᶜ) :=
  .rfl

theorem measurableSet_of_isClub (hs : IsClub s) : MeasurableSet s :=
  ⟨s, hs, .inl subset_rfl⟩

theorem measurableSet_of_not_isStationary (hs : ¬ IsStationary s) : MeasurableSet s := by
  obtain ⟨t, ht, ht'⟩ := not_isStationary_iff.1 hs
  exact ⟨t, ht, .inr <| ht'.subset_compl_left⟩

open Classical in
def measure : Measure (Dieudonne α) where
  measureOf s := if IsStationary s then 1 else 0
  empty := by simp
  mono {s t} hst := by
    by_cases H : IsStationary s ∧ ¬ IsStationary t
    · cases H.2 <| H.1.mono hst
    · split_ifs <;> simp_all
  iUnion_nat f hf := by
    sorry
  m_iUnion := by
    sorry
  trim_le s := by
    rw [OuterMeasure.trim_eq_iInf']
    change ⨅ _, ite .. ≤ ite ..
    split_ifs with hs
    · refine iInf_le_of_le ⟨univ, ?_⟩ ?_
      · simp
      · split_ifs <;> simp
    · refine iInf_le_of_le ⟨s, ?_⟩ ?_
      · simpa using measurableSet_of_not_isStationary hs
      · simp [hs]

instance : IsZeroOneMeasure (α := α) measure where
  zero_one₀ s _ := by rw [or_comm]; classical exact ite_eq_or_eq ..

theorem measure_of_isStationary (hs : IsStationary s) : measure s = 1 := dif_pos hs
theorem measure_of_not_isStationary (hs : ¬ IsStationary s) : measure s = 0 := dif_neg hs

theorem measure_of_isClub [Nonempty α] (hs : IsClub s) : measure s = 1 :=
  measure_of_isStationary (hs.isStationary h₀.out)

@[simp]
theorem measure_univ [Nonempty α] : measure (@univ α) = 1 :=
  measure_of_isStationary .univ

end Dieudonne
