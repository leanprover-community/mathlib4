/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# Subtraction of kernels

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open MeasureTheory MeasurableSpace
open scoped ENNReal

namespace ProbabilityTheory.Kernel


variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [CountableOrCountablyGenerated α β] {κ η : Kernel α β}

noncomputable
instance [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)] : Sub (Kernel α β) where
  sub κ η := if h : IsSFiniteKernel κ ∧ IsSFiniteKernel η
    then
      have := h.1
      have := h.2
      η.withDensity (fun a ↦ κ.rnDeriv η a - 1) + κ.singularPart η
    else 0

lemma sub_def [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)] :
    κ - η = if h : IsSFiniteKernel κ ∧ IsSFiniteKernel η
    then
      have := h.1
      have := h.2
      η.withDensity (fun a ↦ κ.rnDeriv η a - 1) + κ.singularPart η
    else 0 :=
  rfl

@[simp]
lemma sub_of_not_isSFiniteKernel_left [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)]
    (h : ¬IsSFiniteKernel κ) : κ - η = 0 := by simp [sub_def, h]

@[simp]
lemma sub_of_not_isSFiniteKernel_right [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)]
    (h : ¬IsSFiniteKernel η) : κ - η = 0 := by simp [sub_def, h]

lemma sub_of_isSFiniteKernel [IsSFiniteKernel κ] [IsSFiniteKernel η]
    [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)] :
    κ - η = η.withDensity (fun a ↦ κ.rnDeriv η a - 1) + κ.singularPart η := by
  rw [sub_def, dif_pos]
  exact ⟨inferInstance, inferInstance⟩

-- todo name
lemma sub_apply_eq_rnDeriv_add_singularPart [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)]
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (a : α) :
    (κ - η) a = η.withDensity (fun a ↦ κ.rnDeriv η a - 1) a + κ.singularPart η a := by
  rw [sub_of_isSFiniteKernel]
  rfl

lemma sub_apply [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)] [IsFiniteKernel κ]
    [IsFiniteKernel η] (a : α) :
    (κ - η) a = κ a - η a := by
  ext s hs
  rw [sub_apply_eq_rnDeriv_add_singularPart, Kernel.withDensity_apply _ (by fun_prop),
    Kernel.singularPart_eq_singularPart_measure, Measure.sub_apply_eq_rnDeriv_add_singularPart _]
  simp only [Measure.coe_add, Pi.add_apply]
  congr 2
  refine MeasureTheory.withDensity_congr_ae ?_
  filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with b hb
  simp [← hb]

omit [CountableOrCountablyGenerated α β] in
lemma le_iff (κ η : Kernel α β) : κ ≤ η ↔ ∀ a, κ a ≤ η a := Iff.rfl

lemma sub_le_self [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)] [IsFiniteKernel κ]
    [IsFiniteKernel η] :
    κ - η ≤ κ := by
  rw [le_iff]
  intro a
  rw [sub_apply]
  exact Measure.sub_le

instance [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)]
    [IsFiniteKernel κ] [IsFiniteKernel η] : IsFiniteKernel (κ - η) :=
  isFiniteKernel_of_le sub_le_self

lemma sub_apply_eq_zero_iff_le [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)]
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) : (κ - η) a = 0 ↔ κ a ≤ η a := by
  simp_rw [sub_apply_eq_rnDeriv_add_singularPart,
    add_eq_zero_iff_of_nonneg (Measure.zero_le _) (Measure.zero_le _)]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [Kernel.withDensity_apply _ (by fun_prop), withDensity_eq_zero_iff (by fun_prop)] at h
    rw [singularPart_eq_zero_iff_absolutelyContinuous κ η a] at h
    rw [← Measure.rnDeriv_le_one_iff_le h.2]
    filter_upwards [h.1, rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with b hb1 hb2
    rw [← hb2]
    simp only [Pi.sub_apply, Pi.one_apply, Pi.zero_apply] at hb1
    rwa [tsub_eq_zero_iff_le] at hb1
  · rw [(singularPart_eq_zero_iff_absolutelyContinuous κ η a).mpr
        (Measure.absolutelyContinuous_of_le h)]
    rw [Kernel.withDensity_apply _ (by fun_prop), withDensity_eq_zero_iff (by fun_prop)]
    simp only [and_true]
    suffices κ.rnDeriv η a ≤ᵐ[η a] 1 by
      filter_upwards [this] with b hb
      simpa [tsub_eq_zero_iff_le] using hb
    filter_upwards [Measure.rnDeriv_le_one_of_le h,
      rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with b hb1 hb2
    rwa [hb2]

lemma sub_eq_zero_iff_le [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)]
    [IsFiniteKernel κ] [IsFiniteKernel η] : κ - η = 0 ↔ κ ≤ η := by
  simp [Kernel.ext_iff, le_iff, sub_apply_eq_zero_iff_le]

lemma measurableSet_eq_zero (κ : Kernel α β) [IsFiniteKernel κ] :
    MeasurableSet {a | κ a = 0} := by
  have h_sing : {a | κ a = 0} = {a | κ a ⟂ₘ κ a} := by ext; simp
  rw [h_sing]
  exact measurableSet_mutuallySingular κ κ

lemma measurableSet_le [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    MeasurableSet {a | κ a ≤ η a} := by
  have h_sub : {a | κ a ≤ η a} = {a | (κ - η) a = 0} := by
    ext; simp [sub_apply_eq_zero_iff_le]
  rw [h_sub]
  exact measurableSet_eq_zero _

lemma measurableSet_eq [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    MeasurableSet {a | κ a = η a} := by
  have h_sub : {a | κ a = η a} = {a | (κ - η) a = 0} ∩ {a | (η - κ) a = 0} := by
    ext1 a
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, sub_apply_eq_zero_iff_le]
    exact ⟨fun h ↦ by simp [h], fun h ↦ le_antisymm h.1 h.2⟩
  rw [h_sub]
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_eq_zero _
  · exact measurableSet_eq_zero _

end ProbabilityTheory.Kernel
