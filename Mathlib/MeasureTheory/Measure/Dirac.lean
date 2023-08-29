/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
/-!
# Dirac measure

In this file we define the Dirac measure `MeasureTheory.Measure.dirac a`
and prove some basic facts about it.
-/

set_option autoImplicit true

open Function Set
open scoped ENNReal Classical

noncomputable section

variable [MeasurableSpace α] [MeasurableSpace β] {s : Set α}

namespace MeasureTheory

namespace Measure

/-- The dirac measure. -/
def dirac (a : α) : Measure α := (OuterMeasure.dirac a).toMeasure (by simp)
                                                                      -- 🎉 no goals
#align measure_theory.measure.dirac MeasureTheory.Measure.dirac

instance : MeasureSpace PUnit :=
  ⟨dirac PUnit.unit⟩

theorem le_dirac_apply {a} : s.indicator 1 a ≤ dirac a s :=
  OuterMeasure.dirac_apply a s ▸ le_toMeasure_apply _ _ _
#align measure_theory.measure.le_dirac_apply MeasureTheory.Measure.le_dirac_apply

@[simp]
theorem dirac_apply' (a : α) (hs : MeasurableSet s) : dirac a s = s.indicator 1 a :=
  toMeasure_apply _ _ hs
#align measure_theory.measure.dirac_apply' MeasureTheory.Measure.dirac_apply'

@[simp]
theorem dirac_apply_of_mem {a : α} (h : a ∈ s) : dirac a s = 1 := by
  have : ∀ t : Set α, a ∈ t → t.indicator (1 : α → ℝ≥0∞) a = 1 := fun t ht => indicator_of_mem ht 1
  -- ⊢ ↑↑(dirac a) s = 1
  refine' le_antisymm (this univ trivial ▸ _) (this s h ▸ le_dirac_apply)
  -- ⊢ ↑↑(dirac a) s ≤ indicator univ 1 a
  rw [← dirac_apply' a MeasurableSet.univ]
  -- ⊢ ↑↑(dirac a) s ≤ ↑↑(dirac a) univ
  exact measure_mono (subset_univ s)
  -- 🎉 no goals
#align measure_theory.measure.dirac_apply_of_mem MeasureTheory.Measure.dirac_apply_of_mem

@[simp]
theorem dirac_apply [MeasurableSingletonClass α] (a : α) (s : Set α) :
    dirac a s = s.indicator 1 a := by
  by_cases h : a ∈ s; · rw [dirac_apply_of_mem h, indicator_of_mem h, Pi.one_apply]
  -- ⊢ ↑↑(dirac a) s = indicator s 1 a
                        -- 🎉 no goals
  rw [indicator_of_not_mem h, ← nonpos_iff_eq_zero]
  -- ⊢ ↑↑(dirac a) s ≤ 0
  calc
    dirac a s ≤ dirac a {a}ᶜ := measure_mono (subset_compl_comm.1 <| singleton_subset_iff.2 h)
    _ = 0 := by simp [dirac_apply' _ (measurableSet_singleton _).compl]

#align measure_theory.measure.dirac_apply MeasureTheory.Measure.dirac_apply

theorem map_dirac {f : α → β} (hf : Measurable f) (a : α) : (dirac a).map f = dirac (f a) :=
  ext fun s hs => by simp [hs, map_apply hf hs, hf hs, indicator_apply]
                     -- 🎉 no goals
#align measure_theory.measure.map_dirac MeasureTheory.Measure.map_dirac

@[simp]
theorem restrict_singleton (μ : Measure α) (a : α) : μ.restrict {a} = μ {a} • dirac a := by
  ext1 s hs
  -- ⊢ ↑↑(restrict μ {a}) s = ↑↑(↑↑μ {a} • dirac a) s
  by_cases ha : a ∈ s
  -- ⊢ ↑↑(restrict μ {a}) s = ↑↑(↑↑μ {a} • dirac a) s
  · have : s ∩ {a} = {a} := by simpa
    -- ⊢ ↑↑(restrict μ {a}) s = ↑↑(↑↑μ {a} • dirac a) s
    simp [*]
    -- 🎉 no goals
  · have : s ∩ {a} = ∅ := inter_singleton_eq_empty.2 ha
    -- ⊢ ↑↑(restrict μ {a}) s = ↑↑(↑↑μ {a} • dirac a) s
    simp [*]
    -- 🎉 no goals
#align measure_theory.measure.restrict_singleton MeasureTheory.Measure.restrict_singleton

/-- If `f` is a map with countable codomain, then `μ.map f` is a sum of Dirac measures. -/
theorem map_eq_sum [Countable β] [MeasurableSingletonClass β] (μ : Measure α) (f : α → β)
    (hf : Measurable f) : μ.map f = sum fun b : β => μ (f ⁻¹' {b}) • dirac b := by
  ext1 s hs
  -- ⊢ ↑↑(map f μ) s = ↑↑(sum fun b => ↑↑μ (f ⁻¹' {b}) • dirac b) s
  have : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y}) := fun y _ => hf (measurableSet_singleton _)
  -- ⊢ ↑↑(map f μ) s = ↑↑(sum fun b => ↑↑μ (f ⁻¹' {b}) • dirac b) s
  simp [← tsum_measure_preimage_singleton (to_countable s) this, *,
    tsum_subtype s fun b => μ (f ⁻¹' {b}), ← indicator_mul_right s fun b => μ (f ⁻¹' {b})]
#align measure_theory.measure.map_eq_sum MeasureTheory.Measure.map_eq_sum

/-- A measure on a countable type is a sum of Dirac measures. -/
@[simp]
theorem sum_smul_dirac [Countable α] [MeasurableSingletonClass α] (μ : Measure α) :
    (sum fun a => μ {a} • dirac a) = μ := by simpa using (map_eq_sum μ id measurable_id).symm
                                             -- 🎉 no goals
#align measure_theory.measure.sum_smul_dirac MeasureTheory.Measure.sum_smul_dirac

/-- Given that `α` is a countable, measurable space with all singleton sets measurable,
write the measure of a set `s` as the sum of the measure of `{x}` for all `x ∈ s`. -/
theorem tsum_indicator_apply_singleton [Countable α] [MeasurableSingletonClass α] (μ : Measure α)
    (s : Set α) (hs : MeasurableSet s) : (∑' x : α, s.indicator (fun x => μ {x}) x) = μ s :=
  calc
    (∑' x : α, s.indicator (fun x => μ {x}) x) =
      Measure.sum (fun a => μ {a} • Measure.dirac a) s := by
      simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
        Set.indicator_apply, mul_ite, Pi.one_apply, mul_one, mul_zero]
    _ = μ s := by rw [μ.sum_smul_dirac]
                  -- 🎉 no goals
#align measure_theory.measure.tsum_indicator_apply_singleton MeasureTheory.Measure.tsum_indicator_apply_singleton

end Measure

open Measure

theorem mem_ae_dirac_iff {a : α} (hs : MeasurableSet s) : s ∈ (dirac a).ae ↔ a ∈ s := by
  by_cases a ∈ s <;> simp [mem_ae_iff, dirac_apply', hs.compl, indicator_apply, *]
  -- ⊢ s ∈ ae (dirac a) ↔ a ∈ s
  -- ⊢ s ∈ ae (dirac a) ↔ a ∈ s
                     -- 🎉 no goals
                     -- 🎉 no goals
#align measure_theory.mem_ae_dirac_iff MeasureTheory.mem_ae_dirac_iff

theorem ae_dirac_iff {a : α} {p : α → Prop} (hp : MeasurableSet { x | p x }) :
    (∀ᵐ x ∂dirac a, p x) ↔ p a :=
  mem_ae_dirac_iff hp
#align measure_theory.ae_dirac_iff MeasureTheory.ae_dirac_iff

@[simp]
theorem ae_dirac_eq [MeasurableSingletonClass α] (a : α) : (dirac a).ae = pure a := by
  ext s
  -- ⊢ s ∈ ae (dirac a) ↔ s ∈ pure a
  simp [mem_ae_iff, imp_false]
  -- 🎉 no goals
#align measure_theory.ae_dirac_eq MeasureTheory.ae_dirac_eq

theorem ae_eq_dirac' [MeasurableSingletonClass β] {a : α} {f : α → β} (hf : Measurable f) :
    f =ᵐ[dirac a] const α (f a) :=
  (ae_dirac_iff <| show MeasurableSet (f ⁻¹' {f a}) from hf <| measurableSet_singleton _).2 rfl
#align measure_theory.ae_eq_dirac' MeasureTheory.ae_eq_dirac'

theorem ae_eq_dirac [MeasurableSingletonClass α] {a : α} (f : α → δ) :
    f =ᵐ[dirac a] const α (f a) := by simp [Filter.EventuallyEq]
                                      -- 🎉 no goals
#align measure_theory.ae_eq_dirac MeasureTheory.ae_eq_dirac

instance Measure.dirac.isProbabilityMeasure [MeasurableSpace α] {x : α} :
    IsProbabilityMeasure (dirac x) :=
  ⟨dirac_apply_of_mem <| mem_univ x⟩
#align measure_theory.measure.dirac.is_probability_measure MeasureTheory.Measure.dirac.isProbabilityMeasure

theorem restrict_dirac' (hs : MeasurableSet s) [Decidable (a ∈ s)] :
    (Measure.dirac a).restrict s = if a ∈ s then Measure.dirac a else 0 := by
  split_ifs with has
  -- ⊢ Measure.restrict (dirac a) s = dirac a
  · apply restrict_eq_self_of_ae_mem
    -- ⊢ ∀ᵐ (x : α) ∂dirac a, x ∈ s
    rw [ae_dirac_iff] <;> assumption
    -- ⊢ a ∈ s
                          -- 🎉 no goals
                          -- 🎉 no goals
  · rw [restrict_eq_zero, dirac_apply' _ hs, indicator_of_not_mem has]
    -- 🎉 no goals
#align measure_theory.restrict_dirac' MeasureTheory.restrict_dirac'

theorem restrict_dirac [MeasurableSingletonClass α] [Decidable (a ∈ s)] :
    (Measure.dirac a).restrict s = if a ∈ s then Measure.dirac a else 0 := by
  split_ifs with has
  -- ⊢ Measure.restrict (dirac a) s = dirac a
  · apply restrict_eq_self_of_ae_mem
    -- ⊢ ∀ᵐ (x : α) ∂dirac a, x ∈ s
    rwa [ae_dirac_eq]
    -- 🎉 no goals
  · rw [restrict_eq_zero, dirac_apply, indicator_of_not_mem has]
    -- 🎉 no goals
#align measure_theory.restrict_dirac MeasureTheory.restrict_dirac
