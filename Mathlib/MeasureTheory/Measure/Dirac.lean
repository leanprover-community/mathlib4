/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.MeasureTheory.Measure.Typeclasses
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# Dirac measure

In this file we define the Dirac measure `MeasureTheory.Measure.dirac a`
and prove some basic facts about it.
-/

open Function Set
open scoped ENNReal Classical

noncomputable section

variable {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β] {s : Set α} {a : α}

namespace MeasureTheory

namespace Measure

/-- The dirac measure. -/
def dirac (a : α) : Measure α := (OuterMeasure.dirac a).toMeasure (by simp)
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
  refine le_antisymm (this univ trivial ▸ ?_) (this s h ▸ le_dirac_apply)
  rw [← dirac_apply' a MeasurableSet.univ]
  exact measure_mono (subset_univ s)
#align measure_theory.measure.dirac_apply_of_mem MeasureTheory.Measure.dirac_apply_of_mem

@[simp]
theorem dirac_apply [MeasurableSingletonClass α] (a : α) (s : Set α) :
    dirac a s = s.indicator 1 a := by
  by_cases h : a ∈ s; · rw [dirac_apply_of_mem h, indicator_of_mem h, Pi.one_apply]
  rw [indicator_of_not_mem h, ← nonpos_iff_eq_zero]
  calc
    dirac a s ≤ dirac a {a}ᶜ := measure_mono (subset_compl_comm.1 <| singleton_subset_iff.2 h)
    _ = 0 := by simp [dirac_apply' _ (measurableSet_singleton _).compl]
#align measure_theory.measure.dirac_apply MeasureTheory.Measure.dirac_apply

theorem map_dirac {f : α → β} (hf : Measurable f) (a : α) : (dirac a).map f = dirac (f a) :=
  ext fun s hs => by simp [hs, map_apply hf hs, hf hs, indicator_apply]
#align measure_theory.measure.map_dirac MeasureTheory.Measure.map_dirac

lemma map_const (μ : Measure α) (c : β) : μ.map (fun _ ↦ c) = (μ Set.univ) • dirac c := by
  ext s hs
  simp only [aemeasurable_const, measurable_const, Measure.coe_smul, Pi.smul_apply,
    dirac_apply' _ hs, smul_eq_mul]
  classical
  rw [Measure.map_apply measurable_const hs, Set.preimage_const]
  by_cases hsc : c ∈ s
  · rw [(Set.indicator_eq_one_iff_mem _).mpr hsc, mul_one, if_pos hsc]
  · rw [if_neg hsc, (Set.indicator_eq_zero_iff_not_mem _).mpr hsc, measure_empty, mul_zero]

@[simp]
theorem restrict_singleton (μ : Measure α) (a : α) : μ.restrict {a} = μ {a} • dirac a := by
  ext1 s hs
  by_cases ha : a ∈ s
  · have : s ∩ {a} = {a} := by simpa
    simp [*]
  · have : s ∩ {a} = ∅ := inter_singleton_eq_empty.2 ha
    simp [*]
#align measure_theory.measure.restrict_singleton MeasureTheory.Measure.restrict_singleton

/-- If `f` is a map with countable codomain, then `μ.map f` is a sum of Dirac measures. -/
theorem map_eq_sum [Countable β] [MeasurableSingletonClass β] (μ : Measure α) (f : α → β)
    (hf : Measurable f) : μ.map f = sum fun b : β => μ (f ⁻¹' {b}) • dirac b := by
  ext s
  have : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y}) := fun y _ => hf (measurableSet_singleton _)
  simp [← tsum_measure_preimage_singleton (to_countable s) this, *,
    tsum_subtype s fun b => μ (f ⁻¹' {b}), ← indicator_mul_right s fun b => μ (f ⁻¹' {b})]
#align measure_theory.measure.map_eq_sum MeasureTheory.Measure.map_eq_sum

/-- A measure on a countable type is a sum of Dirac measures. -/
@[simp]
theorem sum_smul_dirac [Countable α] [MeasurableSingletonClass α] (μ : Measure α) :
    (sum fun a => μ {a} • dirac a) = μ := by simpa using (map_eq_sum μ id measurable_id).symm
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
#align measure_theory.measure.tsum_indicator_apply_singleton MeasureTheory.Measure.tsum_indicator_apply_singleton

end Measure

open Measure

theorem mem_ae_dirac_iff {a : α} (hs : MeasurableSet s) : s ∈ ae (dirac a) ↔ a ∈ s := by
  by_cases a ∈ s <;> simp [mem_ae_iff, dirac_apply', hs.compl, indicator_apply, *]
#align measure_theory.mem_ae_dirac_iff MeasureTheory.mem_ae_dirac_iff

theorem ae_dirac_iff {a : α} {p : α → Prop} (hp : MeasurableSet { x | p x }) :
    (∀ᵐ x ∂dirac a, p x) ↔ p a :=
  mem_ae_dirac_iff hp
#align measure_theory.ae_dirac_iff MeasureTheory.ae_dirac_iff

@[simp]
theorem ae_dirac_eq [MeasurableSingletonClass α] (a : α) : ae (dirac a) = pure a := by
  ext s
  simp [mem_ae_iff, imp_false]
#align measure_theory.ae_dirac_eq MeasureTheory.ae_dirac_eq

theorem ae_eq_dirac' [MeasurableSingletonClass β] {a : α} {f : α → β} (hf : Measurable f) :
    f =ᵐ[dirac a] const α (f a) :=
  (ae_dirac_iff <| show MeasurableSet (f ⁻¹' {f a}) from hf <| measurableSet_singleton _).2 rfl
#align measure_theory.ae_eq_dirac' MeasureTheory.ae_eq_dirac'

theorem ae_eq_dirac [MeasurableSingletonClass α] {a : α} (f : α → δ) :
    f =ᵐ[dirac a] const α (f a) := by simp [Filter.EventuallyEq]
#align measure_theory.ae_eq_dirac MeasureTheory.ae_eq_dirac

instance Measure.dirac.isProbabilityMeasure {x : α} : IsProbabilityMeasure (dirac x) :=
  ⟨dirac_apply_of_mem <| mem_univ x⟩
#align measure_theory.measure.dirac.is_probability_measure MeasureTheory.Measure.dirac.isProbabilityMeasure

/-! Extra instances to short-circuit type class resolution -/

instance Measure.dirac.instIsFiniteMeasure {a : α} : IsFiniteMeasure (dirac a) := inferInstance
instance Measure.dirac.instSigmaFinite {a : α} : SigmaFinite (dirac a) := inferInstance

theorem restrict_dirac' (hs : MeasurableSet s) [Decidable (a ∈ s)] :
    (Measure.dirac a).restrict s = if a ∈ s then Measure.dirac a else 0 := by
  split_ifs with has
  · apply restrict_eq_self_of_ae_mem
    rw [ae_dirac_iff] <;> assumption
  · rw [restrict_eq_zero, dirac_apply' _ hs, indicator_of_not_mem has]
#align measure_theory.restrict_dirac' MeasureTheory.restrict_dirac'

theorem restrict_dirac [MeasurableSingletonClass α] [Decidable (a ∈ s)] :
    (Measure.dirac a).restrict s = if a ∈ s then Measure.dirac a else 0 := by
  split_ifs with has
  · apply restrict_eq_self_of_ae_mem
    rwa [ae_dirac_eq]
  · rw [restrict_eq_zero, dirac_apply, indicator_of_not_mem has]
#align measure_theory.restrict_dirac MeasureTheory.restrict_dirac

lemma mutuallySingular_dirac [MeasurableSingletonClass α] (x : α) (μ : Measure α) [NoAtoms μ] :
    Measure.dirac x ⟂ₘ μ :=
  ⟨{x}ᶜ, (MeasurableSet.singleton x).compl, by simp, by simp⟩

section dirac_injective

/-- Dirac delta measures at two points are equal if every measurable set contains either both or
neither of the points. -/
lemma dirac_eq_dirac_iff_forall_mem_iff_mem {x y : α} :
    Measure.dirac x = Measure.dirac y ↔ ∀ A, MeasurableSet A → (x ∈ A ↔ y ∈ A) := by
  constructor
  · intro h A A_mble
    have obs := congr_arg (fun μ ↦ μ A) h
    simp only [Measure.dirac_apply' _ A_mble] at obs
    by_cases x_in_A : x ∈ A
    · simpa only [x_in_A, indicator_of_mem, Pi.one_apply, true_iff, Eq.comm (a := (1 : ℝ≥0∞)),
                  indicator_eq_one_iff_mem] using obs
    · simpa only [x_in_A, indicator_of_not_mem, Eq.comm (a := (0 : ℝ≥0∞)), indicator_apply_eq_zero,
                  false_iff, not_false_eq_true, Pi.one_apply, one_ne_zero, imp_false] using obs
  · intro h
    ext A A_mble
    by_cases x_in_A : x ∈ A
    · simp only [Measure.dirac_apply' _ A_mble, x_in_A, indicator_of_mem, Pi.one_apply,
                 (h A A_mble).mp x_in_A]
    · have y_notin_A : y ∉ A := by simp_all only [false_iff, not_false_eq_true]
      simp only [Measure.dirac_apply' _ A_mble, x_in_A, y_notin_A,
                 not_false_eq_true, indicator_of_not_mem]

/-- Dirac delta measures at two points are different if and only if there is a measurable set
containing one of the points but not the other. -/
lemma dirac_ne_dirac_iff_exists_measurableSet {x y : α} :
    Measure.dirac x ≠ Measure.dirac y ↔ ∃ A, MeasurableSet A ∧ x ∈ A ∧ y ∉ A := by
  apply not_iff_not.mp
  simp only [ne_eq, not_not, not_exists, not_and, dirac_eq_dirac_iff_forall_mem_iff_mem]
  refine ⟨fun h A A_mble ↦ by simp only [h A A_mble, imp_self], fun h A A_mble ↦ ?_⟩
  by_cases x_in_A : x ∈ A
  · simp only [x_in_A, h A A_mble x_in_A]
  · simpa only [x_in_A, false_iff] using h Aᶜ (MeasurableSet.compl_iff.mpr A_mble) x_in_A

open MeasurableSpace
/-- Dirac delta measures at two different points are different, assuming the measurable space
separates points. -/
lemma dirac_ne_dirac [SeparatesPoints α] {x y : α} (x_ne_y : x ≠ y) :
    Measure.dirac x ≠ Measure.dirac y := by
  obtain ⟨A, A_mble, x_in_A, y_notin_A⟩ := exists_measurableSet_of_ne x_ne_y
  exact dirac_ne_dirac_iff_exists_measurableSet.mpr ⟨A, A_mble, x_in_A, y_notin_A⟩

/-- Dirac delta measures at two points are different if and only if the two points are different,
assuming the measurable space separates points. -/
lemma dirac_ne_dirac_iff [SeparatesPoints α] {x y : α} :
    Measure.dirac x ≠ Measure.dirac y ↔ x ≠ y :=
  ⟨fun h x_eq_y ↦ h <| congrArg dirac x_eq_y, fun h ↦ dirac_ne_dirac h⟩

/-- Dirac delta measures at two points are equal if and only if the two points are equal,
assuming the measurable space separates points. -/
lemma dirac_eq_dirac_iff [SeparatesPoints α] {x y : α} :
    Measure.dirac x = Measure.dirac y ↔ x = y := not_iff_not.mp dirac_ne_dirac_iff

/-- The assignment `x ↦ dirac x` is injective, assuming the measurable space separates points. -/
lemma injective_dirac [SeparatesPoints α] :
    Function.Injective (fun (x : α) ↦ dirac x) := fun x y x_ne_y ↦ by rwa [← dirac_eq_dirac_iff]

end dirac_injective
