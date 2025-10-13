/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Dirac measure

In this file we define the Dirac measure `MeasureTheory.Measure.dirac a`
and prove some basic facts about it.
-/

open Function Set
open scoped ENNReal

noncomputable section

variable {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β] {s : Set α} {a : α}

namespace MeasureTheory

namespace Measure

/-- The dirac measure. -/
def dirac (a : α) : Measure α := (OuterMeasure.dirac a).toMeasure (by simp)

instance : MeasureSpace PUnit :=
  ⟨dirac PUnit.unit⟩

theorem le_dirac_apply {a} : s.indicator 1 a ≤ dirac a s :=
  OuterMeasure.dirac_apply a s ▸ le_toMeasure_apply _ _ _

@[simp]
theorem dirac_apply' (a : α) (hs : MeasurableSet s) : dirac a s = s.indicator 1 a :=
  toMeasure_apply _ _ hs

theorem dirac_apply_eq_zero_or_one :
    dirac a s = 0 ∨ dirac a s = 1 := by
  rw [← measure_toMeasurable s, dirac_apply' a (measurableSet_toMeasurable ..), indicator]
  simp only [Pi.one_apply, ite_eq_right_iff, one_ne_zero, imp_false, ite_eq_left_iff, zero_ne_one,
    not_not]
  tauto

@[simp]
theorem dirac_apply_ne_zero_iff_eq_one :
    dirac a s ≠ 0 ↔ dirac a s = 1 where
  mp := dirac_apply_eq_zero_or_one.resolve_left
  mpr := ne_zero_of_eq_one

@[simp]
theorem dirac_apply_ne_one_iff_eq_zero :
    dirac a s ≠ 1 ↔ dirac a s = 0 where
  mp := dirac_apply_eq_zero_or_one.resolve_right
  mpr h := h ▸ zero_ne_one

@[simp]
theorem dirac_apply_of_mem {a : α} (h : a ∈ s) : dirac a s = 1 := by
  have : ∀ t : Set α, a ∈ t → t.indicator (1 : α → ℝ≥0∞) a = 1 := fun t ht => indicator_of_mem ht 1
  refine le_antisymm (this univ trivial ▸ ?_) (this s h ▸ le_dirac_apply)
  rw [← dirac_apply' a MeasurableSet.univ]
  exact measure_mono (subset_univ s)

@[simp]
theorem dirac_apply [MeasurableSingletonClass α] (a : α) (s : Set α) :
    dirac a s = s.indicator 1 a := by
  by_cases h : a ∈ s; · rw [dirac_apply_of_mem h, indicator_of_mem h, Pi.one_apply]
  rw [indicator_of_notMem h, ← nonpos_iff_eq_zero]
  calc
    dirac a s ≤ dirac a {a}ᶜ := measure_mono (subset_compl_comm.1 <| singleton_subset_iff.2 h)
    _ = 0 := by simp [dirac_apply' _ (measurableSet_singleton _).compl]

@[simp] lemma dirac_ne_zero : dirac a ≠ 0 :=
  fun h ↦ by simpa [h] using dirac_apply_of_mem (mem_univ a)

theorem map_dirac {f : α → β} (hf : Measurable f) (a : α) : (dirac a).map f = dirac (f a) := by
  classical
  exact ext fun s hs => by simp [hs, map_apply hf hs, hf hs, indicator_apply]

@[simp]
lemma map_const (μ : Measure α) (c : β) : μ.map (fun _ ↦ c) = (μ Set.univ) • dirac c := by
  ext s hs
  simp only [Measure.coe_smul, Pi.smul_apply,
    dirac_apply' _ hs, smul_eq_mul]
  classical
  rw [Measure.map_apply measurable_const hs, Set.preimage_const]
  by_cases hsc : c ∈ s
  · rw [(Set.indicator_eq_one_iff_mem _).mpr hsc, mul_one, if_pos hsc]
  · rw [if_neg hsc, (Set.indicator_eq_zero_iff_notMem _).mpr hsc, measure_empty, mul_zero]

@[simp]
theorem restrict_singleton (μ : Measure α) (a : α) : μ.restrict {a} = μ {a} • dirac a := by
  ext1 s hs
  by_cases ha : a ∈ s
  · have : s ∩ {a} = {a} := by simpa
    simp [*]
  · have : s ∩ {a} = ∅ := inter_singleton_eq_empty.2 ha
    simp [*]

/-- Two measures on a countable space are equal if they agree on singletons. -/
theorem ext_of_singleton [Countable α] {μ ν : Measure α} (h : ∀ a, μ {a} = ν {a}) : μ = ν :=
  ext_of_sUnion_eq_univ (countable_range singleton) (by aesop) (by aesop)

/-- Two measures on a countable space are equal if and only if they agree on singletons. -/
theorem ext_iff_singleton [Countable α] {μ ν : Measure α} : μ = ν ↔ ∀ a, μ {a} = ν {a} :=
  ⟨fun h _ ↦ h ▸ rfl, ext_of_singleton⟩

theorem _root_.MeasureTheory.ext_iff_measureReal_singleton [Countable α]
    {μ1 μ2 : Measure α} [SigmaFinite μ1] [SigmaFinite μ2] :
    μ1 = μ2 ↔ ∀ x, μ1.real {x} = μ2.real {x} := by
  rw [Measure.ext_iff_singleton]
  congr! with x
  rw [measureReal_def, measureReal_def, ENNReal.toReal_eq_toReal_iff]
  simp [measure_singleton_lt_top, ne_of_lt]

/-- If `f` is a map with countable codomain, then `μ.map f` is a sum of Dirac measures. -/
theorem map_eq_sum [Countable β] [MeasurableSingletonClass β] (μ : Measure α) (f : α → β)
    (hf : Measurable f) : μ.map f = sum fun b : β => μ (f ⁻¹' {b}) • dirac b := by
  ext s
  have : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y}) := fun y _ => hf (measurableSet_singleton _)
  simp [← tsum_measure_preimage_singleton (to_countable s) this, *,
    tsum_subtype s fun b => μ (f ⁻¹' {b}), ← indicator_mul_right s fun b => μ (f ⁻¹' {b})]

/-- A measure on a countable type is a sum of Dirac measures. -/
@[simp]
theorem sum_smul_dirac [Countable α] [MeasurableSingletonClass α] (μ : Measure α) :
    (sum fun a => μ {a} • dirac a) = μ := by simpa using (map_eq_sum μ id measurable_id).symm

/-- A measure on a countable type is a sum of Dirac measures.
If `α` has measurable singletons, `sum_smul_dirac` gives a simpler sum. -/
lemma exists_sum_smul_dirac [Countable α] (μ : Measure α) :
    ∃ s : Set α, μ = Measure.sum (fun x : s ↦ μ (measurableAtom x) • dirac (x : α)) := by
  let measurableAtoms := measurableAtom '' (Set.univ : Set α)
  have h_nonempty (s : measurableAtoms) : Set.Nonempty s.1 := by
    obtain ⟨y, _, hy⟩ := s.2
    rw [← hy]
    exact ⟨y, mem_measurableAtom_self y⟩
  let points : measurableAtoms → α := fun s ↦ (h_nonempty s).some
  have h_points_mem (s : measurableAtoms) : points s ∈ s.1 := (h_nonempty s).some_mem
  refine ⟨Set.range points, ext_of_measurableAtoms fun x ↦ ?_⟩
  rw [sum_apply _ (MeasurableSet.measurableAtom_of_countable x)]
  simp only [Measure.smul_apply, smul_eq_mul]
  simp_rw [dirac_apply' _ (MeasurableSet.measurableAtom_of_countable x)]
  rw [tsum_eq_single ⟨points ⟨measurableAtom x, by simp [measurableAtoms]⟩, by simp⟩]
  · rw [indicator_of_mem]
    · simp only [Pi.one_apply, mul_one]
      congr
      refine (measurableAtom_eq_of_mem ?_).symm
      convert h_points_mem _
      simp
    · convert h_points_mem _
      simp
  · simp only [ne_eq, mul_eq_zero, indicator_apply_eq_zero, Pi.one_apply, one_ne_zero, imp_false,
      Subtype.forall, Set.mem_range, Subtype.exists, Subtype.mk.injEq, forall_exists_index]
    refine fun y s hs hsy hyx ↦ .inr fun hyx' ↦ hyx ?_
    rw [← hsy]
    congr
    have h1 : measurableAtom y = measurableAtom x := measurableAtom_eq_of_mem hyx'
    have h2 : measurableAtom y = s := by
      specialize h_points_mem ⟨s, hs⟩
      obtain ⟨z, _, hz⟩ := hs
      simp only at h_points_mem
      rw [← hz, ← hsy]
      refine measurableAtom_eq_of_mem ?_
      convert h_points_mem
    rw [← h2, h1]

/-- Given that `α` is a countable, measurable space with all singleton sets measurable,
write the measure of a set `s` as the sum of the measure of `{x}` for all `x ∈ s`. -/
theorem tsum_indicator_apply_singleton [Countable α] [MeasurableSingletonClass α] (μ : Measure α)
    (s : Set α) (hs : MeasurableSet s) : (∑' x : α, s.indicator (fun x => μ {x}) x) = μ s := by
  classical
  calc
    (∑' x : α, s.indicator (fun x => μ {x}) x) =
      Measure.sum (fun a => μ {a} • Measure.dirac a) s := by
      simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
        Set.indicator_apply, mul_ite, Pi.one_apply, mul_one, mul_zero]
    _ = μ s := by rw [μ.sum_smul_dirac]

end Measure

open Measure

theorem mem_ae_dirac_iff {a : α} (hs : MeasurableSet s) : s ∈ ae (dirac a) ↔ a ∈ s := by
  by_cases a ∈ s <;> simp [mem_ae_iff, dirac_apply', hs.compl, *]

theorem ae_dirac_iff {a : α} {p : α → Prop} (hp : MeasurableSet { x | p x }) :
    (∀ᵐ x ∂dirac a, p x) ↔ p a :=
  mem_ae_dirac_iff hp

@[simp]
theorem ae_dirac_eq [MeasurableSingletonClass α] (a : α) : ae (dirac a) = pure a := by
  ext s
  simp [mem_ae_iff, imp_false]

theorem ae_eq_dirac' [MeasurableSingletonClass β] {a : α} {f : α → β} (hf : Measurable f) :
    f =ᵐ[dirac a] const α (f a) :=
  (ae_dirac_iff <| show MeasurableSet (f ⁻¹' {f a}) from hf <| measurableSet_singleton _).2 rfl

theorem ae_eq_dirac [MeasurableSingletonClass α] {a : α} (f : α → δ) :
    f =ᵐ[dirac a] const α (f a) := by simp [Filter.EventuallyEq]

@[fun_prop]
lemma aemeasurable_dirac [MeasurableSingletonClass α] {a : α} {f : α → β} :
    AEMeasurable f (Measure.dirac a) :=
  ⟨fun _ ↦ f a, measurable_const, ae_eq_dirac f⟩

instance Measure.dirac.isProbabilityMeasure {x : α} : IsProbabilityMeasure (dirac x) :=
  ⟨dirac_apply_of_mem <| mem_univ x⟩

/-! Extra instances to short-circuit type class resolution -/

instance Measure.dirac.instIsFiniteMeasure {a : α} : IsFiniteMeasure (dirac a) := inferInstance
instance Measure.dirac.instSigmaFinite {a : α} : SigmaFinite (dirac a) := inferInstance

theorem dirac_eq_one_iff_mem (hs : MeasurableSet s) : dirac a s = 1 ↔ a ∈ s := by
  rw [← prob_compl_eq_zero_iff hs, ← mem_ae_iff]
  apply mem_ae_dirac_iff hs

theorem dirac_eq_zero_iff_not_mem (hs : MeasurableSet s) : dirac a s = 0 ↔ a ∉ s := by
  rw [← compl_compl s, ← mem_ae_iff, notMem_compl_iff]
  apply mem_ae_dirac_iff (MeasurableSet.compl_iff.mpr hs)

theorem restrict_dirac' (hs : MeasurableSet s) [Decidable (a ∈ s)] :
    (Measure.dirac a).restrict s = if a ∈ s then Measure.dirac a else 0 := by
  split_ifs with has
  · apply restrict_eq_self_of_ae_mem
    rw [ae_dirac_iff] <;> assumption
  · rw [restrict_eq_zero, dirac_apply' _ hs, indicator_of_notMem has]

theorem restrict_dirac [MeasurableSingletonClass α] [Decidable (a ∈ s)] :
    (Measure.dirac a).restrict s = if a ∈ s then Measure.dirac a else 0 := by
  split_ifs with has
  · apply restrict_eq_self_of_ae_mem
    rwa [ae_dirac_eq]
  · rw [restrict_eq_zero, dirac_apply, indicator_of_notMem has]

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
    · simpa only [x_in_A, indicator_of_notMem, Eq.comm (a := (0 : ℝ≥0∞)), indicator_apply_eq_zero,
                  false_iff, not_false_eq_true, Pi.one_apply, one_ne_zero, imp_false] using obs
  · intro h
    ext A A_mble
    by_cases x_in_A : x ∈ A
    · simp only [Measure.dirac_apply' _ A_mble, x_in_A, indicator_of_mem, Pi.one_apply,
                 (h A A_mble).mp x_in_A]
    · have y_notin_A : y ∉ A := by simp_all only [not_false_eq_true]
      simp only [Measure.dirac_apply' _ A_mble, x_in_A, y_notin_A,
                 not_false_eq_true, indicator_of_notMem]

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

end MeasureTheory
