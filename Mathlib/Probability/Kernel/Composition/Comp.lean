/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Composition of kernels

We define the composition `η ∘ₖ κ` of kernels `κ : Kernel α β` and `η : Kernel β γ`, which is
a kernel from `α` to `γ`.

## Main definitions

* `comp (η : Kernel β γ) (κ : Kernel α β) : Kernel α γ`: composition of 2 kernels.
  We define a notation `η ∘ₖ κ = comp η κ`.
  `∫⁻ c, g c ∂((η ∘ₖ κ) a) = ∫⁻ b, ∫⁻ c, g c ∂(η b) ∂(κ a)`

## Main statements

* `lintegral_comp`: Lebesgue integral of a function against a composition of kernels.
* Instances stating that `IsMarkovKernel`, `IsZeroOrMarkovKernel`, `IsFiniteKernel` and
  `IsSFiniteKernel` are stable by composition.

## Notations

* `η ∘ₖ κ = ProbabilityTheory.Kernel.comp η κ`

-/


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

/-- Composition of two kernels. -/
noncomputable def comp (η : Kernel β γ) (κ : Kernel α β) : Kernel α γ where
  toFun a := (κ a).bind η
  measurable' := (Measure.measurable_bind' η.measurable).comp κ.measurable

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ∘ₖ " => ProbabilityTheory.Kernel.comp

theorem comp_apply (η : Kernel β γ) (κ : Kernel α β) (a : α) : (η ∘ₖ κ) a = (κ a).bind η :=
  rfl

theorem comp_apply' (η : Kernel β γ) (κ : Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) :
    (η ∘ₖ κ) a s = ∫⁻ b, η b s ∂κ a := by
  rw [comp_apply, Measure.bind_apply hs (Kernel.aemeasurable _)]

theorem comp_apply_univ_le (κ : Kernel α β) (η : Kernel β γ) (a : α) :
    (η ∘ₖ κ) a Set.univ ≤ κ a Set.univ * IsFiniteKernel.bound η := by
  rw [comp_apply' _ _ _ .univ]
  let Cη := IsFiniteKernel.bound η
  calc
    ∫⁻ b, η b Set.univ ∂κ a ≤ ∫⁻ _, Cη ∂κ a :=
      lintegral_mono fun b => measure_le_bound η b Set.univ
    _ = Cη * κ a Set.univ := MeasureTheory.lintegral_const Cη
    _ = κ a Set.univ * Cη := mul_comm _ _

@[simp] lemma zero_comp (κ : Kernel α β) : (0 : Kernel β γ) ∘ₖ κ = 0 := by ext; simp [comp_apply]

@[simp] lemma comp_zero (κ : Kernel β γ) : κ ∘ₖ (0 : Kernel α β) = 0 := by ext; simp [comp_apply]

section Ae

/-! ### `ae` filter of the composition -/

variable {κ : Kernel α β} {η : Kernel β γ} {a : α} {s : Set γ}

theorem ae_lt_top_of_comp_ne_top (a : α) (hs : (η ∘ₖ κ) a s ≠ ∞) : ∀ᵐ b ∂κ a, η b s < ∞ := by
  have h : ∀ᵐ b ∂κ a, η b (toMeasurable ((η ∘ₖ κ) a) s) < ∞ := by
    refine ae_lt_top (Kernel.measurable_coe η (measurableSet_toMeasurable ..)) ?_
    rwa [← Kernel.comp_apply' _ _ _ (measurableSet_toMeasurable ..), measure_toMeasurable]
  filter_upwards [h] with b hb using (measure_mono (subset_toMeasurable _ _)).trans_lt hb

theorem comp_null (a : α) (hs : MeasurableSet s) :
    (η ∘ₖ κ) a s = 0 ↔ (fun y ↦ η y s) =ᵐ[κ a] 0 := by
  rw [comp_apply' _ _ _ hs, lintegral_eq_zero_iff (η.measurable_coe hs)]

theorem ae_null_of_comp_null (h : (η ∘ₖ κ) a s = 0) : (η · s) =ᵐ[κ a] 0 := by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  simp_rw [comp_null a mt] at ht
  rw [Filter.eventuallyLE_antisymm_iff]
  exact ⟨Filter.EventuallyLE.trans_eq (ae_of_all _ fun _ ↦ measure_mono hst) ht,
    ae_of_all _ fun _ ↦ zero_le _⟩

variable {p : γ → Prop}

theorem ae_ae_of_ae_comp (h : ∀ᵐ z ∂(η ∘ₖ κ) a, p z) :
    ∀ᵐ y ∂κ a, ∀ᵐ z ∂η y, p z := ae_null_of_comp_null h

lemma ae_comp_of_ae_ae (hp : MeasurableSet {z | p z})
    (h : ∀ᵐ y ∂κ a, ∀ᵐ z ∂η y, p z) : ∀ᵐ z ∂(η ∘ₖ κ) a, p z := by
  rwa [ae_iff, comp_null] at *
  exact hp.compl

lemma ae_comp_iff (hp : MeasurableSet {z | p z}) :
    (∀ᵐ z ∂(η ∘ₖ κ) a, p z) ↔ ∀ᵐ y ∂κ a, ∀ᵐ z ∂η y, p z :=
  ⟨ae_ae_of_ae_comp, ae_comp_of_ae_ae hp⟩

end Ae

section Restrict

variable {κ : Kernel α β} {η : Kernel β γ}

theorem comp_restrict {s : Set γ} (hs : MeasurableSet s) :
    η.restrict hs ∘ₖ κ = (η ∘ₖ κ).restrict hs := by
  ext a t ht
  simp_rw [comp_apply' _ _ _ ht, restrict_apply' _ _ _ ht, comp_apply' _ _ _ (ht.inter hs)]

end Restrict

theorem lintegral_comp (η : Kernel β γ) (κ : Kernel α β) (a : α) {g : γ → ℝ≥0∞}
    (hg : Measurable g) : ∫⁻ c, g c ∂(η ∘ₖ κ) a = ∫⁻ b, ∫⁻ c, g c ∂η b ∂κ a := by
  rw [comp_apply, Measure.lintegral_bind (Kernel.aemeasurable _) hg.aemeasurable]

/-- Composition of kernels is associative. -/
theorem comp_assoc {δ : Type*} {mδ : MeasurableSpace δ} (ξ : Kernel γ δ)
    (η : Kernel β γ) (κ : Kernel α β) : ξ ∘ₖ η ∘ₖ κ = ξ ∘ₖ (η ∘ₖ κ) := by
  refine ext_fun fun a f hf => ?_
  simp_rw [lintegral_comp _ _ _ hf, lintegral_comp _ _ _ hf.lintegral_kernel]

lemma comp_discard' (κ : Kernel α β) :
    discard β ∘ₖ κ =
      { toFun a := κ a .univ • Measure.dirac ()
        measurable' := (κ.measurable_coe .univ).smul_measure _ } := by
  ext a s hs
  simp [comp_apply' _ _ _ hs, mul_comm]

@[simp]
lemma comp_discard (κ : Kernel α β) [IsMarkovKernel κ] : discard β ∘ₖ κ = discard α := by
  ext; simp [comp_discard']

@[simp]
lemma swap_copy : (swap α α) ∘ₖ (copy α) = copy α := by
  ext a s hs
  rw [comp_apply, copy_apply, Measure.dirac_bind (Kernel.measurable _), swap_apply' _ hs,
    Measure.dirac_apply' _ hs]
  congr

lemma const_comp (μ : Measure γ) (κ : Kernel α β) :
    const β μ ∘ₖ κ = fun a ↦ (κ a) Set.univ • μ := by
  ext _ _ hs
  simp_rw [comp_apply' _ _ _ hs, const_apply, MeasureTheory.lintegral_const, Measure.smul_apply,
    smul_eq_mul, mul_comm]

@[simp]
lemma const_comp' (μ : Measure γ) (κ : Kernel α β) [IsMarkovKernel κ] :
    const β μ ∘ₖ κ = const α μ := by
  ext; simp_rw [const_comp, measure_univ, one_smul, const_apply]

lemma comp_add_right (μ κ : Kernel α β) (η : Kernel β γ) :
    η ∘ₖ (μ + κ) = η ∘ₖ μ + η ∘ₖ κ := by ext _ _ hs; simp [comp_apply' _ _ _ hs]

lemma comp_add_left (μ : Kernel α β) (κ η : Kernel β γ) :
    (κ + η) ∘ₖ μ = κ ∘ₖ μ + η ∘ₖ μ := by
  ext a s hs
  simp_rw [comp_apply' _ _ _ hs, add_apply, Measure.add_apply, comp_apply' _ _ _ hs,
    lintegral_add_left (Kernel.measurable_coe κ hs)]

lemma comp_sum_right {ι : Type*} [Countable ι] (κ : ι → Kernel α β) (η : Kernel β γ) :
    η ∘ₖ Kernel.sum κ = Kernel.sum fun i ↦ η ∘ₖ (κ i) := by
  ext _ _ hs
  simp_rw [sum_apply, comp_apply' _ _ _ hs, Measure.sum_apply _ hs, sum_apply,
    lintegral_sum_measure, comp_apply' _ _ _ hs]

lemma comp_sum_left {ι : Type*} [Countable ι] (κ : Kernel α β) (η : ι → Kernel β γ) :
    (Kernel.sum η) ∘ₖ κ = Kernel.sum (fun i ↦ (η i) ∘ₖ κ) := by
  ext _ _ hs
  simp_rw [sum_apply, comp_apply' _ _ _ hs, sum_apply, Measure.sum_apply _ hs,
    comp_apply' _ _ _ hs]
  rw [lintegral_tsum]
  exact fun _ ↦ (Kernel.measurable_coe _ hs).aemeasurable

instance IsMarkovKernel.comp (η : Kernel β γ) [IsMarkovKernel η] (κ : Kernel α β)
    [IsMarkovKernel κ] : IsMarkovKernel (η ∘ₖ κ) where
  isProbabilityMeasure a := by
    rw [comp_apply]
    constructor
    rw [Measure.bind_apply .univ η.aemeasurable]
    simp

instance IsZeroOrMarkovKernel.comp (κ : Kernel α β) [IsZeroOrMarkovKernel κ]
    (η : Kernel β γ) [IsZeroOrMarkovKernel η] : IsZeroOrMarkovKernel (η ∘ₖ κ) := by
  obtain rfl | _ := eq_zero_or_isMarkovKernel κ <;> obtain rfl | _ := eq_zero_or_isMarkovKernel η
  all_goals simpa using by infer_instance

instance IsFiniteKernel.comp (η : Kernel β γ) [IsFiniteKernel η] (κ : Kernel α β)
    [IsFiniteKernel κ] : IsFiniteKernel (η ∘ₖ κ) := by
  refine ⟨⟨IsFiniteKernel.bound κ * IsFiniteKernel.bound η,
    ENNReal.mul_lt_top (IsFiniteKernel.bound_lt_top κ) (IsFiniteKernel.bound_lt_top η),
    fun a ↦ ?_⟩⟩
  calc (η ∘ₖ κ) a Set.univ
  _ ≤ κ a Set.univ * IsFiniteKernel.bound η := comp_apply_univ_le κ η a
  _ ≤ IsFiniteKernel.bound κ * IsFiniteKernel.bound η :=
    mul_le_mul (measure_le_bound κ a Set.univ) le_rfl (zero_le _) (zero_le _)

instance IsSFiniteKernel.comp (η : Kernel β γ) [IsSFiniteKernel η] (κ : Kernel α β)
    [IsSFiniteKernel κ] : IsSFiniteKernel (η ∘ₖ κ) := by
  simp_rw [← kernel_sum_seq κ, ← kernel_sum_seq η, comp_sum_left, comp_sum_right]
  infer_instance

end Kernel
end ProbabilityTheory
