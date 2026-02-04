/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Notation

import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.RadonNikodym

/-!
# Chain rule for the Kullback-Leibler divergence

Suppose that we have two finite joint measures on a product `α × β`, which can be decomposed as
`μ ⊗ₘ κ` and `ν ⊗ₘ η`, where `μ` and `ν` are measures on `α` and `κ` and `η` are Markov kernels
from `α` to `β`. Then we can express the Kullback-Leibler divergence between these two joint
measures as a sum of `klDiv μ ν` and the conditional Kullback-Leibler divergence between the kernels
`κ` and `η`, averaged over `μ`. The resulting equality is most often written as
`klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + μ[fun x ↦ klDiv (κ x) (η x)]`.

Here we first prove the following version:
`klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`.
This version avoids the issue of measurability of the function `x ↦ klDiv (κ x) (η x)`, which is not
always guaranteed, and thus holds for all measurable spaces `α` and `β`, without any assumptions.

## Main statements

* `klDiv_compProd_eq_add`: `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`

## Proof

The Kullback-Leibler divergence `klDiv μ ν` is defined with an if-then-else statement:
if the measures are absolutely continuous (`μ ≪ ν`) and the log-likelihood ratio `llr μ ν` is
integrable, then it is defined as `∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ`, otherwise
it is defined to be `∞`.

We first deal with the case in which absolute continuity does not hold. The crucial observation is
that `μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ μ ≪ ν ∧ μ ⊗ₘ κ ≪ μ ⊗ₘ η`, which means that if one of the two sides of the
KL equality is infinite because of lack of absolute continuity, then the other side is also infinite
for the same reason.

Then, we deal with the case in which absolute continuity holds but integrability does not. Again,
we can show a similar equivalence for integrability, which allows us to conclude that both sides
are infinite.
`Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)` is equivalent to
`Integrable (llr μ ν) μ ∧ Integrable (llr (μ ⊗ₘ κ) (μ ⊗ₘ η)) (μ ⊗ₘ κ)`.
This is harder to prove than the absolute continuity and relies on the convexity of
the function `x ↦ x * log x`.

Finally, we prove the equality in the case in which both absolute continuity and integrability hold.
In that case, `klDiv μ ν = ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ` and similarly for
the other terms. It is easy to see that it suffices to prove the equality of the integrals parts.
The main ingredient is the chain rule for Radon-Nikodym derivatives:
`∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) = ∂μ/∂ν * ∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)`.
Finally, the computation for the integral of the log-likelihood ratio is as follows:
```
∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂(μ ⊗ₘ κ)
_ = ∫ p, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal * log ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal ∂(ν ⊗ₘ η)
_ = ∫ p, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal *
    (log ((∂μ/∂ν) p.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal) ∂(ν ⊗ₘ η)
_ = ∫ p, (log ((∂μ/∂ν) p.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal) ∂(μ ⊗ₘ κ)
_ = ∫ p, log ((∂μ/∂ν) p.1).toReal ∂(μ ⊗ₘ κ) + ∫ p, log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal ∂(μ ⊗ₘ κ)
_ = ∫ a, llr μ ν a ∂μ + ∫ p, llr (μ ⊗ₘ κ) (μ ⊗ₘ η) p ∂(μ ⊗ₘ κ)
```

## TODO

Add a version of the chain rule for the integral form of the contional KL divergence, i.e.
`μ[fun x ↦ klDiv (κ x) (η x)]`.

-/

@[expose] public section

open Real MeasureTheory Set ProbabilityTheory

open scoped ENNReal

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β}

section ConvexOn

variable {f g : ℝ → ℝ} {s : Set ℝ} {x : ℝ}

lemma _root_.ConvexOn.affine_le_of_mem_interior (hf : ConvexOn ℝ s f) {x y : ℝ}
    (hx : x ∈ interior s) (hy : y ∈ s) :
    derivWithin f (Set.Ioi x) x * y + (f x - derivWithin f (Set.Ioi x) x * x) ≤ f y := by
  rw [add_comm]
  rcases lt_trichotomy x y with hxy | h_eq | hyx
  · have : derivWithin f (Set.Ioi x) x ≤ slope f x y :=
      hf.rightDeriv_le_slope_of_mem_interior hx hy hxy
    rw [slope_def_field] at this
    rwa [le_div_iff₀ (by simp [hxy]), le_sub_iff_add_le, add_comm, mul_sub, add_sub,
      add_sub_right_comm] at this
  · simp [h_eq]
  · have : slope f x y ≤ derivWithin f (Set.Ioi x) x := by
      have := (hf.slope_le_leftDeriv_of_mem_interior hy hx hyx).trans
        (hf.leftDeriv_le_rightDeriv_of_mem_interior hx)
      rwa [slope_comm]
    rw [slope_def_field] at this
    rw [← neg_div_neg_eq, neg_sub, neg_sub] at this
    rwa [div_le_iff₀ (by simp [hyx]), sub_le_iff_le_add, mul_sub, ← sub_le_iff_le_add',
      sub_sub_eq_add_sub, add_sub_right_comm] at this

lemma _root_.Convex.subsingleton_of_interior_eq_empty (hs : Convex ℝ s) (h : interior s = ∅) :
    s.Subsingleton := by
  intro x hx y hy
  by_contra h_ne
  wlog h_lt : x < y
  · refine this hs h hy hx (Ne.symm h_ne) ?_
    exact lt_of_le_of_ne (not_lt.mp h_lt) (Ne.symm h_ne)
  · have h_subset : Set.Icc x y ⊆ s := by
      rw [← segment_eq_Icc h_lt.le]
      exact hs.segment_subset hx hy
    have : Set.Ioo x y ⊆ interior s := by
      rw [← interior_Icc]
      exact interior_mono h_subset
    simp only [h, Set.subset_empty_iff, Set.Ioo_eq_empty_iff] at this
    exact this h_lt

lemma _root_.ConvexOn.exists_affine_le (hf : ConvexOn ℝ s f) (hs : Convex ℝ s) :
    ∃ c c', ∀ x ∈ s, c * x + c' ≤ f x := by
  cases Set.eq_empty_or_nonempty (interior s) with
  | inl h => -- there is at most one point in `s`
    have hs_sub : s.Subsingleton := hs.subsingleton_of_interior_eq_empty h
    cases Set.eq_empty_or_nonempty s with
    | inl h' => simp [h']
    | inr h' => -- there is exactly one point in `s`
      obtain ⟨x, hxs⟩ := h'
      refine ⟨0, f x, fun y hys ↦ ?_⟩
      simp [hs_sub hxs hys]
  | inr h => -- there is a point in the interior of `s`
    obtain ⟨x, hx⟩ := h
    refine ⟨derivWithin f (Set.Ioi x) x, f x - derivWithin f (Set.Ioi x) x * x, fun y hy ↦ ?_⟩
    exact hf.affine_le_of_mem_interior hx hy

end ConvexOn

variable (ν) in
lemma ae_rnDeriv_ne_zero_imp_of_ae_aux [SigmaFinite μ] [SigmaFinite ν] {p : α → Prop}
    (h : ∀ᵐ a ∂μ, p a) :
    ∀ᵐ a ∂ν, μ.rnDeriv ν a ≠ 0 → p a := by
  rw [ν.haveLebesgueDecomposition_add μ, ae_add_measure_iff]
  constructor
  · rw [← ν.haveLebesgueDecomposition_add μ]
    have : ∀ᵐ x ∂(ν.singularPart μ), μ.rnDeriv ν x = 0 := μ.rnDeriv_eq_zero_ae_singularPart ν
    filter_upwards [this] with x hx h_absurd using absurd hx h_absurd
  · have h_ac : μ.withDensity (ν.rnDeriv μ) ≪ μ := withDensity_absolutelyContinuous _ _
    rw [← ν.haveLebesgueDecomposition_add μ]
    suffices ∀ᵐx ∂μ, μ.rnDeriv ν x ≠ 0 → p x from h_ac this
    filter_upwards [h] with _ h _ using h

lemma ae_rnDeriv_ne_zero_imp_of_ae [SigmaFinite μ] [SigmaFinite ν] {p : α → Prop}
    (h : ∀ᵐ a ∂μ, p a) :
    ∀ᵐ a ∂ν, μ.rnDeriv ν a ≠ 0 → p a := by
  suffices ∀ᵐ a ∂ν, (ν.withDensity (μ.rnDeriv ν)).rnDeriv ν a ≠ 0 → p a by
    have h := ν.rnDeriv_withDensity (μ.measurable_rnDeriv ν)
    filter_upwards [this, h] with x hx1 hx2
    rwa [hx2] at hx1
  refine ae_rnDeriv_ne_zero_imp_of_ae_aux ν ?_
  exact (Measure.absolutelyContinuous_of_le (μ.withDensity_rnDeriv_le ν)) h

section Integrable

variable {E : Type*} {f g : ℝ → ℝ}

lemma _root_.ConvexOn.apply_rnDeriv_ae_le_integral [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    (fun a ↦ f ((∂μ/∂ν) a).toReal)
      ≤ᵐ[ν] fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂(η a) := by
  have h_compProd : (fun p ↦ (∂μ/∂ν) p.1 * (∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p) =ᵐ[ν ⊗ₘ η]
      ∂μ ⊗ₘ κ/∂ν ⊗ₘ η := (rnDeriv_compProd hκη ν).symm
  have h_lt_top := Measure.ae_ae_of_ae_compProd <| (μ ⊗ₘ κ).rnDeriv_lt_top (ν ⊗ₘ η)
  have h_integrable := Measure.integrable_toReal_rnDeriv (μ := μ ⊗ₘ κ) (ν := ν ⊗ₘ η)
  rw [Measure.integrable_compProd_iff] at h_integrable h_int
  rotate_left
  · exact (hf.comp_measurable (by fun_prop)).aestronglyMeasurable
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  have h_ae1 : ∀ᵐ a ∂ν, (∂μ/∂ν) a * ∫⁻ b, (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, b) ∂(η a) = (∂μ/∂ν) a := by
    suffices ∀ᵐ a ∂ν, (∂μ/∂ν) a ≠ 0 → ∫⁻ b, (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, b) ∂(η a) = 1 by
      filter_upwards [this] with a ha
      by_cases h0 : (∂μ/∂ν) a = 0
      · simp [h0]
      · rw [ha h0, mul_one]
    refine ae_rnDeriv_ne_zero_imp_of_ae ?_
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) measurable_const ?_
    intro s hs hsμ
    simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter, one_mul]
    calc ∫⁻ a in s, ∫⁻ b, (∂μ ⊗ₘ κ/∂μ ⊗ₘ η) (a, b) ∂η a ∂μ
    _ = ∫⁻ a in s, ∫⁻ b in univ, (∂μ ⊗ₘ κ/∂μ ⊗ₘ η) (a, b) ∂η a ∂μ := by simp
    _ = μ s := by
      rw [← Measure.setLIntegral_compProd (by fun_prop) hs .univ, Measure.setLIntegral_rnDeriv hκη,
        Measure.compProd_apply_prod hs .univ]
      simp
  have h_ae2 : ∀ᵐ a ∂ν, ∀ᵐ b ∂(η a), (∂μ/∂ν) a * (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, b) =
      (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b) := by
    rwa [Filter.EventuallyEq, Measure.ae_compProd_iff] at h_compProd
    simp only [measurableSet_setOf]
    fun_prop
  filter_upwards [h_ae1, h_ae2, h_lt_top, h_integrable.1, h_int.1]
    with a h_eq_one h_mul_eq h_lt_top h_int' h_int
  calc f ((∂μ/∂ν) a).toReal
    = f ((∂μ/∂ν) a * ∫⁻ b, (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, b) ∂(η a)).toReal := by simp [h_eq_one]
  _ = f (∫⁻ b, (∂μ/∂ν) a * (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, b) ∂(η a)).toReal := by
    rw [lintegral_const_mul _ (by fun_prop)]
  _ = f (∫⁻ b, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b) ∂η a).toReal := by
    congr 2
    refine lintegral_congr_ae ?_
    filter_upwards [h_mul_eq] with b hb using hb
  _ = f (∫ b, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a) := by
    rw [integral_toReal (by fun_prop) h_lt_top]
  _ ≤ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a := by
    rw [← average_eq_integral, ← average_eq_integral]
    exact ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp) h_int' h_int

lemma _root_.ConvexOn.integrable_apply_rnDeriv_of_integrable_compProd
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (hf_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    Integrable (fun a ↦ f ((∂μ/∂ν) a).toReal) ν := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  refine integrable_of_le_of_le (f := fun a ↦ f ((∂μ/∂ν) a).toReal)
    (g₁ := fun x ↦ c * ((∂μ/∂ν) x).toReal + c')
    (g₂ := fun x ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (x, b)).toReal ∂(η x)) ?_ ?_ ?_ (by fun_prop) ?_
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  · exact ae_of_all _ fun x ↦ h _ ENNReal.toReal_nonneg
  · exact hf_cvx.apply_rnDeriv_ae_le_integral hf hf_cont hf_int hκη
  · exact hf_int.integral_compProd

end Integrable

lemma integrable_llr_of_integrable_llr_compProd
    [IsMarkovKernel κ] [IsMarkovKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)) :
    Integrable (llr μ ν) μ := by
  have ⟨hμν_ac, hκη_ac⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
  rw [← integrable_rnDeriv_mul_log_iff h_ac] at h_int
  replace h_int := convexOn_mul_log.integrable_apply_rnDeriv_of_integrable_compProd
    continuous_mul_log.stronglyMeasurable continuous_mul_log.continuousOn h_int hκη_ac
  exact (integrable_rnDeriv_mul_log_iff hμν_ac).mp h_int

lemma rnDeriv_compProd_mul_log_eq_mul_add [IsMarkovKernel κ]
    [IsMarkovKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    ∀ᵐ p ∂(ν ⊗ₘ η), ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal * log ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal =
      (((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal * (log ((∂μ/∂ν) p.1).toReal +
        log ((∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) p).toReal)) := by
  filter_upwards [rnDeriv_compProd h_ac ν] with p hp
  simp_rw [hp]
  simp only [ENNReal.toReal_mul]
  by_cases h_zero1 : ((∂μ/∂ν) p.1).toReal = 0
  · simp [h_zero1]
  by_cases h_zero2 : ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal = 0
  · simp [h_zero2]
  simp [log_mul h_zero1 h_zero2]

lemma integrable_llr_compProd_iff [IsMarkovKernel κ]
    [IsMarkovKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ) ↔
      Integrable (llr μ ν) μ ∧ Integrable (llr (μ ⊗ₘ κ) (μ ⊗ₘ η)) (μ ⊗ₘ κ) := by
  have ⟨h_ac_μν, h_ac_κη⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
  rw [← integrable_rnDeriv_mul_log_iff h_ac,
    integrable_congr (rnDeriv_compProd_mul_log_eq_mul_add h_ac_κη)]
  have : Integrable (fun x ↦ ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal *
        (log ((∂μ/∂ν) x.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) x).toReal)) (ν ⊗ₘ η) ↔
      Integrable (fun x ↦ (log ((∂μ/∂ν) x.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) x).toReal))
        (μ ⊗ₘ κ) := integrable_rnDeriv_smul_iff h_ac
  rw [this]
  have h_iff_κ : Integrable (llr μ ν) μ ↔ Integrable (fun x ↦ llr μ ν x.1) (μ ⊗ₘ κ) := by
    rw [Measure.integrable_compProd_iff]
    swap; · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
    simp only [ne_eq, enorm_ne_top, not_false_eq_true, integrable_const_enorm,
      Filter.eventually_true, norm_eq_abs, integral_const, probReal_univ, smul_eq_mul, one_mul,
      true_and]
    rw [← integrable_norm_iff (by fun_prop)]
    simp
  rw [h_iff_κ]
  -- goal of the form `Integrable (f + g) ↔ Integrable f ∧ Integrable g`
  refine ⟨fun h_int ↦ ?_, fun ⟨h_int1, h_int2⟩ ↦ h_int1.add h_int2⟩
  have h_int_iff : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ) ↔
      Integrable (fun x ↦ log ((∂μ/∂ν) x.1).toReal +
        log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) x).toReal) (μ ⊗ₘ κ) := by
    have ⟨h_ac_μν, h_ac_κη⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
    rw [← integrable_rnDeriv_mul_log_iff h_ac,
     integrable_congr (rnDeriv_compProd_mul_log_eq_mul_add h_ac_κη)]
    exact integrable_rnDeriv_smul_iff h_ac
  rw [← h_int_iff] at h_int
  have h_int1 := integrable_llr_of_integrable_llr_compProd h_ac h_int
  rw [h_iff_κ] at h_int1
  rw [h_int_iff, integrable_add_iff_integrable_right'] at h_int
  · refine ⟨h_int1, h_int⟩
  · exact h_int1

variable (μ ν κ η) in
/-- **Chain rule** for the Kullback-Leibler divergence, with conditional KL expressed using
composition-products.
This version holds without any assumption on the measurable spaces. -/
theorem klDiv_compProd_eq_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ]
    [IsMarkovKernel η] :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) := by
  have h_ac_iff : μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ μ ≪ ν ∧ μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
    Measure.absolutelyContinuous_compProd_iff
  -- first, if we don't have absolute continuity, both sides are `∞`
  by_cases h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η
  swap
  · rw [klDiv_of_not_ac h_ac]
    rw [h_ac_iff] at h_ac
    simp only [not_and_or] at h_ac
    cases h_ac with
    | inl h => simp [h]
    | inr h => simp [h]
  -- same if we don't have integrability
  by_cases h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)
  swap
  · rw [klDiv_of_not_integrable h_int]
    rw [integrable_llr_compProd_iff h_ac] at h_int
    simp only [not_and_or] at h_int
    cases h_int with
    | inl h => simp [h]
    | inr h => simp [h]
  -- now we can use the Radon-Nikodym derivatives to express the KL divergences
  have ⟨h_ac_μν, h_ac_κη⟩ := h_ac_iff.mp h_ac
  have ⟨h_int_μν, h_int_κη⟩ := (integrable_llr_compProd_iff h_ac).mp h_int
  rw [klDiv_of_ac_of_integrable h_ac h_int, klDiv_of_ac_of_integrable h_ac_μν h_int_μν,
    klDiv_of_ac_of_integrable h_ac_κη h_int_κη]
  rw [← ENNReal.ofReal_add]
  rotate_left
  · exact integral_llr_add_sub_measure_univ_nonneg h_ac_μν h_int_μν
  · exact integral_llr_add_sub_measure_univ_nonneg h_ac_κη h_int_κη
  congr
  simp_rw [measureReal_def, Measure.compProd_apply_univ]
  rw [add_sub_cancel_right]
  suffices ∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂μ ⊗ₘ κ =
      ∫ a, llr μ ν a ∂μ + ∫ p, llr (μ ⊗ₘ κ) (μ ⊗ₘ η) p ∂(μ ⊗ₘ κ) by rw [this]; ring
  have h_int1 : Integrable (fun p ↦ log ((∂μ/∂ν) p.1).toReal) (μ ⊗ₘ κ) := by
    rw [Measure.integrable_compProd_iff]
    · simp only [ne_eq, enorm_ne_top, not_false_eq_true, integrable_const_enorm,
        Filter.eventually_true, norm_eq_abs, integral_const, probReal_univ, smul_eq_mul, one_mul,
        true_and]
      rw [← integrable_norm_iff (by fun_prop)] at h_int_μν
      convert h_int_μν
    · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  calc ∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂μ ⊗ₘ κ
  _ = ∫ p, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal * log ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal ∂(ν ⊗ₘ η) := by
    rw [integral_rnDeriv_mul_log h_ac]
  _ = ∫ p, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal *
      (log ((∂μ/∂ν) p.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal) ∂(ν ⊗ₘ η) :=
    integral_congr_ae (rnDeriv_compProd_mul_log_eq_mul_add h_ac_κη)
  _ = ∫ p, (log ((∂μ/∂ν) p.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal) ∂(μ ⊗ₘ κ) :=
    integral_rnDeriv_smul h_ac
  _ = ∫ p, log ((∂μ/∂ν) p.1).toReal ∂(μ ⊗ₘ κ) +
      ∫ p, log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal ∂(μ ⊗ₘ κ) := by
    rw [integral_add h_int1]
    exact h_int_κη.ofReal
  _ = ∫ a, llr μ ν a ∂μ + ∫ p, llr (μ ⊗ₘ κ) (μ ⊗ₘ η) p ∂(μ ⊗ₘ κ) := by
    congr
    rw [Measure.integral_compProd h_int1]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rfl

end InformationTheory
