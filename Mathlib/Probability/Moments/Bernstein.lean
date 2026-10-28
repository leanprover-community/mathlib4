/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Moments.Basic

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Bernstein bounds

We bound the conditional moment-generating function of a centered random variable whose
values are bounded above, in terms of its conditional second moment. This also gives
Bernstein's concentration inequality for finite sums of independent random variables.

## Main results

* `ProbabilityTheory.condExp_exp_mul_le_exp_mul_condExp_sq`: a conditional Bernstein bound
  in terms of the conditional second moment.
* `ProbabilityTheory.measure_sum_ge_le_bernstein`: Bernstein's inequality for a finite sum of
  independent, centered random variables with a common upper bound.
-/

public section

namespace Real

private lemma exp_le_one_add_add_sq_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    exp x ≤ 1 + x + x ^ 2 / 2 := by
  have hd (y : ℝ) : HasDerivAt (fun z : ℝ ↦ 1 + z + z ^ 2 / 2 - exp z)
      (1 + y - exp y) y := by
    convert! (((hasDerivAt_id y).const_add 1).add
      (((hasDerivAt_id y).pow 2).div_const 2)).sub (hasDerivAt_exp y) using 1
    simp
  have hmono := antitone_of_hasDerivAt_nonpos hd fun y ↦
    sub_nonpos.mpr ((add_comm 1 y).trans_le (add_one_le_exp y))
  simpa using hmono hx

private lemma exp_le_one_add_add_sq_div_of_nonneg {x : ℝ} (hx : 0 ≤ x) (hx3 : x < 3) :
    exp x ≤ 1 + x + x ^ 2 / (2 * (1 - x / 3)) := by
  let f : ℝ → ℝ := fun y ↦ (y ^ 2 + 4 * y + 6) / (6 - y * 2) * exp (-y)
  have hd (y : ℝ) (hy : y < 3) : HasDerivAt f
      (2 * y ^ 3 / (6 - y * 2) ^ 2 * exp (-y)) y := by
    have hy0 : 6 - y * 2 ≠ 0 := by linarith
    convert! (((((hasDerivAt_id y).pow 2).add
      ((hasDerivAt_id y).const_mul 4)).add_const 6).div
      ((hasDerivAt_const y 6).sub ((hasDerivAt_id y).mul_const 2)) hy0).mul
      (hasDerivAt_id y).neg.exp using 1
    dsimp
    field_simp [hy0]
    ring
  have hm : MonotoneOn f (Set.Ico 0 3) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 3)
    · exact fun y hy ↦ (hd y hy.2).continuousAt.continuousWithinAt
    · exact fun y hy ↦ (hd y (interior_subset hy).2).hasDerivWithinAt
    · intro y hy
      have hy0 := (interior_subset hy).1
      positivity
  have h := hm (by simp) ⟨hx, hx3⟩ hx
  have hx0 : 6 - x * 2 ≠ 0 := by linarith
  have hq : (x ^ 2 + 4 * x + 6) / (6 - x * 2) =
      1 + x + x ^ 2 / (2 * (1 - x / 3)) := by
    rw [show 2 * (1 - x / 3) = (6 - x * 2) / 3 by ring, div_div_eq_mul_div]
    apply (div_eq_iff hx0).2
    rw [add_mul, div_mul_cancel₀ _ hx0]
    ring
  simpa [f, hq, exp_neg, ← div_eq_mul_inv, le_div_iff₀ (exp_pos x)] using h

/-- A one-sided Bernstein bound for the exponential function. -/
lemma exp_le_one_add_add_sq_div {x y : ℝ} (hxy : x ≤ y) (hy : 0 ≤ y) (hy3 : y < 3) :
    exp x ≤ 1 + x + x ^ 2 / (2 * (1 - y / 3)) := by
  rcases le_total x 0 with hx | hx
  · refine (exp_le_one_add_add_sq_of_nonpos hx).trans ?_
    gcongr
    · linarith
    · linarith
  · refine (exp_le_one_add_add_sq_div_of_nonneg hx (hxy.trans_lt hy3)).trans ?_
    gcongr
    linarith

end Real

open MeasureTheory Filter
open scoped ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} {m₀ m : MeasurableSpace Ω} {μ : Measure[m₀] Ω} {X : Ω → ℝ} {b θ : ℝ}

/-- The exponential of a nonnegative multiple of a random variable bounded above is integrable. -/
lemma integrable_exp_mul_of_ae_le [IsFiniteMeasure μ] (hX : AEStronglyMeasurable[m₀] X μ)
    (hbound : ∀ᵐ ω ∂μ, X ω ≤ b) (hθ : 0 ≤ θ) :
    Integrable (fun ω ↦ Real.exp (θ * X ω)) μ := by
  refine (integrable_const (Real.exp (θ * b))).mono'
    (Real.continuous_exp.comp_aestronglyMeasurable (hX.const_mul θ)) ?_
  filter_upwards [hbound] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hθ)

/-- A conditional Bernstein bound: the conditional moment-generating function of a centered
random variable bounded above is controlled by its conditional second moment. -/
lemma condExp_exp_mul_le_exp_mul_condExp_sq [IsFiniteMeasure μ] (hm : m ≤ m₀)
    (hX : MemLp X 2 μ) (hbound : ∀ᵐ ω ∂μ, X ω ≤ b) (hmean : μ[X | m] =ᵐ[μ] 0)
    (hb : 0 < b) (hθ : 0 ≤ θ) (hθb : θ * b < 3) :
    μ[fun ω ↦ Real.exp (θ * X ω) | m] ≤ᵐ[μ]
      fun ω ↦ Real.exp ((θ ^ 2 / (2 * (1 - θ * b / 3))) *
        (μ[fun ω ↦ X ω ^ 2 | m]) ω) := by
  let c := θ ^ 2 / (2 * (1 - θ * b / 3))
  have hiθ := (hX.integrable one_le_two).const_mul θ
  have hisq := hX.integrable_sq.const_mul c
  have hibound : Integrable (fun ω ↦ 1 + θ * X ω + c * X ω ^ 2) μ :=
    ((integrable_const 1).add hiθ).add hisq
  have hpoint : (fun ω ↦ Real.exp (θ * X ω)) ≤ᵐ[μ]
      fun ω ↦ 1 + θ * X ω + c * X ω ^ 2 := by
    filter_upwards [hbound] with ω hω
    simpa only [c, mul_pow, div_mul_eq_mul_div] using
      Real.exp_le_one_add_add_sq_div (mul_le_mul_of_nonneg_left hω hθ)
        (mul_nonneg hθ hb.le) hθb
  have hmono := condExp_mono (m := m)
    (integrable_exp_mul_of_ae_le hX.aestronglyMeasurable hbound hθ)
    hibound hpoint
  have hadd := condExp_add ((integrable_const 1).add hiθ) hisq m
  have hadd' := condExp_add (integrable_const 1) hiθ m
  filter_upwards [hmono, hadd, hadd', condExp_smul θ X m,
    condExp_smul c (fun ω ↦ X ω ^ 2) m, hmean] with ω hω ha ha' hθω hcω hzero
  simp only [Pi.add_def, Pi.smul_def, smul_eq_mul, Pi.zero_apply,
    condExp_const hm] at ha ha' hθω hcω hzero
  calc
    _ ≤ (μ[fun ω ↦ 1 + θ * X ω + c * X ω ^ 2 | m]) ω := hω
    _ = 1 + c * (μ[fun ω ↦ X ω ^ 2 | m]) ω := by
      rw [ha, ha', hθω, hcω, hzero]
      simp
    _ ≤ _ := by
      simpa [c, add_comm] using Real.add_one_le_exp (c * (μ[fun ω ↦ X ω ^ 2 | m]) ω)

/-- A Bernstein bound for the moment-generating function of a centered random variable
bounded above. -/
lemma mgf_le_exp_of_ae_le_of_integral_eq_zero [IsProbabilityMeasure μ]
    (hX : MemLp X 2 μ) (hbound : ∀ᵐ ω ∂μ, X ω ≤ b) (hmean : μ[X] = 0)
    (hb : 0 < b) (hθ : 0 ≤ θ) (hθb : θ * b < 3) :
    mgf X μ θ ≤ Real.exp ((θ ^ 2 / (2 * (1 - θ * b / 3))) * μ[fun ω ↦ X ω ^ 2]) := by
  have h := condExp_exp_mul_le_exp_mul_condExp_sq (m := ⊥) bot_le hX hbound
    (by filter_upwards with ω; simp [condExp_bot, hmean]) hb hθ hθb
  obtain ⟨ω, hω⟩ := h.exists
  simpa [condExp_bot, mgf] using hω

/-- **Bernstein's inequality** for independent centered random variables bounded above.
Here `v` bounds the sum of their second moments, equivalently their total variance. -/
lemma measure_sum_ge_le_bernstein [IsProbabilityMeasure μ] {ι : Type*}
    {X : ι → Ω → ℝ} {s : Finset ι} {b t v : ℝ} (hindep : iIndepFun X μ)
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ≤ b)
    (hmean : ∀ i ∈ s, μ[X i] = 0) (hb : 0 < b) (ht : 0 ≤ t) (hv : 0 < v)
    (hsq : ∑ i ∈ s, μ[fun ω ↦ X i ω ^ 2] ≤ v) :
    μ.real {ω | t ≤ ∑ i ∈ s, X i ω} ≤ Real.exp (-t ^ 2 / (2 * (v + b * t / 3))) := by
  let θ := t / (v + b * t / 3)
  let c := θ ^ 2 / (2 * (1 - θ * b / 3))
  have hd : 0 < v + b * t / 3 := by positivity
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hθb : θ * b < 3 := by
    dsimp [θ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
    nlinarith
  have he : 0 < 1 - θ * b / 3 := by linarith
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hsum_meas : AEStronglyMeasurable[m₀] (fun ω ↦ ∑ i ∈ s, X i ω) μ :=
    Finset.aestronglyMeasurable_fun_sum s fun i hi ↦ (hX i hi).aestronglyMeasurable
  have hsum_bound : ∀ᵐ ω ∂μ, (∑ i ∈ s, X i ω) ≤ s.card * b := by
    filter_upwards [(eventually_all_finset s).2 hbound] with ω hω
    simpa using Finset.sum_le_sum hω
  have hprod : mgf (fun ω ↦ ∑ i ∈ s, X i ω) μ θ = ∏ i ∈ s, mgf (X i) μ θ := by
    have hrest : iIndepFun (fun i : s ↦ X i) μ := hindep.precomp Subtype.val_injective
    have h := hrest.mgf_sum₀ (t := θ)
      (fun i ↦ (hX i i.2).aestronglyMeasurable.aemeasurable) Finset.univ
    rw [Finset.sum_coe_sort s X, Finset.prod_coe_sort s (fun i ↦ mgf (X i) μ θ)] at h
    simpa only [← Finset.sum_apply] using h
  have hmgf : mgf (fun ω ↦ ∑ i ∈ s, X i ω) μ θ ≤ Real.exp (c * v) := by
    rw [hprod]
    calc
      _ ≤ ∏ i ∈ s, Real.exp (c * μ[fun ω ↦ X i ω ^ 2]) := by
        apply Finset.prod_le_prod₀ (fun _ _ ↦ mgf_nonneg)
        exact fun i hi ↦ mgf_le_exp_of_ae_le_of_integral_eq_zero
          (hX i hi) (hbound i hi) (hmean i hi) hb hθ hθb
      _ = Real.exp (c * ∑ i ∈ s, μ[fun ω ↦ X i ω ^ 2]) := by
        rw [← Real.exp_sum, Finset.mul_sum]
      _ ≤ Real.exp (c * v) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsq hc)
  calc
    _ ≤ Real.exp (-θ * t) * mgf (fun ω ↦ ∑ i ∈ s, X i ω) μ θ :=
      measure_ge_le_exp_mul_mgf t hθ (integrable_exp_mul_of_ae_le hsum_meas hsum_bound hθ)
    _ ≤ Real.exp (-θ * t) * Real.exp (c * v) := by gcongr
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      dsimp [c, θ]
      field_simp
      ring

end ProbabilityTheory
