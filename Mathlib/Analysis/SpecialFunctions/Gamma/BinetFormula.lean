/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Analysis.SpecialFunctions.Gamma.BinetKernel

set_option linter.style.longFile 1800

/-!
# Binet's Formula for log Γ and Stirling Series with Error Bounds

This file develops the Binet formula for the logarithm of the Gamma function
and derives sharp error bounds for the Stirling asymptotic series.

## Main Definitions

* `Binet.J`: the Binet integral (defined for `0 < z.re`)
* `Binet.R`: the real correction term in Stirling's formula
* `Binet.stirlingSeries`, `Binet.stirlingRemainder`: the Stirling series (via Bernoulli numbers) and
   its remainder

## Main Results

* `Binet.log_Gamma_real_eq`: Binet's formula for `Real.log (Real.Gamma x)` on `0 < x`
* `Binet.J_norm_le_re`: the main bound `‖J z‖ ≤ 1 / (12 * z.re)` for `0 < z.re`
* `Binet.J_norm_le_real`: the specialization `‖J x‖ ≤ 1 / (12 * x)` for `0 < x`

## References

* NIST DLMF 5.11: Asymptotic Expansions
* Robbins, H. "A Remark on Stirling's Formula." Amer. Math. Monthly 62 (1955): 26-29.
* Whittaker & Watson, "A Course of Modern Analysis", Chapter 12

## Implementation Notes

We use the normalized kernel `BinetKernel.Ktilde` (from `BinetKernel.K`), which satisfies
`BinetKernel.Ktilde t → 1 / 12` as `t → 0⁺` and `0 ≤ BinetKernel.Ktilde t ≤ 1 / 12` for `0 ≤ t`.
-/

open Real Complex Set MeasureTheory Filter Topology BinetKernel
open scoped BigOperators Nat


private lemma one_div_cast_sub_le_two_div_cast (n : ℕ) (hn2 : 2 ≤ n) :
    (1 : ℝ) / ((n - 1 : ℕ) : ℝ) ≤ (2 : ℝ) / (n : ℝ) := by
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn2))
  have hn1_pos : 0 < ((n - 1 : ℕ) : ℝ) := by
    have : 0 < n - 1 := Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hn2)
    exact_mod_cast this
  refine (div_le_div_iff₀ hn1_pos hn_pos).2 ?_
  have hn1_ge1 : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ n - 1 := Nat.sub_le_sub_right hn2 1
    exact_mod_cast this
  have hn_nat_pos : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn2
  have hnat : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn_nat_pos)
  have hcast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hnat.symm
  nlinarith [hn1_ge1, hcast]
noncomputable section

namespace Binet

/-! ## The Binet integral J(z) -/

/-- The Binet integral term in Binet's formula (defined for `0 < z.re`). -/
def J (z : ℂ) : ℂ :=
  if 0 < z.re then
    ∫ t in Set.Ioi (0 : ℝ), (Ktilde t : ℂ) * Complex.exp (-t * z)
  else 0

/-- J(z) is well-defined for Re(z) > 0 (the integral converges). -/
lemma J_well_defined {z : ℂ} (hz : 0 < z.re) :
    MeasureTheory.Integrable (fun t : ℝ => (Ktilde t : ℂ) * Complex.exp (-t * z))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)) :=
  BinetKernel.integrable_Ktilde_exp_complex hz

/-- For Re(z) > 0, J(z) equals the integral. -/
lemma J_eq_integral {z : ℂ} (hz : 0 < z.re) :
    J z = ∫ t in Set.Ioi (0 : ℝ), (Ktilde t : ℂ) * Complex.exp (-t * z) := by
  simp only [J, if_pos hz]

lemma norm_Ktilde_mul_exp {z : ℂ} (t : ℝ) (ht : 0 < t) :
    ‖(Ktilde t : ℂ) * Complex.exp (-t * z)‖ = Ktilde t * Real.exp (-t * z.re) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Ktilde_nonneg (le_of_lt ht)), Complex.norm_exp]
  congr 1
  have : ((-↑t * z).re) = -t * z.re := by
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [this]

lemma integrable_const_mul_exp {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => (1/12 : ℝ) * Real.exp (-t * x)) (Set.Ioi 0) := by
  apply Integrable.const_mul
  have h := integrableOn_exp_mul_Ioi (neg_neg_of_pos hx) 0
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t _
  ring_nf

lemma Ktilde_mul_exp_le {x : ℝ} (t : ℝ) (ht : 0 < t) :
    Ktilde t * Real.exp (-t * x) ≤ (1/12 : ℝ) * Real.exp (-t * x) :=
  mul_le_mul_of_nonneg_right (Ktilde_le (le_of_lt ht)) (Real.exp_nonneg _)

lemma integral_exp_neg_mul_Ioi {x : ℝ} (hx : 0 < x) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) = 1 / x := by
  have h := integral_exp_mul_Ioi (neg_neg_of_pos hx) 0
  simp only [mul_zero, Real.exp_zero] at h
  have heq : (fun t => Real.exp (-t * x)) = (fun t => Real.exp (-x * t)) := by
    ext t; ring_nf
  rw [heq, h]
  field_simp

/-- The fundamental bound `‖J z‖ ≤ 1 / (12 * z.re)` for `0 < z.re`.

This is the key estimate for the Stirling remainder. -/
theorem J_norm_le_re {z : ℂ} (hz : 0 < z.re) : ‖J z‖ ≤ 1 / (12 * z.re) := by
  rw [J_eq_integral hz]
  calc ‖∫ t in Set.Ioi (0 : ℝ), (Ktilde t : ℂ) * Complex.exp (-t * z)‖
      ≤ ∫ t in Set.Ioi (0 : ℝ), ‖(Ktilde t : ℂ) * Complex.exp (-t * z)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), Ktilde t * Real.exp (-t * z.re) := by
        apply MeasureTheory.setIntegral_mono_on
        · exact (J_well_defined hz).norm
        · exact BinetKernel.integrable_Ktilde_exp hz
        · exact measurableSet_Ioi
        · intro t ht
          rw [norm_Ktilde_mul_exp t ht]
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), (1/12 : ℝ) * Real.exp (-t * z.re) := by
        apply MeasureTheory.setIntegral_mono_on
        · exact BinetKernel.integrable_Ktilde_exp hz
        · exact integrable_const_mul_exp hz
        · exact measurableSet_Ioi
        · intro t ht
          exact Ktilde_mul_exp_le t ht
    _ = (1/12 : ℝ) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * z.re) := by
        rw [← MeasureTheory.integral_const_mul]
    _ = (1/12 : ℝ) * (1 / z.re) := by
        rw [integral_exp_neg_mul_Ioi hz]
    _ = 1 / (12 * z.re) := by ring

/-- For real `x > 0`, the bound simplifies to `‖J (x : ℂ)‖ ≤ 1 / (12 * x)`.

This is a special case of `J_norm_le_re`. -/
theorem J_norm_le_real {x : ℝ} (hx : 0 < x) : ‖J (x : ℂ)‖ ≤ 1 / (12 * x) := by
  have hre : (0 : ℝ) < (x : ℂ).re := by simp [hx]
  have h := J_norm_le_re hre
  simp only [Complex.ofReal_re] at h
  exact h

lemma tendsto_re_J_atTop : Tendsto (fun y : ℝ => (Binet.J (y : ℂ)).re) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨(1 / (12 * ε) : ℝ) + 1, ?_⟩
  intro y hy
  have hy_pos : 0 < y := by
    have : 0 < (1 / (12 * ε) : ℝ) := by positivity
    have : 0 < (1 / (12 * ε) : ℝ) + 1 := by linarith
    exact this.trans_le hy
  have hbound : |(Binet.J (y : ℂ)).re| ≤ 1 / (12 * y) := by
    have := Complex.abs_re_le_norm (Binet.J (y : ℂ))
    have hnorm := J_norm_le_real (x := y) hy_pos
    exact le_trans this hnorm
  have h1 : 1 / (12 * y) < ε := by
    have hy' : 0 < 12 * y := by positivity
    have hy_gt : (1 / (12 * ε) : ℝ) < y := by linarith
    have hpos : 0 < (12 * ε : ℝ) := by positivity
    have : (12 * ε : ℝ) * (1 / (12 * ε) : ℝ) < (12 * ε : ℝ) * y := by
      exact mul_lt_mul_of_pos_left hy_gt hpos
    have hleft : (12 * ε : ℝ) * (1 / (12 * ε) : ℝ) = 1 := by field_simp
    rw [hleft] at this
    have hbig : (1 : ℝ) < ε * (12 * y) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hy'' : 0 < 12 * y := by positivity
    have : (1 : ℝ) / (12 * y) < ε := (div_lt_iff₀ hy'').2 (by
      simpa [mul_assoc] using hbig)
    simpa using this
  have : |(Binet.J (y : ℂ)).re - 0| < ε := by
    simpa using lt_of_le_of_lt hbound h1
  simpa [Real.dist_eq] using this

lemma eq_of_tendsto_atTop_of_add_one {h : ℝ → ℝ} {x l : ℝ} (hx : 0 < x)
    (h_add_one : ∀ y, 0 < y → h y = h (y + 1)) (hlim : Tendsto h atTop (𝓝 l)) :
    h x = l := by
  have hxseq : Tendsto (fun n : ℕ => h (x + n)) atTop (𝓝 l) := by
    have hxadd : Tendsto (fun n : ℕ => (x + n : ℝ)) atTop atTop := by
      -- `x + n → ∞`
      have hnx : Tendsto (fun n : ℕ => ((n : ℝ) + x)) atTop atTop :=
        Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds
      simpa [add_assoc, add_comm, add_left_comm] using hnx
    exact hlim.comp hxadd
  have hconst : (fun n : ℕ => h (x + n)) = fun _ => h x := by
    funext n
    induction n with
    | zero => simp
    | succ n ih =>
      have hxpos : 0 < x + n := by linarith [hx]
      have hstep : h (x + (n + 1)) = h (x + n) := by
        simpa [add_assoc, add_comm, add_left_comm] using (h_add_one (x + n) hxpos).symm
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm, ih] using hstep
  rw [hconst] at hxseq
  exact tendsto_const_nhds_iff.mp hxseq

end Binet
