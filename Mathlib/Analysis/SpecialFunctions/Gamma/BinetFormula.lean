/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Analysis.SpecialFunctions.Gamma.BinetKernel

set_option linter.style.longFile 2100

/-!
# Binet's Formula for log Γ and Stirling Series with Error Bounds

This file develops the Binet formula for the logarithm of the Gamma function
and derives sharp error bounds for the Stirling asymptotic series.

## Main Definitions

* `Binet.J`: the Binet integral `J z = ∫ t in Ioi (0 : ℝ), K̃(t) * exp (-t*z)` (for `0 < z.re`)
* `Binet.R`: the real correction term in Stirling's formula
* `Binet.stirlingSeries`, `Binet.stirlingRemainder`: the Stirling series (via Bernoulli numbers) and
   its remainder

## Main Results

* `Binet.log_Gamma_real_eq`: Binet's formula for `Real.log (Real.Gamma x)` on `0 < x`
* `Binet.J_norm_le_re`: the fundamental bound `‖J z‖ ≤ 1 / (12 * z.re)` for `0 < z.re`
* `Binet.J_norm_le_real`: the specialization `‖J x‖ ≤ 1 / (12 * x)` for `0 < x`

## References

* NIST DLMF 5.11: Asymptotic Expansions
* Robbins, H. "A Remark on Stirling's Formula." Amer. Math. Monthly 62 (1955): 26-29.
* Whittaker & Watson, "A Course of Modern Analysis", Chapter 12

## Implementation Notes

We use the normalized kernel `BinetKernel.Ktilde`, defined from `BinetKernel.K` by
  `K̃(t) = K(t) / t`
on `(0, ∞)` (with a continuous extension at `t = 0`). This satisfies `K̃(t) → 1 / 12` as `t → 0⁺`
  and `0 ≤ K̃(t) ≤ 1 / 12` for `t ≥ 0`.
-/

open Real Complex Set MeasureTheory Filter Topology BinetKernel
open scoped BigOperators Nat


lemma one_div_cast_sub_le_two_div_cast (n : ℕ) (hn2 : 2 ≤ n) :
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
#find_home one_div_cast_sub_le_two_div_cast
noncomputable section

namespace Binet

/-! ## The Binet integral J(z) -/

/-- The Binet integral: J(z) = ∫₀^∞ K̃(t) e^{-tz} dt for Re(z) > 0.
This is the correction term in log Γ(z) = (z-1/2)log z - z + log(2π)/2 + J(z). -/
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

/-- The fundamental bound: |J(z)| ≤ 1/(12·Re(z)) for Re(z) > 0.
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

/-- For real positive x, the bound simplifies to |J(x)| ≤ 1/(12x).
This is a special case of J_norm_le_re since for real x > 0, ‖x‖ = x = x.re. -/
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

/-! ## Binet's formula for log Γ -/

/-!
### About a complex `log Γ` statement

A statement of the form

`Complex.log (Complex.Gamma z) = (z - 1/2) * Complex.log z - z + log(2π)/2 + J z`

using the *principal* complex logarithm `Complex.log` is **not valid on all of** `{z | 0 < re z}`:
`Γ` crosses the negative real axis infinitely many times in the right half-plane, so the composite
`Complex.log ∘ Complex.Gamma` cannot be holomorphic there.

A principled complex formulation should instead use a holomorphic branch of `log Γ`
(often called `logGamma`) on a suitable simply-connected domain.
-/

/-- The Stirling main terms for real `x`. -/
def stirlingMainReal (x : ℝ) : ℝ :=
  (x - 1 / 2) * Real.log x - x + Real.log (2 * Real.pi) / 2

/-- The (real) Stirling correction term:
`R(x) := log Γ(x) - ((x - 1/2) log x - x + log(2π)/2)`. -/
def R (x : ℝ) : ℝ :=
  Real.log (Real.Gamma x) - stirlingMainReal x

lemma stirlingMainReal_add_one_sub {x : ℝ} (hx : 0 < x) :
    stirlingMainReal (x + 1) - stirlingMainReal x =
      Real.log x + (x + 1 / 2) * Real.log (1 + 1 / x) - 1 := by
  unfold stirlingMainReal
  have hx1 : 0 < x + 1 := by linarith
  have hlog_sum : Real.log (x + 1) = Real.log x + Real.log (1 + 1 / x) := by
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h1 : x + 1 = x * (1 + 1 / x) := by
      calc
        x + 1 = x + x * (1 / x) := by simp [hx0]
        _ = x * (1 + 1 / x) := by ring
    rw [h1, Real.log_mul hx0 (by
      have : 0 < (1 + 1 / x) := by
        have : 0 < (1 / x : ℝ) := by positivity
        linarith
      exact ne_of_gt this)]
  rw [hlog_sum]
  ring

lemma R_sub_R_add_one {x : ℝ} (hx : 0 < x) :
    R x - R (x + 1) = (x + 1 / 2) * Real.log (1 + 1 / x) - 1 := by
  unfold R
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hΓ_diff :
      Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x) = Real.log x := by
    have hΓ : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one (s := x) hx0
    have hΓx_ne : Real.Gamma x ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
    calc
      Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x)
          = (Real.log x + Real.log (Real.Gamma x)) - Real.log (Real.Gamma x) := by
              simp [hΓ, Real.log_mul hx0 hΓx_ne]
      _ = Real.log x := by ring
  have hS := stirlingMainReal_add_one_sub (x := x) hx
  calc
    (Real.log (Real.Gamma x) - stirlingMainReal x) - (Real.log (Real.Gamma (x + 1)) -
      stirlingMainReal (x + 1))
        = (stirlingMainReal (x + 1) - stirlingMainReal x) -
            (Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x)) := by ring
    _ = (Real.log x + (x + 1 / 2) * Real.log (1 + 1 / x) - 1) - Real.log x := by
          simpa [hΓ_diff] using congrArg (fun t => t - Real.log x) hS
    _ = (x + 1 / 2) * Real.log (1 + 1 / x) - 1 := by ring

/-- Real-part version of the Binet integral: for `x > 0`,
`re (J x) = ∫₀^∞ K̃(t) * exp(-t*x) dt`. -/
theorem re_J_eq_integral_Ktilde {x : ℝ} (hx : 0 < x) :
    (Binet.J (x : ℂ)).re = ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) := by
  have hx' : 0 < (x : ℂ).re := by simpa using hx
  rw [Binet.J_eq_integral (z := (x : ℂ)) hx']
  have hInt :
      Integrable (fun t : ℝ => (BinetKernel.Ktilde t : ℂ) * Complex.exp (-t * (x : ℂ)))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Binet.J_well_defined (z := (x : ℂ)) hx'
  have hre :
      ∫ t in Set.Ioi (0 : ℝ),
          ((BinetKernel.Ktilde t : ℂ) * Complex.exp (-t * (x : ℂ))).re
        = (∫ t in Set.Ioi (0 : ℝ),
              (BinetKernel.Ktilde t : ℂ) * Complex.exp (-t * (x : ℂ))).re := by
    simpa using
      (integral_re (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (f := fun t : ℝ => (BinetKernel.Ktilde t : ℂ) * Complex.exp (-t * (x : ℂ))) hInt)
  rw [← hre]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro t _ht
  dsimp
  have hexp : Complex.exp (-t * (x : ℂ)) = (Real.exp (-t * x) : ℂ) := by
    have harg : (-t * (x : ℂ)) = ((-t * x : ℝ) : ℂ) := by simp
    calc
      Complex.exp (-t * (x : ℂ)) = Complex.exp ((-t * x : ℝ) : ℂ) := by simp [harg]
      _ = (Real.exp (-t * x) : ℂ) := by simp
  rw [hexp]
  simp [-Complex.ofReal_exp]

/-- Auxiliary identity: for `t > 0`,
`K̃(t) * (1 - exp(-t)) = ∫_{u∈[0,1]} (1/2 - u) * exp(-u*t) du`. -/
lemma Ktilde_mul_one_sub_exp_eq_integral {t : ℝ} (ht : 0 < t) :
    BinetKernel.Ktilde t * (1 - Real.exp (-t)) =
      ∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hIcc :
      (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t)) =
        ∫ u in (0 : ℝ)..1, (1 / 2 - u) * Real.exp (-u * t) := by
    have hIccIoc :
        (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t)) =
          ∫ u in Set.Ioc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t) := by
      simpa using
        (MeasureTheory.integral_Icc_eq_integral_Ioc
          (μ := (volume : Measure ℝ)) (f := fun u : ℝ => (1 / 2 - u) * Real.exp (-u * t))
          (x := (0 : ℝ)) (y := (1 : ℝ)))
    have hIoc :
        ∫ u in Set.Ioc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t) =
          ∫ u in (0 : ℝ)..1, (1 / 2 - u) * Real.exp (-u * t) := by
      simpa using
        (intervalIntegral.integral_of_le (μ := (volume : Measure ℝ))
          (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := fun u : ℝ => (1 / 2 - u) * Real.exp (-u * t)) (by norm_num : (0 : ℝ) ≤ 1)).symm
    exact hIccIoc.trans hIoc
  rw [hIcc]
  have hInt_exp : IntervalIntegrable (fun u : ℝ => Real.exp (-u * t)) volume (0 : ℝ) 1 := by
    have hcont : Continuous (fun u : ℝ => Real.exp (-u * t)) := by
      fun_prop
    exact hcont.intervalIntegrable (μ := (volume : Measure ℝ)) (0 : ℝ) 1
  have hInt_u_exp :
      IntervalIntegrable (fun u : ℝ => u * Real.exp (-u * t)) volume (0 : ℝ) 1 :=
    by
    have hcont : Continuous (fun u : ℝ => u * Real.exp (-u * t)) := by
      fun_prop
    exact hcont.intervalIntegrable (μ := (volume : Measure ℝ)) (0 : ℝ) 1
  have h_split :
      (∫ u in (0 : ℝ)..1, (1 / 2 - u) * Real.exp (-u * t)) =
        (1 / 2 : ℝ) * (∫ u in (0 : ℝ)..1, Real.exp (-u * t)) -
          (∫ u in (0 : ℝ)..1, u * Real.exp (-u * t)) := by
    have hlin :
        (fun u : ℝ => (1 / 2 - u) * Real.exp (-u * t)) =
          (fun u : ℝ => (1 / 2 : ℝ) * Real.exp (-u * t)) - fun u : ℝ => u * Real.exp (-u * t) := by
      funext u
      simp [sub_mul]
    rw [hlin]
    have hInt1 :
        IntervalIntegrable (fun u : ℝ => (1 / 2 : ℝ) * Real.exp (-u * t)) volume (0 : ℝ) 1 :=
      hInt_exp.const_mul (1 / 2 : ℝ)
    simpa [intervalIntegral.integral_const_mul] using
      (intervalIntegral.integral_sub (μ := (volume : Measure ℝ)) hInt1 hInt_u_exp)
  rw [h_split]
  have h_exp :
      (∫ u in (0 : ℝ)..1, Real.exp (-u * t)) = (1 - Real.exp (-t)) / t := by
    have hab : (0 : ℝ) ≤ 1 := by norm_num
    have hcont : ContinuousOn (fun u : ℝ => -(Real.exp (-u * t) / t)) (Set.Icc (0 : ℝ) 1) := by
      have hcont' : Continuous (fun u : ℝ => -(Real.exp (-u * t) / t)) := by
        fun_prop
      exact hcont'.continuousOn
    have hderiv :
        ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun u : ℝ => -(Real.exp (-u * t) / t))
          (Real.exp (-u * t)) u := by
      intro u _hu
      have h_inner : HasDerivAt (fun u : ℝ => -u * t) (-t) u := by
        simpa [mul_assoc] using ((hasDerivAt_id u).mul_const (-t))
      have h_exp' : HasDerivAt (fun u : ℝ => Real.exp (-u * t))
          ((-t) * Real.exp (-u * t)) u := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          (Real.hasDerivAt_exp (-u * t)).comp u h_inner
      have : HasDerivAt (fun u : ℝ => Real.exp (-u * t) / t) (((-t) * Real.exp (-u * t)) / t) u :=
        h_exp'.div_const t
      have : HasDerivAt (fun u : ℝ => -(Real.exp (-u * t) / t)) (-(((-t) *
          Real.exp (-u * t)) / t)) u :=
        this.neg
      simpa [ht0, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    have hint : IntervalIntegrable (fun u : ℝ => Real.exp (-u * t)) volume (0 : ℝ) 1 := hInt_exp
    have hFTC :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint
    have h' : (∫ u in (0 : ℝ)..1, Real.exp (-u * t)) = -(Real.exp (-t) / t) + t⁻¹ := by
      simpa [Real.exp_zero, ht0] using hFTC
    calc
      (∫ u in (0 : ℝ)..1, Real.exp (-u * t)) = -(Real.exp (-t) / t) + t⁻¹ := h'
      _ = (1 - Real.exp (-t)) / t := by
          field_simp [ht0]
          ring
  have h_u_exp :
      (∫ u in (0 : ℝ)..1, u * Real.exp (-u * t)) =
        (1 - Real.exp (-t) * (t + 1)) / (t ^ 2) := by
    have hab : (0 : ℝ) ≤ 1 := by norm_num
    let F : ℝ → ℝ := fun u =>
      -(u * Real.exp (-u * t)) / t - (Real.exp (-u * t)) / (t ^ 2)
    have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
      refine (Continuous.continuousOn ?_)
      have hcont' : Continuous F := by
        fun_prop [F]
      exact hcont'
    have hderiv : ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F (u * Real.exp (-u * t)) u := by
      intro u _hu
      have h_inner : HasDerivAt (fun u : ℝ => -u * t) (-t) u := by
        simpa [mul_assoc] using ((hasDerivAt_id u).mul_const (-t))
      have h_exp' : HasDerivAt (fun u : ℝ => Real.exp (-u * t))
          ((-t) * Real.exp (-u * t)) u := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using (Real.hasDerivAt_exp
          (-u * t)).comp u h_inner
      have h_mul : HasDerivAt (fun u : ℝ => u * Real.exp (-u * t))
          (Real.exp (-u * t) + u * ((-t) * Real.exp (-u * t))) u := by
        simpa [mul_assoc, add_comm, add_left_comm, add_assoc] using (hasDerivAt_id u).mul h_exp'
      have hF1 :
          HasDerivAt (fun u : ℝ => -(u * Real.exp (-u * t)) / t)
            (-(Real.exp (-u * t) + u * ((-t) * Real.exp (-u * t))) / t) u := by
        have h_neg : HasDerivAt (fun x => -(x * Real.exp (-x * t)))
            (-(Real.exp (-u * t) + u * ((-t) * Real.exp (-u * t)))) u := h_mul.neg
        have h_div : HasDerivAt (fun x => -(x * Real.exp (-x * t)) / t)
            (-(Real.exp (-u * t) + u * ((-t) * Real.exp (-u * t))) / t) u := h_neg.div_const t
        simpa using h_div
      have hF2 :
          HasDerivAt (fun u : ℝ => (Real.exp (-u * t)) / (t ^ 2))
            (((-t) * Real.exp (-u * t)) / (t ^ 2)) u := by
        exact h_exp'.div_const (t ^ 2)
      have hF : HasDerivAt F
          (-(Real.exp (-u * t) + u * ((-t) * Real.exp (-u * t))) / t -
              ((-t) * Real.exp (-u * t)) / (t ^ 2)) u := by
        simpa [F] using hF1.sub hF2
      have : (-(Real.exp (-u * t) + u * ((-t) * Real.exp (-u * t))) / t -
              ((-t) * Real.exp (-u * t)) / (t ^ 2))
            = u * Real.exp (-u * t) := by
        have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
        field_simp [ht0, ht2]
        ring
      convert hF using 1
      have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
      field_simp [ht0, ht2]
      ring
    have hint : IntervalIntegrable (fun u : ℝ => u * Real.exp (-u * t)) volume (0 : ℝ) 1 :=
      hInt_u_exp
    have hFTC :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint
    have : (∫ u in (0 : ℝ)..1, u * Real.exp (-u * t)) = F 1 - F 0 := hFTC
    have h_eval :
        (∫ u in (0 : ℝ)..1, u * Real.exp (-u * t)) =
          (-(Real.exp (-t) / t) - Real.exp (-t) / (t ^ 2) + 1 / (t ^ 2)) := by
      simpa [F, ht0, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_assoc, mul_comm, mul_left_comm]
        using this
    have h_simp :
        (-(Real.exp (-t) / t) - Real.exp (-t) / (t ^ 2) + 1 / (t ^ 2)) =
          (1 - Real.exp (-t) * (t + 1)) / (t ^ 2) := by
      have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
      field_simp [ht0, ht2]
      ring
    exact h_eval.trans h_simp
  have hkernel : BinetKernel.Ktilde t = (1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t := by
    simpa [one_div] using (BinetKernel.Ktilde_pos (t := t) ht)
  rw [h_exp, h_u_exp, hkernel]
  have h_exp_ne : Real.exp t - 1 ≠ 0 := by
    have h1 : 1 < Real.exp t := (Real.one_lt_exp_iff).2 ht
    exact ne_of_gt (sub_pos.2 h1)
  field_simp [ht0, h_exp_ne, Real.exp_neg, pow_two]
  have h_exp_mul : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [h_exp_mul]

/-- Recurrence for the real part of the Binet integral. -/
theorem re_J_sub_re_J_add_one {x : ℝ} (hx : 0 < x) :
    (Binet.J (x : ℂ)).re - (Binet.J ((x : ℂ) + 1)).re =
      (x + 1 / 2) * Real.log (1 + 1 / x) - 1 := by
  have hx1 : 0 < x + 1 := by linarith
  have hJx : (Binet.J (x : ℂ)).re =
      ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) :=
    re_J_eq_integral_Ktilde (x := x) hx
  have hJx1 : (Binet.J ((x : ℂ) + 1)).re =
      ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * (x + 1)) := by
    simpa using (re_J_eq_integral_Ktilde (x := x + 1) hx1)
  rw [hJx, hJx1]
  have hInt_x :
      IntegrableOn (fun t : ℝ => BinetKernel.Ktilde t * Real.exp (-t * x)) (Set.Ioi 0) :=
    BinetKernel.integrable_Ktilde_exp (x := x) hx
  have hInt_x1 :
      IntegrableOn (fun t : ℝ => BinetKernel.Ktilde t * Real.exp (-t * (x + 1))) (Set.Ioi 0) :=
    BinetKernel.integrable_Ktilde_exp (x := x + 1) hx1
  have hsub :
      (∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x)) -
        (∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * (x + 1))) =
        ∫ t in Set.Ioi (0 : ℝ),
          (BinetKernel.Ktilde t * Real.exp (-t * x) - BinetKernel.Ktilde t *
            Real.exp (-t * (x + 1))) := by
    simpa [sub_eq_add_neg] using
      (MeasureTheory.integral_sub (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (hf := hInt_x) (hg := hInt_x1)).symm
  rw [hsub]
  have hintegrand :
      (fun t : ℝ =>
          BinetKernel.Ktilde t * Real.exp (-t * x) - BinetKernel.Ktilde t * Real.exp (-t * (x + 1)))
        = fun t : ℝ => BinetKernel.Ktilde t * Real.exp (-t * x) * (1 - Real.exp (-t)) := by
    funext t
    have : Real.exp (-t * (x + 1)) = Real.exp (-t * x) * Real.exp (-t) := by
      have : -t * (x + 1) = (-t * x) + (-t) := by ring
      simp [this, Real.exp_add, mul_comm]
    rw [this]
    ring
  rw [hintegrand]
  have hkernel :
      ∀ t ∈ Set.Ioi (0 : ℝ),
        BinetKernel.Ktilde t * (1 - Real.exp (-t)) =
          ∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t) := by
    intro t ht
    exact Ktilde_mul_one_sub_exp_eq_integral (t := t) ht
  have hswap1 :
      ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) * (1 - Real.exp (-t)) =
        ∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-t * x) * (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    dsimp
    have : BinetKernel.Ktilde t * Real.exp (-t * x) * (1 - Real.exp (-t)) =
        Real.exp (-t * x) * (BinetKernel.Ktilde t * (1 - Real.exp (-t))) := by ring
    rw [this, hkernel t ht]
  rw [hswap1]
  let F : ℝ → ℝ → ℝ := fun t u =>
    Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))
  have hF_int :
      Integrable (Function.uncurry F)
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    have hmeas :
        AEStronglyMeasurable (Function.uncurry F)
          ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
      have hcont : Continuous (Function.uncurry F) := by
        simpa [F] using (by
          fun_prop)
      exact hcont.aestronglyMeasurable
    refine (MeasureTheory.integrable_prod_iff hmeas).2 ?_
    constructor
    · refine (MeasureTheory.ae_restrict_iff' (μ := volume)
        (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi).2 ?_
      refine MeasureTheory.ae_of_all _ ?_
      intro t ht
      have ht0 : 0 < t := ht
      haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
        have : (volume (Set.Icc (0 : ℝ) 1)) ≠ ⊤ := by simp
        exact (MeasureTheory.isFiniteMeasure_restrict).2 this
      refine (MeasureTheory.Integrable.mono' (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
        (hg := MeasureTheory.integrable_const (c := (Real.exp (-t * x) / 2 : ℝ))) ?_ ?_)
      · have : Continuous fun u : ℝ => F t u := by
          have : Continuous fun u : ℝ => Real.exp (-t * x) := continuous_const
          have : Continuous fun u : ℝ => (1 / 2 - u) * Real.exp (-u * t) := by
            fun_prop
          exact continuous_const.mul this
        exact this.aestronglyMeasurable
      · refine (MeasureTheory.ae_restrict_iff' (μ := volume)
          (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc).2 ?_
        refine MeasureTheory.ae_of_all _ ?_
        intro u hu
        have hu' : u ∈ Set.Icc (0 : ℝ) 1 := hu
        have hu0 : 0 ≤ u := hu'.1
        have hu1 : u ≤ 1 := hu'.2
        have h_abs : |(1 / 2 - u) * Real.exp (-u * t)| ≤ (1 / 2 : ℝ) := by
          have h1 : |1 / 2 - u| ≤ (1 / 2 : ℝ) := by
            refine (abs_sub_le_iff).2 ?_
            constructor <;> linarith [hu0, hu1]
          have h2 : |Real.exp (-u * t)| ≤ (1 : ℝ) := by
            have : -u * t ≤ 0 := by
              have : 0 ≤ u * t := mul_nonneg hu0 (le_of_lt ht0)
              linarith
            have := Real.exp_le_one_iff.mpr this
            have hpos : 0 ≤ Real.exp (-u * t) := (Real.exp_pos _).le
            simpa [abs_of_nonneg hpos] using this
          calc
            |(1 / 2 - u) * Real.exp (-u * t)| = |1 / 2 - u| * |Real.exp (-u * t)| := by
                simp [abs_mul]
            _ ≤ (1 / 2 : ℝ) * 1 := by
                gcongr
            _ = (1 / 2 : ℝ) := by ring
        have h_exp_nonneg : 0 ≤ Real.exp (-t * x) := (Real.exp_pos _).le
        have :
            |F t u| ≤ Real.exp (-t * x) / 2 := by
          dsimp [F]
          have : |Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))|
              = |Real.exp (-t * x)| * |(1 / 2 - u) * Real.exp (-u * t)| := by
                simp [abs_mul]
          rw [this]
          have habs_exp : |Real.exp (-t * x)| = Real.exp (-t * x) := by
            simp
          rw [habs_exp]
          have := mul_le_mul_of_nonneg_left h_abs h_exp_nonneg
          simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this
        simpa [Real.norm_eq_abs, abs_of_nonneg h_exp_nonneg] using this
    · haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
        have : (volume (Set.Icc (0 : ℝ) 1)) ≠ ⊤ := by simp
        exact (MeasureTheory.isFiniteMeasure_restrict).2 this
      have hbound :
          ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi (0 : ℝ))),
            (∫ u : ℝ, ‖(Function.uncurry F) (t, u)‖ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
              ≤ (Real.exp (-t * x) / 2 : ℝ) := by
        refine (MeasureTheory.ae_restrict_iff' (μ := volume)
          (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi).2 ?_
        refine MeasureTheory.ae_of_all _ ?_
        intro t ht
        have ht0 : 0 < t := ht
        have h_point :
            ∀ u ∈ Set.Icc (0 : ℝ) 1,
              ‖F t u‖ ≤ (Real.exp (-t * x) / 2 : ℝ) := by
          intro u hu
          have hu0 : 0 ≤ u := hu.1
          have hu1 : u ≤ 1 := hu.2
          have h_abs : |(1 / 2 - u) * Real.exp (-u * t)| ≤ (1 / 2 : ℝ) := by
            have h1 : |1 / 2 - u| ≤ (1 / 2 : ℝ) := by
              have : |u - (1 / 2 : ℝ)| ≤ (1 / 2 : ℝ) := by
                refine (abs_sub_le_iff).2 ?_
                constructor <;> linarith [hu0, hu1]
              simpa [abs_sub_comm] using this
            have h2 : |Real.exp (-u * t)| ≤ (1 : ℝ) := by
              have : -u * t ≤ 0 := by
                have : 0 ≤ u * t := mul_nonneg hu0 (le_of_lt ht0)
                linarith
              have hexp : Real.exp (-u * t) ≤ (1 : ℝ) := Real.exp_le_one_iff.mpr this
              have hpos : 0 ≤ Real.exp (-u * t) := (Real.exp_pos _).le
              simpa [abs_of_nonneg hpos] using hexp
            calc
              |(1 / 2 - u) * Real.exp (-u * t)| = |1 / 2 - u| * |Real.exp (-u * t)| := by
                  simp [abs_mul]
              _ ≤ (1 / 2 : ℝ) * 1 := by
                  gcongr
              _ = (1 / 2 : ℝ) := by ring
          have h_exp_nonneg : 0 ≤ Real.exp (-t * x) := (Real.exp_pos _).le
          have :
              |F t u| ≤ Real.exp (-t * x) / 2 := by
            dsimp [F]
            calc
              |Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))|
                  = Real.exp (-t * x) * |(1 / 2 - u) * Real.exp (-u * t)| := by
                      simp [abs_mul]
              _ ≤ Real.exp (-t * x) * (1 / 2 : ℝ) := by
                      gcongr
              _ = Real.exp (-t * x) / 2 := by ring
          simpa [Real.norm_eq_abs] using this
        have hmono :
            (fun u : ℝ => ‖F t u‖) ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
              fun _u : ℝ => (Real.exp (-t * x) / 2 : ℝ) := by
          refine (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Set.Icc (0 : ℝ) 1)
            measurableSet_Icc).2 ?_
          refine MeasureTheory.ae_of_all _ ?_
          intro u hu
          exact h_point u hu
        have hconst :
            (∫ u : ℝ, (Real.exp (-t * x) / 2 : ℝ) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
              = Real.exp (-t * x) / 2 := by
          simp
        have hF_integrable : Integrable (fun u : ℝ => F t u) (volume.restrict
            (Set.Icc (0 : ℝ) 1)) := by
          apply Continuous.integrableOn_Icc
          unfold F
          fun_prop
        have hconst_integrable : Integrable (fun _u : ℝ => (Real.exp (-t * x) / 2 : ℝ))
            (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) := by
          exact integrable_const _
        have habs_integrable : Integrable (fun u : ℝ => |F t u|)
            (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) := by
          exact hF_integrable.abs
        have hmono' :
            (fun u : ℝ => |F t u|) ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
              fun _u : ℝ => (Real.exp (-t * x) / 2 : ℝ) := by
          simp_rw [Real.norm_eq_abs] at hmono
          exact hmono
        have := MeasureTheory.integral_mono_ae habs_integrable hconst_integrable hmono'
        simpa [hconst] using this
      have hdom : Integrable (fun t : ℝ => (Real.exp (-t * x) / 2 : ℝ))
          (volume.restrict (Set.Ioi (0 : ℝ))) := by
        have hx' : 0 < x := hx
        have : IntegrableOn (fun t : ℝ => Real.exp (-t * x)) (Set.Ioi 0) := by
          have h := integrableOn_exp_mul_Ioi (a := -x) (c := (0:ℝ)) (by linarith : (-x : ℝ) < 0)
          simpa [mul_assoc, mul_comm, mul_left_comm] using h
        have h2 : IntegrableOn (fun t => Real.exp (-t * x) / 2) (Set.Ioi 0) := by
          simp only [div_eq_mul_inv]
          exact this.mul_const (2⁻¹)
        exact h2.integrable
      refine (MeasureTheory.Integrable.mono' (μ := volume.restrict (Set.Ioi (0 : ℝ))) (hg := hdom)
        ?_ ?_)
      · have hmeas' :
            AEStronglyMeasurable
              (fun t : ℝ =>
                ∫ u : ℝ, ‖(Function.uncurry F) (t, u)‖ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
              (volume.restrict (Set.Ioi (0 : ℝ))) := by
          have hF_meas' : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖Function.uncurry F p‖)
              ((volume.restrict (Set.Ioi (0 : ℝ))).prod
                (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
            exact AEStronglyMeasurable.norm hmeas
          exact AEStronglyMeasurable.integral_prod_right' hF_meas'
        exact hmeas'
      · filter_upwards [hbound] with t ht
        calc ‖∫ u : ℝ, ‖Function.uncurry F (t, u)‖ ∂volume.restrict (Icc 0 1)‖
            = ∫ u : ℝ, ‖Function.uncurry F (t, u)‖ ∂volume.restrict (Icc 0 1) := by
              apply Real.norm_of_nonneg
              apply MeasureTheory.integral_nonneg
              intro u
              exact norm_nonneg _
          _ ≤ rexp (-t * x) / 2 := ht
  have hswap :
      ∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-t * x) * (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t))
        =
        ∫ u in Set.Icc (0 : ℝ) 1,
          ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t)) := by
    have hswap0 :
        (∫ t in Set.Ioi (0 : ℝ), ∫ u in Set.Icc (0 : ℝ) 1, F t u) =
          ∫ u in Set.Icc (0 : ℝ) 1, ∫ t in Set.Ioi (0 : ℝ), F t u := by
      simpa [Function.uncurry] using
      (MeasureTheory.integral_integral_swap (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (ν := volume.restrict (Set.Icc (0 : ℝ) 1)) (f := fun t u => F t u) hF_int)
    have hLHS :
        (∫ t in Set.Ioi (0 : ℝ), ∫ u in Set.Icc (0 : ℝ) 1, F t u) =
          ∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-t * x) * (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t)) := by
      refine MeasureTheory.integral_congr_ae ?_
      refine (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi).2 ?_
      refine MeasureTheory.ae_of_all _ ?_
      intro t ht
      have :
          (∫ u in Set.Icc (0 : ℝ) 1, F t u) =
            Real.exp (-t * x) * ∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t) := by
        simp [F, MeasureTheory.integral_const_mul]
      simp [this]
    have hswap1 :
        (∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-t * x) * (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t))) =
          ∫ u in Set.Icc (0 : ℝ) 1, ∫ t in Set.Ioi (0 : ℝ), F t u := by
      calc
        (∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-t * x) * (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t)))
            =
            ∫ t in Set.Ioi (0 : ℝ), ∫ u in Set.Icc (0 : ℝ) 1, F t u := by
              simpa using hLHS.symm
        _ = ∫ u in Set.Icc (0 : ℝ) 1, ∫ t in Set.Ioi (0 : ℝ), F t u := hswap0
    simpa [F] using hswap1
  rw [hswap]
  have hx0 : x ≠ 0 := ne_of_gt hx
  have h_inner :
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t)))
          = (1 / 2 - u) * (1 / (x + u)) := by
    intro u hu
    have hu0 : 0 ≤ u := hu.1
    have hxu : 0 < x + u := by linarith [hx, hu0]
    have hmul :
        (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))) =
          (1 / 2 - u) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * (x + u))) := by
      have hrew : (fun t : ℝ => Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))) =
          fun t : ℝ => (1 / 2 - u) * Real.exp (-(t * (x + u))) := by
        funext t
        have hexp :
            Real.exp (-t * x) * Real.exp (-u * t) = Real.exp ((-t * x) + (-u * t)) := by
          simpa using (Real.exp_add (-t * x) (-u * t)).symm
        have hadd : (-t * x) + (-u * t) = -(t * (x + u)) := by ring
        calc
          Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))
              = (1 / 2 - u) * (Real.exp (-t * x) * Real.exp (-u * t)) := by
                  ring
          _ = (1 / 2 - u) * Real.exp ((-t * x) + (-u * t)) := by
                  simpa using congrArg (fun y => (1 / 2 - u) * y) hexp
          _ = (1 / 2 - u) * Real.exp (-(t * (x + u))) := by
                  simpa using congrArg (fun y => (1 / 2 - u) * Real.exp y) hadd
      have hrew_int :
          (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))) =
            ∫ t in Set.Ioi (0 : ℝ), (1 / 2 - u) * Real.exp (-(t * (x + u))) := by
        simpa using congrArg (fun f : ℝ → ℝ => ∫ t in Set.Ioi (0 : ℝ), f t) hrew
      calc
        (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t)))
            = ∫ t in Set.Ioi (0 : ℝ), (1 / 2 - u) * Real.exp (-(t * (x + u))) := hrew_int
        _ = (1 / 2 - u) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * (x + u))) := by
            simp [MeasureTheory.integral_const_mul]
    have hbase : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * (x + u)))) = 1 / (x + u) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using (integral_exp_neg_mul_Ioi (x := x + u) hxu)
    calc
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t)))
          = (1 / 2 - u) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * (x + u))) := hmul
      _ = (1 / 2 - u) * (1 / (x + u)) := by simp [hbase]
  have h_inner_int :
      (∫ u in Set.Icc (0 : ℝ) 1,
          ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t)))
        = ∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * (1 / (x + u)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro u hu
    exact h_inner u hu
  rw [h_inner_int]
  have hrew_u :
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        (1 / 2 - u) * (1 / (x + u)) = (x + 1 / 2) * (1 / (x + u)) - 1 := by
    intro u hu
    have hu0 : 0 ≤ u := hu.1
    have hx_u : x + u ≠ 0 := by
      have : 0 < x + u := by linarith [hx, hu0]
      exact ne_of_gt this
    field_simp [hx_u]
    ring_nf
  have hrew_u_int :
      (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * (1 / (x + u))) =
        ∫ u in Set.Icc (0 : ℝ) 1, ((x + 1 / 2) * (1 / (x + u)) - 1) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro u hu
    simpa using hrew_u u hu
  rw [hrew_u_int]
  have hxpos : 0 < x := hx
  have h_shift :
      (∫ u in Set.Icc (0 : ℝ) 1, (1 / (x + u) : ℝ)) = Real.log (1 + 1 / x) := by
    have hIcc :
        (∫ u in Set.Icc (0 : ℝ) 1, (1 / (x + u) : ℝ)) = ∫ u in (0 : ℝ)..1, (1 / (x + u) : ℝ) := by
      have hIccIoc :
          (∫ u in Set.Icc (0 : ℝ) 1, (1 / (x + u) : ℝ)) =
            ∫ u in Set.Ioc (0 : ℝ) 1, (1 / (x + u) : ℝ) := by
        simpa using
          (MeasureTheory.integral_Icc_eq_integral_Ioc
            (μ := (volume : Measure ℝ)) (f := fun u : ℝ => (1 / (x + u) : ℝ))
            (x := (0 : ℝ)) (y := (1 : ℝ)))
      have hIoc :
          ∫ u in Set.Ioc (0 : ℝ) 1, (1 / (x + u) : ℝ) = ∫ u in (0 : ℝ)..1, (1 / (x + u) : ℝ) := by
        simpa using
          (intervalIntegral.integral_of_le (μ := (volume : Measure ℝ))
            (a := (0 : ℝ)) (b := (1 : ℝ)) (f := fun u : ℝ => (1 / (x + u) : ℝ))
            (by norm_num : (0 : ℝ) ≤ 1)).symm
      exact hIccIoc.trans hIoc
    rw [hIcc]
    have hshift' :
        (∫ u in (0 : ℝ)..1, (1 / (x + u) : ℝ)) = ∫ u in x..(x + 1), (1 / u : ℝ) := by
      simp
    rw [hshift']
    have hx0' : (0 : ℝ) ∉ Set.uIcc x (x + 1) := by
      intro hxmem
      have hxle : x ≤ x + 1 := by linarith
      have hxmem' : (0 : ℝ) ∈ Set.Icc x (x + 1) := by
        simpa [Set.uIcc, hxle, min_eq_left hxle, max_eq_right hxle] using hxmem
      have hx_le0 : x ≤ (0 : ℝ) := (Set.mem_Icc.1 hxmem').1
      linarith [hxpos, hx_le0]
    have hinv : (∫ u in x..(x + 1), (u : ℝ)⁻¹) = Real.log ((x + 1) / x) := by
      simpa [one_div] using (integral_inv (a := x) (b := x + 1) hx0')
    have hdiv : (x + 1) / x = 1 + 1 / x := by
      field_simp [hx0]
    simpa [one_div, hdiv] using hinv
  have hI1 : (∫ u in Set.Icc (0 : ℝ) 1, (1 : ℝ)) = 1 := by simp
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hInt_inv :
      Integrable (fun u : ℝ => (x + u)⁻¹) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    refine (MeasureTheory.Integrable.mono' (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
      (hg := MeasureTheory.integrable_const (c := ‖(x⁻¹ : ℝ)‖)) ?_ ?_)
    · exact (Measurable.inv ((measurable_const.add measurable_id))).aestronglyMeasurable
    · refine (MeasureTheory.ae_restrict_iff' (μ := volume)
        (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc).2 ?_
      refine MeasureTheory.ae_of_all _ ?_
      intro u hu
      have hu0 : 0 ≤ u := hu.1
      have hxle : x ≤ x + u := by linarith
      have hxpos' : 0 < x := hxpos
      have hxupos : 0 < x + u := lt_of_lt_of_le hxpos' hxle
      have : (x + u)⁻¹ ≤ x⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hxpos' hxle
      have hnorm1 : ‖(x + u)⁻¹‖ = (x + u)⁻¹ := by
        simp [Real.norm_eq_abs, abs_of_pos hxupos]
      have hnorm2 : ‖(x⁻¹ : ℝ)‖ = x⁻¹ := by
        simp [Real.norm_eq_abs, abs_of_pos hxpos']
      simpa [hnorm1, hnorm2] using this
  have hInt_mul :
      Integrable (fun u : ℝ => (x + (1 / 2 : ℝ)) * (x + u)⁻¹)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hInt_inv.const_mul (x + (1 / 2 : ℝ))
  have hInt_const :
      Integrable (fun _u : ℝ => (-1 : ℝ)) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    integrable_const _
  have hadd :
      (∫ u in Set.Icc (0 : ℝ) 1, (-1 : ℝ) + (x + (1 / 2 : ℝ)) * (x + u)⁻¹) =
        (∫ u in Set.Icc (0 : ℝ) 1, (-1 : ℝ)) +
          ∫ u in Set.Icc (0 : ℝ) 1, (x + (1 / 2 : ℝ)) * (x + u)⁻¹ := by
    simpa using
      (MeasureTheory.integral_add (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) hInt_const hInt_mul)
  have hmul_shift :
      (∫ u in Set.Icc (0 : ℝ) 1, (x + (1 / 2 : ℝ)) * (x + u)⁻¹)
        = (x + (1 / 2 : ℝ)) * Real.log (1 + 1 / x) := by
    calc
      (∫ u in Set.Icc (0 : ℝ) 1, (x + (1 / 2 : ℝ)) * (x + u)⁻¹)
          = (x + (1 / 2 : ℝ)) * ∫ u in Set.Icc (0 : ℝ) 1, (x + u)⁻¹ := by
              simp [MeasureTheory.integral_const_mul]
      _ = (x + (1 / 2 : ℝ)) * Real.log (1 + 1 / x) := by
              simpa [one_div] using congrArg (fun z => (x + (1 / 2 : ℝ)) * z) h_shift
  have hconst : (∫ u in Set.Icc (0 : ℝ) 1, (-1 : ℝ)) = -1 := by simp
  have hrew_goal :
      (∫ u in Set.Icc (0 : ℝ) 1, (x + (1 / 2 : ℝ)) * (1 / (x + u)) - 1) =
        ∫ u in Set.Icc (0 : ℝ) 1, (-1 : ℝ) + (x + (1 / 2 : ℝ)) * (x + u)⁻¹ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro u hu
    simp [one_div, sub_eq_add_neg, add_comm, mul_comm]
  rw [hrew_goal]
  calc
    ∫ u in Set.Icc (0 : ℝ) 1, (-1 : ℝ) + (x + (1 / 2 : ℝ)) * (x + u)⁻¹
        = (-1) + (x + (1 / 2 : ℝ)) * Real.log (1 + 1 / x) := by
            rw [hadd, hconst, hmul_shift]
    _ = (x + (1 / 2 : ℝ)) * Real.log (1 + 1 / x) - 1 := by ring

--set_option maxHeartbeats 0 in
-- Heartbeat-heavy: `log_Gamma_real_eq` is a long automation-driven proof (integrals + inequalities).
/-- Binet's formula for real arguments. -/
theorem log_Gamma_real_eq {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1/2) * Real.log x - x + Real.log (2 * Real.pi) / 2 + (J x).re := by
  have hR : R x = (Binet.J (x : ℂ)).re := by
    let h : ℝ → ℝ := fun y => R y - (Binet.J (y : ℂ)).re
    have h_periodic : ∀ y, 0 < y → h y = h (y + 1) := by
      intro y hy
      have hy1 : 0 < y + 1 := by linarith
      have hRrec := R_sub_R_add_one (x := y) hy
      have hJrec := re_J_sub_re_J_add_one (x := y) hy
      have hdiff : R y - R (y + 1) = (Binet.J (y : ℂ)).re - (Binet.J ((y : ℂ) + 1)).re := by
        calc
          R y - R (y + 1)
              = (y + 1 / 2) * Real.log (1 + 1 / y) - 1 := hRrec
          _ = (Binet.J (y : ℂ)).re - (Binet.J ((y : ℂ) + 1)).re := by
              simpa using hJrec.symm
      dsimp [h]
      have heq :
          R y - (Binet.J (y : ℂ)).re = R (y + 1) - (Binet.J ((y : ℂ) + 1)).re := by
        linarith [hdiff]
      simpa using heq
    have hRlim : Tendsto R atTop (𝓝 0) := by
      have hnat : Tendsto (fun n : ℕ => R (n : ℝ)) atTop (𝓝 0) := by
        have hst : Tendsto Stirling.stirlingSeq atTop (𝓝 (Real.sqrt Real.pi)) :=
          Stirling.tendsto_stirlingSeq_sqrt_pi
        have hlogst : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n))
            atTop (𝓝 (Real.log (Real.sqrt Real.pi))) :=
          (Real.continuousAt_log (by
            have : (0 : ℝ) < Real.sqrt Real.pi := by
              have : (0 : ℝ) < Real.pi := Real.pi_pos
              simpa using Real.sqrt_pos.2 this
            exact ne_of_gt this)).tendsto.comp hst
        have hπ : Real.log (Real.sqrt Real.pi) = Real.log Real.pi / 2 := by
          simpa using (Real.log_sqrt (x := Real.pi) (by exact le_of_lt Real.pi_pos))
        have hR_eq :
            (fun n : ℕ => R (n : ℝ)) =ᶠ[atTop]
              fun n : ℕ => Real.log (Stirling.stirlingSeq n) - Real.log Real.pi / 2 := by
          filter_upwards [eventually_gt_atTop 0] with n hn
          have hn0 : (n : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hn)
          have hGamma_n :
              Real.Gamma (n : ℝ) = ((n - 1)! : ℝ) := by
            have hn' : 0 < n := hn
            have hn_succ : (n - 1).succ = n := Nat.succ_pred_eq_of_pos hn'
            have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
              have := congrArg (fun k : ℕ => (k : ℝ)) hn_succ
              simpa [Nat.cast_succ] using this
            have hGamma := Real.Gamma_nat_eq_factorial (n - 1)
            simpa [hcast, Nat.cast_add, Nat.cast_one, add_assoc] using hGamma
          have hlogGamma :
              Real.log (Real.Gamma (n : ℝ)) = Real.log (n ! : ℝ) - Real.log (n : ℝ) := by
            have hn_fact_ne : ((n ! : ℕ) : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.factorial_ne_zero n)
            have hpred_fact_ne : (((n - 1)! : ℕ) : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.factorial_ne_zero (n - 1))
            have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
            have hfac : (n ! : ℝ) = (n : ℝ) * ((n - 1)! : ℝ) := by
              have hn_succ : (n - 1).succ = n := Nat.succ_pred_eq_of_pos hn
              have : (n ! : ℝ) = (n : ℝ) * ((n - 1)! : ℝ) := by
                have hn_pos : 0 < n := hn
                have hn' : (n - 1 + 1) = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn_pos)
                have hnat : ((n - 1 + 1) ! : ℕ) = (n - 1 + 1) * (n - 1)! :=
                  Nat.factorial_succ (n - 1)
                have := congrArg (fun k : ℕ => (k : ℝ)) hnat
                simpa [hn', Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc,
                  mul_comm, mul_left_comm] using this
              exact this
            have hlog_mul : Real.log (n ! : ℝ) = Real.log (n : ℝ) + Real.log ((n - 1)! : ℝ) := by
              have h : Real.log ((n : ℝ) * ((n - 1)! : ℝ)) =
                  Real.log (n : ℝ) + Real.log ((n - 1)! : ℝ) := by
                simpa using Real.log_mul (x := (n : ℝ)) (y := ((n - 1)! : ℝ)) hn_ne hpred_fact_ne
              simpa [hfac, mul_comm, add_comm, add_left_comm, add_assoc] using h
            have : Real.log ((n - 1)! : ℝ) = Real.log (n ! : ℝ) - Real.log (n : ℝ) := by
              linarith
            simp [hGamma_n, this]
          have hn' : n ≠ 0 := Nat.ne_of_gt hn
          have hlogst_formula := Stirling.log_stirlingSeq_formula n
          unfold R stirlingMainReal at *
          have hn_pos_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
          have hlog_pi2 : Real.log (Real.pi * 2) = Real.log Real.pi + Real.log 2 := by
            simpa [mul_comm] using Real.log_mul (Real.pi_pos.ne') (by norm_num : (2 : ℝ) ≠ 0)
          have hlogst_formula' :
              Real.log (Stirling.stirlingSeq n) =
                Real.log (n ! : ℝ) - (1 / 2 : ℝ) * (Real.log 2 + Real.log (n : ℝ))
                  - (n : ℝ) * (Real.log (n : ℝ) - 1) := by
            have hn_pos_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
            have hn_ne : (n : ℝ) ≠ 0 := hn_pos_real.ne'
            have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
            have hlog_2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log (n : ℝ) := by
              simpa using Real.log_mul h2_ne hn_ne
            have hlog_div : Real.log ((n : ℝ) / Real.exp 1) = Real.log (n : ℝ) - 1 := by
              simpa [Real.log_exp, sub_eq_add_neg] using
                (Real.log_div hn_ne (Real.exp_pos 1).ne')
            have h0 := Stirling.log_stirlingSeq_formula n
            have h0' :
                Real.log (Stirling.stirlingSeq n) =
                  Real.log (n ! : ℝ) - (1 / 2 : ℝ) * Real.log (2 * (n : ℝ))
                    - (n : ℝ) * Real.log ((n : ℝ) / Real.exp 1) := by
              simpa [Stirling.stirlingSeq, sub_eq_add_neg, one_div, mul_assoc, mul_left_comm,
                mul_comm, add_assoc, add_left_comm, add_comm] using h0
            calc
              Real.log (Stirling.stirlingSeq n)
                  = Real.log (n ! : ℝ) - (1 / 2 : ℝ) * Real.log (2 * (n : ℝ))
                      - (n : ℝ) * Real.log ((n : ℝ) / Real.exp 1) := h0'
              _ = Real.log (n ! : ℝ) - (1 / 2 : ℝ) * (Real.log 2 + Real.log (n : ℝ))
                    - (n : ℝ) * (Real.log (n : ℝ) - 1) := by
                  simp [hlog_2n, hlog_div]
          simp [hlogGamma, hlogst_formula', hlog_pi2, sub_eq_add_neg,
            mul_add, add_mul, mul_comm]
          ring_nf
        have h_tendsto :
            Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) -
              Real.log Real.pi / 2) atTop (𝓝 0) :=
          by simpa [hπ, sub_eq_add_neg, add_assoc] using hlogst.sub_const (Real.log Real.pi / 2)
        exact (tendsto_congr' hR_eq).2 h_tendsto
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hnat' := (Metric.tendsto_atTop).1 hnat (ε / 2) (by positivity)
      rcases hnat' with ⟨N1, hN1⟩
      have h_inv : Tendsto (fun n : ℕ => (3 : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
        have : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
          tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
        simpa [div_eq_mul_inv, mul_assoc] using (this.const_mul (3 : ℝ))
      have h_inv' := (Metric.tendsto_atTop).1 h_inv (ε / 2) (by positivity)
      rcases h_inv' with ⟨N2, hN2⟩
      let N : ℕ := max (max N1 N2) 2
      refine ⟨(N : ℝ) + 1, ?_⟩
      intro y hy
      have hy0 : 0 ≤ y := by linarith
      let n : ℕ := ⌊y⌋₊
      have hn_le : (n : ℝ) ≤ y := Nat.floor_le hy0
      have hy_lt : y < (n : ℝ) + 1 := Nat.lt_floor_add_one y
      have hn_ge : N ≤ n := by
        by_contra h
        have hn_lt : n < N := Nat.lt_of_not_ge h
        have : y < (N : ℝ) := (Nat.floor_lt hy0).1 hn_lt
        linarith
      have hn2 : 2 ≤ n := le_trans (by exact le_max_right _ _) hn_ge
      have hn_pos : 0 < (n : ℝ) := by
        have : (0 : ℝ) < (2 : ℝ) := by norm_num
        exact this.trans_le (by exact_mod_cast hn2)
      have hn1_pos : 0 < (n - 1 : ℕ) := by
        exact Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hn2)
      have ha0 : 0 ≤ y - n := sub_nonneg.2 hn_le
      have ha1 : y - n < 1 := by
        have : y < (n : ℝ) + 1 := hy_lt
        linarith
      have ha_le : y - n ≤ 1 := le_of_lt ha1
      have hf := Real.convexOn_log_Gamma
      have h_upper :
          Real.log (Real.Gamma y) ≤
            Real.log (Real.Gamma (n : ℝ)) + (y - n) * Real.log (n : ℝ) := by
        by_cases hy_eq : y = (n : ℝ)
        · have hy_sub : y - n = 0 := by linarith [hy_eq]
          simp [hy_eq]
        · have hn_mem : (n : ℝ) ∈ Set.Ioi (0 : ℝ) := hn_pos
          have hy_mem : y ∈ Set.Ioi (0 : ℝ) := lt_of_lt_of_le hn_pos hn_le
          have hn1_mem : (n : ℝ) + 1 ∈ Set.Ioi (0 : ℝ) := by
            have : (0 : ℝ) < (n : ℝ) + 1 := by linarith [hn_pos]
            simpa using this
          have hn1_ne : (n : ℝ) + 1 ≠ (n : ℝ) := by linarith
          have hsec :=
            ConvexOn.secant_mono (f := fun z : ℝ => Real.log (Real.Gamma z)) hf
              hn_mem hy_mem hn1_mem hy_eq hn1_ne (le_of_lt hy_lt)
          have hdiff :
              (Real.log (Real.Gamma y) - Real.log (Real.Gamma (n : ℝ))) / (y - n) ≤
                Real.log (Real.Gamma ((n : ℝ) + 1)) - Real.log (Real.Gamma (n : ℝ)) := by
            simpa using hsec
          have hy_n_pos : 0 < y - n := sub_pos.2 (lt_of_le_of_ne hn_le (Ne.symm hy_eq))
          have := (div_le_iff₀ hy_n_pos).1 hdiff
          have hstep :
              Real.log (Real.Gamma ((n : ℝ) + 1)) - Real.log (Real.Gamma (n : ℝ)) =
                Real.log (n : ℝ) := by
            have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
            have hΓ : Real.Gamma ((n : ℝ) + 1) = (n : ℝ) * Real.Gamma (n : ℝ) := Real.Gamma_add_one
              (s := (n : ℝ)) hn_ne
            have hΓn_ne : Real.Gamma (n : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos hn_pos).ne'
            calc
              Real.log (Real.Gamma ((n : ℝ) + 1)) - Real.log (Real.Gamma (n : ℝ))
                  = (Real.log (n : ℝ) + Real.log (Real.Gamma (n : ℝ))) - Real.log (Real.Gamma
                      (n : ℝ)) := by
                    simp [hΓ, Real.log_mul hn_ne hΓn_ne]
              _ = Real.log (n : ℝ) := by ring
          have hmul :
              Real.log (Real.Gamma y) - Real.log (Real.Gamma (n : ℝ)) ≤
                Real.log (n : ℝ) * (y - n) := by
            simpa [hstep] using this
          have := add_le_add_left hmul (Real.log (Real.Gamma (n : ℝ)))
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
            mul_comm] using this
      have h_lower :
          Real.log (Real.Gamma y) ≥
            Real.log (Real.Gamma (n : ℝ)) + (y - n) * Real.log ((n - 1 : ℕ) : ℝ) := by
        by_cases hy_eq : y = (n : ℝ)
        · have hy_sub : y - n = 0 := by linarith [hy_eq]
          simp [hy_eq]
        · -have hn_1_mem : ((n - 1 : ℕ) : ℝ) ∈ Set.Ioi (0 : ℝ) := by
            have : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast hn1_pos
            simpa using this
          have hn_mem : (n : ℝ) ∈ Set.Ioi (0 : ℝ) := hn_pos
          have hy_mem : y ∈ Set.Ioi (0 : ℝ) := lt_of_lt_of_le hn_pos hn_le
          have hn_nat_pos : 0 < n := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn2
          have hn1_ne : ((n - 1 : ℕ) : ℝ) ≠ (n : ℝ) := by
            have hlt : n - 1 < n := Nat.sub_lt_self (Nat.succ_pos 0) hn_nat_pos
            exact ne_of_lt (by exact_mod_cast hlt : ((n - 1 : ℕ) : ℝ) < (n : ℝ))
          have hn1_le_n : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast (Nat.sub_le n 1)
          have hn1_le_y : ((n - 1 : ℕ) : ℝ) ≤ y := le_trans hn1_le_n hn_le
          have hsec :=
            ConvexOn.secant_mono (f := fun z : ℝ => Real.log (Real.Gamma z)) hf
              hn_mem hn_1_mem hy_mem hn1_ne hy_eq hn1_le_y
          have hdiff :
              (Real.log (Real.Gamma ((n - 1 : ℕ) : ℝ)) - Real.log (Real.Gamma (n : ℝ))) /
                    (((n - 1 : ℕ) : ℝ) - (n : ℝ)) ≤
                (Real.log (Real.Gamma y) - Real.log (Real.Gamma (n : ℝ))) / (y - n) := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsec
          have hy_n_pos : 0 < y - n := sub_pos.2 (lt_of_le_of_ne hn_le (Ne.symm hy_eq))
          have hy_gt_n : (n : ℝ) < y := lt_of_le_of_ne hn_le (Ne.symm hy_eq)
          have hleft :
              (Real.log (Real.Gamma ((n - 1 : ℕ) : ℝ)) - Real.log (Real.Gamma (n : ℝ))) /
                    (((n - 1 : ℕ) : ℝ) - (n : ℝ)) =
                Real.log ((n - 1 : ℕ) : ℝ) := by
            have hn1_ne0 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn1_pos)
            have hΓ :
                Real.Gamma (n : ℝ) =
                  ((n - 1 : ℕ) : ℝ) * Real.Gamma ((n - 1 : ℕ) : ℝ) := by
              have hnat : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn_nat_pos)
              have hcast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
                exact_mod_cast hnat.symm
              have hΓ' := Real.Gamma_add_one (s := ((n - 1 : ℕ) : ℝ)) hn1_ne0
              simpa [hcast, add_comm, add_left_comm, add_assoc] using hΓ'
            have hΓn1_ne : Real.Gamma ((n - 1 : ℕ) : ℝ) ≠ 0 :=
              (Real.Gamma_pos_of_pos (by exact_mod_cast hn1_pos)).ne'
            have hlog :
                Real.log (Real.Gamma (n : ℝ)) =
                  Real.log ((n - 1 : ℕ) : ℝ) + Real.log (Real.Gamma ((n - 1 : ℕ) : ℝ)) := by
              simp [hΓ, Real.log_mul hn1_ne0 hΓn1_ne]
            have hnum :
                Real.log (Real.Gamma ((n - 1 : ℕ) : ℝ)) - Real.log (Real.Gamma (n : ℝ)) =
                  - Real.log ((n - 1 : ℕ) : ℝ) := by
              linarith [hlog]
            have hden : (((n - 1 : ℕ) : ℝ) - (n : ℝ)) = (-1 : ℝ) := by
              have hnat : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn_nat_pos)
              have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hnat
              linarith
            simp [hnum, hden]
          have hmul := (le_div_iff₀ hy_n_pos).1 (by simpa [hleft] using hdiff)
          have := add_le_add_left hmul (Real.log (Real.Gamma (n : ℝ)))
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
            mul_comm] using this
      have hn0' : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
      have hR_upper : R y ≤ R (n : ℝ) + 1 / (n : ℝ) := by
        have hy_pos : 0 < y := lt_of_lt_of_le hn_pos hn_le
        have hy_ne : y ≠ 0 := ne_of_gt hy_pos
        have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
        have hlog_ge :
            (y - (n : ℝ)) / y ≤ Real.log y - Real.log (n : ℝ) := by
          have hx_pos : 0 < y / (n : ℝ) := div_pos hy_pos hn_pos
          have h0 : 1 - (y / (n : ℝ))⁻¹ ≤ Real.log (y / (n : ℝ)) :=
            Real.one_sub_inv_le_log_of_pos (x := y / (n : ℝ)) hx_pos
          have hL : 1 - (y / (n : ℝ))⁻¹ = (y - (n : ℝ)) / y := by
            field_simp [hy_ne, hn_ne]
          have hR : Real.log (y / (n : ℝ)) = Real.log y - Real.log (n : ℝ) := by
            simpa using (Real.log_div (x := y) (y := (n : ℝ)) hy_ne hn_ne)
          have h0' : (y - (n : ℝ)) / y ≤ Real.log y - Real.log (n : ℝ) := by
            have h0'' : (y - (n : ℝ)) / y ≤ Real.log (y / (n : ℝ)) := by
              have htmp := h0
              rw [hL] at htmp
              exact htmp
            simpa [hR] using h0''
          exact h0'
        have hΔ :
            stirlingMainReal (n : ℝ) + (y - (n : ℝ)) * Real.log (n : ℝ) - stirlingMainReal y ≤
              1 / (n : ℝ) := by
          have hΔ_eq :
              stirlingMainReal (n : ℝ) + (y - (n : ℝ)) * Real.log (n : ℝ) - stirlingMainReal y =
                (y - (n : ℝ)) - (y - (1 / 2 : ℝ)) * (Real.log y - Real.log (n : ℝ)) := by
            unfold stirlingMainReal
            ring
          have hy1 : 0 ≤ y - (1 / 2 : ℝ) := by linarith [hy]
          have hΔ_le :
              (y - (n : ℝ)) - (y - (1 / 2 : ℝ)) * (Real.log y - Real.log (n : ℝ)) ≤
                (y - (n : ℝ)) - (y - (1 / 2 : ℝ)) * ((y - (n : ℝ)) / y) := by
            have hmul := mul_le_mul_of_nonneg_left hlog_ge hy1
            linarith
          have hΔ_simp :
              (y - (n : ℝ)) - (y - (1 / 2 : ℝ)) * ((y - (n : ℝ)) / y) =
                (y - (n : ℝ)) / (2 * y) := by
            field_simp [hy_ne]
            ring
          have hΔ_bound : (y - (n : ℝ)) / (2 * y) ≤ 1 / (n : ℝ) := by
            have h2y_pos : 0 < 2 * y := by nlinarith [hy_pos]
            have h2n_pos : 0 < 2 * (n : ℝ) := by nlinarith [hn_pos]
            have hstep1 :
                (y - (n : ℝ)) / (2 * y) ≤ 1 / (2 * y) := by
              refine div_le_div_of_nonneg_right ?_ (le_of_lt h2y_pos)
              linarith [ha_le]
            have hstep2 :
                (1 : ℝ) / (2 * y) ≤ 1 / (2 * (n : ℝ)) := by
              have hle : 2 * (n : ℝ) ≤ 2 * y := by nlinarith [hn_le]
              exact one_div_le_one_div_of_le h2n_pos hle
            have hstep3 :
                (1 : ℝ) / (2 * (n : ℝ)) ≤ 1 / (n : ℝ) := by
              have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
              have hnonneg : 0 ≤ (1 / (n : ℝ) : ℝ) := one_div_nonneg.2 (le_of_lt hn_pos)
              have hrew : (1 : ℝ) / (2 * (n : ℝ)) = (1 / (n : ℝ)) / 2 := by
                field_simp [hn0]
              have : (1 / (n : ℝ)) / 2 ≤ (1 / (n : ℝ)) :=
                div_le_self hnonneg (by norm_num : (1 : ℝ) ≤ 2)
              rw [hrew]
              exact this
            exact le_trans hstep1 (le_trans hstep2 hstep3)
          calc
            stirlingMainReal (n : ℝ) + (y - (n : ℝ)) * Real.log (n : ℝ) - stirlingMainReal y
                = (y - (n : ℝ)) - (y - (1 / 2 : ℝ)) * (Real.log y - Real.log (n : ℝ)) := hΔ_eq
            _ ≤ (y - (n : ℝ)) - (y - (1 / 2 : ℝ)) * ((y - (n : ℝ)) / y) := hΔ_le
            _ = (y - (n : ℝ)) / (2 * y) := hΔ_simp
            _ ≤ 1 / (n : ℝ) := hΔ_bound
        have : Real.log (Real.Gamma y) - stirlingMainReal y ≤
            (Real.log (Real.Gamma (n : ℝ)) - stirlingMainReal (n : ℝ)) + 1 / (n : ℝ) :=
          by linarith [h_upper, hΔ]
        simpa [R, sub_eq_add_neg, add_assoc] using this
      have hR_lower : R y ≥ R (n : ℝ) - 3 / (n : ℝ) := by
        have hy_pos : 0 < y := lt_of_lt_of_le hn_pos hn_le
        have hy_ne : y ≠ 0 := ne_of_gt hy_pos
        have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
        have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
        have hlogy_ub : Real.log y ≤ Real.log (n : ℝ) + (y - (n : ℝ)) / (n : ℝ) := by
          have hx_pos : 0 < y / (n : ℝ) := div_pos hy_pos hn_pos
          have hlog : Real.log (y / (n : ℝ)) ≤ y / (n : ℝ) - 1 :=
            Real.log_le_sub_one_of_pos (x := y / (n : ℝ)) hx_pos
          have hlog_div : Real.log (y / (n : ℝ)) = Real.log y - Real.log (n : ℝ) := by
            simpa using (Real.log_div (x := y) (y := (n : ℝ)) hy_ne hn_ne)
          have hrhs : y / (n : ℝ) - 1 = (y - (n : ℝ)) / (n : ℝ) := by
            field_simp [hn_ne]
          have : Real.log y - Real.log (n : ℝ) ≤ (y - (n : ℝ)) / (n : ℝ) := by
            simpa [hlog_div, hrhs] using hlog
          linarith
        have hlognm1 : Real.log ((n - 1 : ℕ) : ℝ) ≥ Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ) := by
          have hn_nat_pos : 0 < n := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn2
          have hn1_pos_real : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hn1_pos
          have hn1_ne0 : ((n - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hn1_pos_real
          have hlognm1' : Real.log ((n - 1 : ℕ) : ℝ) ≥
              Real.log (n : ℝ) - 1 / ((n - 1 : ℕ) : ℝ) := by
            have hx_pos : 0 < (n : ℝ) / ((n - 1 : ℕ) : ℝ) := div_pos hn_pos hn1_pos_real
            have hlog : Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤ (n : ℝ) / ((n - 1 : ℕ) : ℝ) - 1 :=
              Real.log_le_sub_one_of_pos (x := (n : ℝ) / ((n - 1 : ℕ) : ℝ)) hx_pos
            have hlog' :
                Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) =
                  Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) := by
              simpa using (Real.log_div (x := (n : ℝ)) (y := ((n - 1 : ℕ) : ℝ)) hn_ne hn1_ne0)
            have hrhs : (n : ℝ) / ((n - 1 : ℕ) : ℝ) - 1 = 1 / ((n - 1 : ℕ) : ℝ) := by
              field_simp [hn1_ne0]
              have hnat : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn_nat_pos)
              have hcast : ((n : ℝ) : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
                exact_mod_cast hnat.symm
              linarith [hcast]
            have : Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) ≤ 1 / ((n - 1 : ℕ) : ℝ) := by
              have htmp := hlog
              rw [hlog'] at htmp
              rw [hrhs] at htmp
              exact htmp
            have h1 :
                Real.log (n : ℝ) ≤ Real.log ((n - 1 : ℕ) : ℝ) + 1 / ((n - 1 : ℕ) : ℝ) := by
              have h1' : Real.log (n : ℝ) ≤ 1 / ((n - 1 : ℕ) : ℝ) + Real.log ((n - 1 : ℕ) : ℝ) :=
                (sub_le_iff_le_add).1 this
              have h1'' := h1'
              rw [add_comm] at h1''
              exact h1''
            exact (sub_le_iff_le_add).2 h1
          have hfrac : (1 : ℝ) / ((n - 1 : ℕ) : ℝ) ≤ (2 : ℝ) / (n : ℝ) :=
            one_div_cast_sub_le_two_div_cast n hn2
          have hcomp :
              Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ) ≤ Real.log (n : ℝ) - 1 / ((n - 1 : ℕ) : ℝ) := by
            exact sub_le_sub_left hfrac (Real.log (n : ℝ))
          exact le_trans hcomp hlognm1'
        have hy_le' : y ≤ (n : ℝ) + 1 := le_of_lt hy_lt
        have hy1 : 0 ≤ y - (1 / 2 : ℝ) := by
          have hN2_nat : (2 : ℕ) ≤ N := le_max_right (max N1 N2) 2
          have hN2 : (2 : ℝ) ≤ (N : ℝ) := by
            have h : ((2 : ℕ) : ℝ) ≤ (N : ℝ) := (Nat.cast_le (α := ℝ)).2 hN2_nat
            exact h
          have hy3 : (3 : ℝ) ≤ y := by
            have h3' : (2 : ℝ) + 1 ≤ (N : ℝ) + 1 := add_le_add_left hN2 1
            have h3 : (3 : ℝ) ≤ (N : ℝ) + 1 := by
              have h21 : (2 : ℝ) + 1 = 3 := by norm_num
              have h3'' := h3'
              rw [h21] at h3''
              exact h3''
            have hy' : (N : ℝ) + 1 ≤ y := hy
            exact le_trans h3 hy'
          have : (1 / 2 : ℝ) ≤ y := by
            have hhalf : (1 / 2 : ℝ) ≤ 3 := by norm_num
            exact le_trans hhalf hy3
          exact sub_nonneg.2 this
        have ha_nonneg : 0 ≤ y - (n : ℝ) := ha0
        have hlogGamma_lb : Real.log (Real.Gamma y) ≥ Real.log (Real.Gamma (n : ℝ)) +
            (y - (n : ℝ)) * Real.log ((n - 1 : ℕ) : ℝ) := by
          exact h_lower
        have hmain : stirlingMainReal (n : ℝ) + (y - (n : ℝ)) * Real.log ((n - 1 : ℕ) : ℝ) -
            stirlingMainReal (n : ℝ) + (y - (n : ℝ)) * Real.log ((n - 1 : ℕ) : ℝ) -
                stirlingMainReal y ≥
              - (3 / (n : ℝ)) := by
          unfold stirlingMainReal
          have hlogy_mul :
              (y - (1 / 2 : ℝ)) * Real.log y ≤
                (y - (1 / 2 : ℝ)) * (Real.log (n : ℝ) + (y - (n : ℝ)) / (n : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hlogy_ub hy1
          have hlognm1_mul :
              (y - (n : ℝ)) * Real.log ((n - 1 : ℕ) : ℝ) ≥
                (y - (n : ℝ)) * (Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ)) := by
            have h := mul_le_mul_of_nonneg_left hlognm1 ha_nonneg
            exact h
          set a : ℝ := y - (n : ℝ) with ha
          have ha0 : 0 ≤ a := by simpa [a] using ha_nonneg
          have ha1 : a ≤ 1 := by simpa [a] using ha_le
          have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
          have hy_a : y = (n : ℝ) + a := by
            dsimp [a]
            ring
          have hrew0 :
              ( (n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ) + Real.log (2 * π) / 2
                + (y - (n : ℝ)) * Real.log ((n - 1 : ℕ) : ℝ)
                - ((y - 1 / 2) * Real.log y - y + Real.log (2 * π) / 2)) =
                ( (n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ)
                  + a * Real.log ((n - 1 : ℕ) : ℝ)
                  + (-( (y - 1 / 2) * Real.log y)) + y) := by
            ring
          have h1 :
              a * (Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ)) ≤ a * Real.log ((n - 1 : ℕ) : ℝ) := by
            have : a * Real.log ((n - 1 : ℕ) : ℝ) ≥ a * (Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ)) := by
              simpa [a] using hlognm1_mul
            simpa [ge_iff_le] using this
          have h2 :
              -((y - 1 / 2) * (Real.log (n : ℝ) + a / (n : ℝ))) ≤ -((y - 1 / 2) * Real.log y) := by
            have := neg_le_neg hlogy_mul
            simpa [a] using this
          have hmain_lower :
              ( (n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ)
                + a * Real.log ((n - 1 : ℕ) : ℝ)
                + (-( (y - 1 / 2) * Real.log y)) + y)
                ≥
              ( (n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ)
                + a * (Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ))
                + (-( (y - 1 / 2) * (Real.log (n : ℝ) + a / (n : ℝ)))) + y) := by
            linarith [h1, h2]
          have hsimp :
              ( (n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ)
                + a * (Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ))
                + (-( (y - 1 / 2) * (Real.log (n : ℝ) + a / (n : ℝ)))) + y)
                =
              a * (1 / 2 - a) / (n : ℝ) - 2 * a / (n : ℝ) := by
            rw [hy_a]
            field_simp [hn0]
            ring
          have hfinal : a * (1 / 2 - a) / (n : ℝ) - 2 * a / (n : ℝ) ≥ - (3 / (n : ℝ)) := by
            have hnum : a * (1 / 2 - a) - 2 * a ≥ (-3 : ℝ) := by
              nlinarith [ha0, ha1]
            have hdiv : (a * (1 / 2 - a) - 2 * a) / (n : ℝ) ≥ (-3 : ℝ) / (n : ℝ) :=
              div_le_div_of_nonneg_right hnum (le_of_lt hn_pos)
            have hrew :
                a * (1 / 2 - a) / (n : ℝ) - 2 * a / (n : ℝ) =
                  (a * (1 / 2 - a) - 2 * a) / (n : ℝ) := by
              field_simp [hn0]
            calc
              a * (1 / 2 - a) / (n : ℝ) - 2 * a / (n : ℝ)
                  = (a * (1 / 2 - a) - 2 * a) / (n : ℝ) := hrew
              _ ≥ (-3 : ℝ) / (n : ℝ) := hdiv
              _ = - (3 / (n : ℝ)) := by simp [neg_div]
          -- Put it all together.
          calc
            ( (n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ) + Real.log (2 * π) / 2
              + (y - (n : ℝ)) * Real.log ((n - 1 : ℕ) : ℝ)
              - ((y - 1 / 2) * Real.log y - y + Real.log (2 * π) / 2))
                =
                ( (n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ)
                  + a * Real.log ((n - 1 : ℕ) : ℝ)
                  + (-( (y - 1 / 2) * Real.log y)) + y) := hrew0
            _ ≥
                ( (n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ)
                  + a * (Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ))
                  + (-( (y - 1 / 2) * (Real.log (n : ℝ) + a / (n : ℝ)))) + y) := hmain_lower
            _ = a * (1 / 2 - a) / (n : ℝ) - 2 * a / (n : ℝ) := hsimp
            _ ≥ - (3 / (n : ℝ)) := hfinal
        have : Real.log (Real.Gamma y) - stirlingMainReal y ≥
            (Real.log (Real.Gamma (n : ℝ)) - stirlingMainReal (n : ℝ)) - 3 / (n : ℝ) := by
          linarith [hlogGamma_lb, hmain]
        simpa [R] using this
      have hR_abs : |R y| ≤ |R (n : ℝ)| + 3 / (n : ℝ) := by
        have hlower : -(|R (n : ℝ)| + 3 / (n : ℝ)) ≤ R y := by
          have h1 : R (n : ℝ) - 3 / (n : ℝ) ≤ R y := hR_lower
          have h2 : -|R (n : ℝ)| - 3 / (n : ℝ) ≤ R (n : ℝ) - 3 / (n : ℝ) :=
            sub_le_sub_right (neg_abs_le (R (n : ℝ))) (3 / (n : ℝ))
          have h3 : -|R (n : ℝ)| - 3 / (n : ℝ) ≤ R y := le_trans h2 h1
          have hneg : -(|R (n : ℝ)| + 3 / (n : ℝ)) = -|R (n : ℝ)| - 3 / (n : ℝ) := by ring
          simpa [hneg] using h3
        have hupper : R y ≤ |R (n : ℝ)| + 3 / (n : ℝ) := by
          have hn_pos' : 0 < (n : ℝ) := hn_pos
          have hRn : R (n : ℝ) ≤ |R (n : ℝ)| := le_abs_self _
          have hdiv : (1 : ℝ) / (n : ℝ) ≤ (3 : ℝ) / (n : ℝ) :=
            div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 3) (le_of_lt hn_pos')
          have hstep : R (n : ℝ) + (1 : ℝ) / (n : ℝ) ≤ |R (n : ℝ)| + (3 : ℝ) / (n : ℝ) := by
            exact add_le_add hRn hdiv
          exact le_trans hR_upper hstep
        exact abs_le.2 ⟨hlower, hupper⟩
      have hRn_small : |R (n : ℝ)| < ε / 2 := by
        have hN1_le_N : N1 ≤ N := by
          exact le_trans (le_max_left N1 N2) (le_max_left (max N1 N2) 2)
        have hn_ge1 : N1 ≤ n := le_trans hN1_le_N hn_ge
        have hdist : dist (R (n : ℝ)) 0 < ε / 2 := hN1 n hn_ge1
        simpa [Real.dist_eq] using hdist
      have h3n_small : 3 / (n : ℝ) < ε / 2 := by
        have hN2_le_N : N2 ≤ N := by
          exact le_trans (le_max_right N1 N2) (le_max_left (max N1 N2) 2)
        have hn_ge2 : N2 ≤ n := le_trans hN2_le_N hn_ge
        have hdist : dist ((3 : ℝ) / (n : ℝ)) 0 < ε / 2 := hN2 n hn_ge2
        simpa [Real.dist_eq] using hdist
      have : |R y| < ε := by
        have hsum : |R (n : ℝ)| + 3 / (n : ℝ) < ε := by
          have : |R (n : ℝ)| + 3 / (n : ℝ) < ε / 2 + ε / 2 := add_lt_add hRn_small h3n_small
          simpa [add_halves] using this
        exact lt_of_le_of_lt hR_abs hsum
      simpa [Real.dist_eq, abs_sub_comm] using this
    have hJlim : Tendsto (fun y : ℝ => (Binet.J (y : ℂ)).re) atTop (𝓝 0) :=
      tendsto_re_J_atTop
    have hlim : Tendsto h atTop (𝓝 0) := by
      simpa [h, sub_eq_add_neg] using hRlim.add (hJlim.neg)
    have hxseq : Tendsto (fun n : ℕ => h (x + n)) atTop (𝓝 0) := by
      have hxadd : Tendsto (fun n : ℕ => (x + n : ℝ)) atTop atTop := by
        have hnx : Tendsto (fun n : ℕ => ((n : ℝ) + x)) atTop atTop :=
          Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds
        simpa [add_assoc, add_comm, add_left_comm] using hnx
      exact hlim.comp hxadd
    have hx0' : h x = 0 :=
      eq_of_tendsto_atTop_of_add_one (h := h) (x := x) (l := 0) hx h_periodic hlim
    dsimp [h] at hx0'
    linarith
  have hmain : Real.log (Real.Gamma x) = stirlingMainReal x + (Binet.J (x : ℂ)).re := by
    have hR' : R x + stirlingMainReal x = (Binet.J (x : ℂ)).re + stirlingMainReal x :=
      congrArg (fun r : ℝ => r + stirlingMainReal x) hR
    have hlog : Real.log (Real.Gamma x) = (Binet.J (x : ℂ)).re + stirlingMainReal x := by
      have hR'' := hR'
      dsimp [R] at hR''
      rw [sub_add_cancel] at hR''
      exact hR''
    have hlog' := hlog
    rw [add_comm] at hlog'
    exact hlog'
  have hmain' := hmain
  dsimp [stirlingMainReal] at hmain'
  exact hmain'

lemma R_eq_re_J {x : ℝ} (hx : 0 < x) : R x = (Binet.J (x : ℂ)).re := by
  have h := log_Gamma_real_eq (x := x) hx
  unfold R stirlingMainReal
  linarith [h]

/-! ## Section 3: Stirling series with Bernoulli numbers -/

/-- The Bernoulli number B_n as a real number. -/
def bernoulliReal (n : ℕ) : ℝ :=
  (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli n)).eval 0

/-- The k-th term of the Stirling series: B_{2k} / (2k(2k-1) z^{2k-1}) -/
def stirlingTerm (k : ℕ) (z : ℂ) : ℂ :=
  if k = 0 then 0 else
    (bernoulliReal (2 * k) : ℂ) / (2 * k * (2 * k - 1) * z ^ (2 * k - 1))

/-- The truncated Stirling series up to order n. -/
def stirlingSeries (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range n, stirlingTerm k z

/-- The remainder after n terms of the Stirling series. -/
def stirlingRemainder (n : ℕ) (z : ℂ) : ℂ :=
  J z - stirlingSeries n z

/-- The Binet integral equals the Stirling series plus remainder. -/
theorem J_eq_stirlingSeries_add_remainder (z : ℂ) (n : ℕ) :
    J z = stirlingSeries n z + stirlingRemainder n z := by
  simp only [stirlingRemainder, add_sub_cancel]

/-- Simplified bound for n = 0: |R₀(z)| ≤ 1/(12·Re(z)).
This follows from J_norm_le_re since R₀(z) = J(z). -/
theorem stirlingRemainder_zero_bound {z : ℂ} (hz : 0 < z.re) :
    ‖stirlingRemainder 0 z‖ ≤ 1 / (12 * z.re) := by
  simp only [stirlingRemainder, stirlingSeries, Finset.range_zero, Finset.sum_empty]
  simp only [sub_zero]
  exact J_norm_le_re hz

/-- For real positive x: |R₀(x)| ≤ 1/(12x). -/
theorem stirlingRemainder_zero_bound_real {x : ℝ} (hx : 0 < x) :
    ‖stirlingRemainder 0 (x : ℂ)‖ ≤ 1 / (12 * x) := by
  simp only [stirlingRemainder, stirlingSeries, Finset.range_zero, Finset.sum_empty]
  simp only [sub_zero]
  exact J_norm_le_real hx

/-! ## Section 4: Gamma function bounds -/

/-- For x ∈ [1, 2], Γ(x) ≤ 1 since Γ(1) = Γ(2) = 1 and the function is convex. -/
theorem Gamma_le_one_of_mem_Icc {x : ℝ} (hlo : 1 ≤ x) (hhi : x ≤ 2) :
    Real.Gamma x ≤ 1 := by
  have h_convex := Real.convexOn_Gamma
  have h1 : Real.Gamma 1 = 1 := Real.Gamma_one
  have h2 : Real.Gamma 2 = 1 := Real.Gamma_two
  let t := 2 - x
  have ht_nonneg : 0 ≤ t := by linarith
  have ht_le_one : t ≤ 1 := by linarith
  have hx_conv : x = t * 1 + (1 - t) * 2 := by field_simp [t]; ring
  have := h_convex.2 (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 2)
    ht_nonneg (by linarith : 0 ≤ 1 - t) (by ring : t + (1 - t) = 1)
  rw [smul_eq_mul, smul_eq_mul] at this
  calc Real.Gamma x
      = Real.Gamma (t * 1 + (1 - t) * 2) := by rw [hx_conv]
    _ ≤ t * Real.Gamma 1 + (1 - t) * Real.Gamma 2 := this
    _ = t * 1 + (1 - t) * 1 := by rw [h1, h2]
    _ = 1 := by ring

/-- The integral representation gives |Γ(z)| ≤ Γ(Re(z)) for Re(z) > 0.
Key: |t^{z-1}| = t^{Re(z)-1} for t > 0. -/
theorem norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  have h_norm_eq : ∀ t ∈ Set.Ioi (0 : ℝ),
      ‖((-t).exp : ℂ) * (t : ℂ) ^ (z - 1)‖ = Real.exp (-t) * t ^ (z.re - 1) := by
    intro t ht
    have hcpow : ‖(t : ℂ) ^ (z - 1)‖ = t ^ (z.re - 1) := by
      simpa using Complex.norm_cpow_eq_rpow_re_of_pos ht (z - 1)
    simp [Complex.norm_exp, hcpow]
  calc ‖Complex.GammaIntegral z‖
      ≤ ∫ t in Set.Ioi (0 : ℝ), ‖((-t).exp : ℂ) * (t : ℂ) ^ (z - 1)‖ := by
        unfold Complex.GammaIntegral
        exact MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (z.re - 1) := by
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_norm_eq

/-- Combined bound: For Re(z) ∈ [1, 2], |Γ(z)| ≤ 1. -/
theorem norm_Gamma_le_one {z : ℂ} (hlo : 1 ≤ z.re) (hhi : z.re ≤ 2) :
    ‖Complex.Gamma z‖ ≤ 1 := by
  have hz_pos : 0 < z.re := by linarith
  calc ‖Complex.Gamma z‖
      ≤ Real.Gamma z.re := norm_Gamma_le_Gamma_re hz_pos
    _ ≤ 1 := Gamma_le_one_of_mem_Icc hlo hhi

end Binet

/-! ## Section 6: Connection to Stirling.GammaAux -/

namespace Stirling.GammaAux

/-- The Gamma bound on [1, 2], proved via convexity. -/
theorem Gamma_bound_one_two' {s : ℂ} (hs_lo : 1 ≤ s.re) (hs_hi : s.re ≤ 2) :
    ‖Complex.Gamma s‖ ≤ 1 :=
  Binet.norm_Gamma_le_one hs_lo hs_hi

end Stirling.GammaAux

/-!
## Compatibility / centralized API (`BinetFormula.*`)

Some downstream files historically refer to results in this file via the namespace `BinetFormula`.
The core development lives in `namespace Binet`; we provide thin wrappers here to keep the
namespace stable while we progressively centralize the Gamma/Stirling API.
-/

namespace Binet

open Real Complex Set MeasureTheory Filter Topology BinetKernel
open scoped BigOperators

/-- Real-part version of the Binet integral: for `x > 0`,
`re (J x) = ∫₀^∞ K̃(t) * exp(-t*x) dt`. -/
theorem re_J_eq_integral_Ktilde {x : ℝ} (hx : 0 < x) :
    (Binet.J (x : ℂ)).re = ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) := by
  simpa using (Binet.re_J_eq_integral_Ktilde (x := x) hx)

/-- Integrability of the real Binet integrand `K̃(t) * exp(-t*x)` on `(0,∞)` for `x > 0`. -/
theorem integrable_Ktilde_mul_exp_neg_mul {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => BinetKernel.Ktilde t * Real.exp (-t * x)) (Set.Ioi 0) := by
  simpa using (Binet.BinetKernel.integrable_Ktilde_exp (x := x) hx)

/-- **Positivity of the Binet integral (real part).**

For `x > 0`, the Binet correction term satisfies `(Binet.J x).re > 0`. -/
theorem re_J_pos {x : ℝ} (hx : 0 < x) : 0 < (Binet.J (x : ℂ)).re := by
  have hJ : (Binet.J (x : ℂ)).re =
      ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) :=
    re_J_eq_integral_Ktilde (x := x) hx
  let f : ℝ → ℝ := fun t => BinetKernel.Ktilde t * Real.exp (-t * x)
  have hf_int : IntegrableOn f (Set.Ioi (0 : ℝ)) volume := by
    simpa [f] using (integrable_Ktilde_mul_exp_neg_mul (x := x) hx)
  have hf_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] f := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hK0 : 0 ≤ BinetKernel.Ktilde t := BinetKernel.Ktilde_nonneg (le_of_lt ht)
    exact mul_nonneg hK0 (Real.exp_nonneg _)
  have hμ_support : (0 : ENNReal) < volume (Function.support f ∩ Set.Ioi (0 : ℝ)) := by
    have hsub : Set.Ioc (0 : ℝ) 1 ⊆ Function.support f ∩ Set.Ioi (0 : ℝ) := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have hKpos : 0 < BinetKernel.Ktilde t := by
        have hconst : 0 < (1 / 12 : ℝ) * Real.exp (-t / 12) := by
          have : (0 : ℝ) < (1 / 12 : ℝ) := by norm_num
          exact mul_pos this (Real.exp_pos _)
        exact
          lt_of_lt_of_le hconst
            (BinetKernel.Ktilde_ge_one_div_twelve_mul_exp_neg_div_twelve ht0)
      have hf_ne : f t ≠ 0 := ne_of_gt (mul_pos hKpos (Real.exp_pos _))
      have ht_support : t ∈ Function.support f := by
        simpa [Function.mem_support] using hf_ne
      exact ⟨ht_support, ht.1⟩
    have hvol_pos : (0 : ENNReal) < volume (Set.Ioc (0 : ℝ) 1) := by simp
    exact lt_of_lt_of_le hvol_pos (measure_mono hsub)
  have hf_pos : 0 < ∫ t in Set.Ioi (0 : ℝ), f t ∂volume := by
    refine
      (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
        (μ := volume) (s := Set.Ioi (0 : ℝ)) hf_nonneg hf_int).2 hμ_support
  simpa [hJ, f] using hf_pos

/-- **Upper bound for the Binet integral (real part).**

For `x > 0`, we have `(Binet.J x).re ≤ 1/(12x)`. -/
theorem re_J_le_one_div_twelve {x : ℝ} (hx : 0 < x) :
    (Binet.J (x : ℂ)).re ≤ 1 / (12 * x) := by
  have h₁ : (Binet.J (x : ℂ)).re ≤ |(Binet.J (x : ℂ)).re| := le_abs_self _
  have h₂ : |(Binet.J (x : ℂ)).re| ≤ 1 / (12 * x) :=
    (Complex.abs_re_le_norm (Binet.J (x : ℂ))).trans (Binet.J_norm_le_real (x := x) hx)
  exact h₁.trans h₂

/-- Compatibility alias: historical name for the strict upper bound on `re (J x)`. -/
theorem re_J_lt_one_div_twelve {x : ℝ} (hx : 0 < x) :
    (Binet.J (x : ℂ)).re < 1 / (12 * x) := by
  have hJ : (Binet.J (x : ℂ)).re =
      ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) :=
    re_J_eq_integral_Ktilde (x := x) hx
  let f : ℝ → ℝ := fun t => BinetKernel.Ktilde t * Real.exp (-t * x)
  let g : ℝ → ℝ := fun t => (1 / 12 : ℝ) * Real.exp (-t * x)
  let h : ℝ → ℝ := fun t => g t - f t
  have hf_int : IntegrableOn f (Set.Ioi (0 : ℝ)) volume := by
    simpa [f] using (integrable_Ktilde_mul_exp_neg_mul (x := x) hx)
  have hg_int : IntegrableOn g (Set.Ioi (0 : ℝ)) volume := by
    simpa [g] using (Binet.integrable_const_mul_exp (x := x) hx)
  have hh_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] h := by
    have : ∀ᵐ t ∂volume, t ∈ Set.Ioi (0 : ℝ) → 0 ≤ h t := by
      refine MeasureTheory.ae_of_all _ ?_
      intro t ht
      have hK : BinetKernel.Ktilde t ≤ (1 / 12 : ℝ) := BinetKernel.Ktilde_le (le_of_lt ht)
      have hE : 0 ≤ Real.exp (-t * x) := Real.exp_nonneg _
      dsimp [h, f, g]
      refine sub_nonneg.2 ?_
      exact mul_le_mul_of_nonneg_right hK hE
    exact
      (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi).2 this
  have hh_int : IntegrableOn h (Set.Ioi (0 : ℝ)) volume := by
    simpa [h] using (hg_int.sub hf_int)
  have hμ_support : (0 : ENNReal) < volume (Function.support h ∩ Set.Ioi (0 : ℝ)) := by
    have hsub : Set.Ioc (0 : ℝ) 1 ⊆ Function.support h ∩ Set.Ioi (0 : ℝ) := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have htI : t ∈ Set.Ioi (0 : ℝ) := ht0
      have hK : BinetKernel.Ktilde t < (1 / 12 : ℝ) := BinetKernel.Ktilde_lt ht0
      have hE : 0 < Real.exp (-t * x) := Real.exp_pos _
      have : h t ≠ 0 := by
        have : 0 < h t := by
          dsimp [h, f, g]
          have hlt :
              BinetKernel.Ktilde t * Real.exp (-t * x) < (1 / 12 : ℝ) * Real.exp (-t * x) := by
            exact mul_lt_mul_of_pos_right hK hE
          exact sub_pos.2 hlt
        exact ne_of_gt this
      have ht_support : t ∈ Function.support h := by
        simp [Function.mem_support, this]
      exact ⟨ht_support, htI⟩
    have hvol_pos : (0 : ENNReal) < volume (Set.Ioc (0 : ℝ) 1) := by simp
    exact lt_of_lt_of_le hvol_pos (measure_mono hsub)
  have hh_pos : 0 < ∫ t in Set.Ioi (0 : ℝ), h t := by
    have := (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae (μ := volume)
      (s := Set.Ioi (0 : ℝ)) (f := h) hh_nonneg hh_int).2 hμ_support
    simpa using this
  have hsub_eq :
      (∫ t in Set.Ioi (0 : ℝ), h t) =
        (∫ t in Set.Ioi (0 : ℝ), g t) - (∫ t in Set.Ioi (0 : ℝ), f t) := by
    simpa [h, sub_eq_add_neg] using
      (MeasureTheory.integral_sub (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (hf := hg_int) (hg := hf_int))
  have hlt_fg : (∫ t in Set.Ioi (0 : ℝ), f t) < (∫ t in Set.Ioi (0 : ℝ), g t) := by
    have : 0 < (∫ t in Set.Ioi (0 : ℝ), g t) - (∫ t in Set.Ioi (0 : ℝ), f t) := by
      simpa [hsub_eq] using hh_pos
    exact (sub_pos.mp this)
  have hg_val : (∫ t in Set.Ioi (0 : ℝ), g t) = 1 / (12 * x) := by
    have hbase : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * x)) = 1 / x := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using (Binet.integral_exp_neg_mul_Ioi (x := x) hx)
    calc
      (∫ t in Set.Ioi (0 : ℝ), g t)
          = (1 / 12 : ℝ) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * x)) := by
              simp [g, MeasureTheory.integral_const_mul, mul_comm]
      _ = (1 / 12 : ℝ) * (1 / x) := by simp [hbase]
      _ = 1 / (12 * x) := by ring
  have : (Binet.J (x : ℂ)).re < 1 / (12 * x) := by
    have : (∫ t in Set.Ioi (0 : ℝ), f t) < 1 / (12 * x) := by
      have : (∫ t in Set.Ioi (0 : ℝ), f t) < (∫ t in Set.Ioi (0 : ℝ), g t) := hlt_fg
      exact lt_of_lt_of_eq this hg_val
    simpa [hJ, f] using this
  exact this

/-- Compatibility: real Binet formula for `log Γ(x)` on `x > 0`. -/
theorem Real_log_Gamma_eq_Binet {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + Real.log (2 * Real.pi) / 2 + (Binet.J x).re := by
  simpa using (Binet.log_Gamma_real_eq (x := x) hx)

end Binet
