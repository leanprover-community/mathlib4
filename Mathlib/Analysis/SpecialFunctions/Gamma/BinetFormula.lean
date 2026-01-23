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

lemma log_Gamma_real_eq_of_R_eq_re_J {x : ℝ} (hR : R x = (Binet.J (x : ℂ)).re) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + Real.log (2 * Real.pi) / 2 + (J x).re := by
  have hR' := hR
  dsimp [R] at hR'
  have hmain : Real.log (Real.Gamma x) = stirlingMainReal x + (Binet.J (x : ℂ)).re := by
    linarith
  -- rewrite `stirlingMainReal`, and rewrite `(Binet.J (x : ℂ)).re` as `(J x).re`
  simpa [stirlingMainReal] using hmain

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



end Binet
