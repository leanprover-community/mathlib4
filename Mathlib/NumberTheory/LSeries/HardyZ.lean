/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Lince
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Hardy's Z function

Hardy's `Z` function is the real-valued function on `ℝ` whose zeros are exactly the heights of
the zeros of `ζ` on the critical line. It is defined here by dividing the completed zeta
function `Λ` on the critical line by the modulus of its archimedean factor:

$$ Z(t) = \frac{\Lambda(1/2 + it)}{|\Gamma_{\mathbb{R}}(1/2 + it)|}. $$

The numerator is real, by `completedRiemannZeta_conj` together with the functional equation
`completedRiemannZeta_one_sub`, and the denominator is a positive real, so `Z` is real-valued.

This definition avoids the Riemann–Siegel theta function `ϑ`. The textbook definition
`Z t = exp (I * ϑ t) * ζ (1/2 + I * t)` requires a continuous branch of `log Γ` along the
critical line, which Mathlib does not currently have.

The two agree. Writing `Γ_ℝ(1/2 + it) = π ^ (-1/4) * π ^ (-it/2) * Γ(1/4 + it/2)`, the factor
`π ^ (-1/4)` is a positive real and `|π ^ (-it/2)| = 1`, so dividing `Λ` by `|Γ_ℝ|` leaves

$$ Z(t) = \pi^{-it/2} \frac{\Gamma(1/4 + it/2)}{|\Gamma(1/4 + it/2)|} \zeta(1/2 + it)
        = e^{i \vartheta(t)} \zeta(1/2 + it), $$

with `ϑ(t) = arg Γ(1/4 + it/2) - (t/2) * log π`, which is exactly the Riemann–Siegel theta
function. Dividing by a modulus and multiplying by `exp (I * ϑ)` are the same normalisation;
the first simply does not name a branch. Once `ϑ` is available this can be recorded as a lemma.

### Main results

* `hardyZ`: the definition, as a function `ℝ → ℝ`.
* `abs_hardyZ`: `|Z t| = ‖ζ (1/2 + i t)‖`.
* `hardyZ_neg`: `Z` is even.
* `hardyZ_eq_zero_iff`: `Z t = 0 ↔ ζ (1/2 + i t) = 0`, the reason the definition exists.
* `continuous_hardyZ`: `Z` is continuous, so the intermediate value theorem applies to it and
  sign changes of `Z` locate zeros of `ζ` on the critical line.

### References

* E. C. Titchmarsh, *The theory of the Riemann zeta-function*, 2nd ed., Oxford, 1986, §4.17
-/

@[expose] public section

open Complex Real Filter Topology
open scoped ComplexConjugate

private lemma half_add_mul_I_re (t : ℝ) : ((1 : ℂ) / 2 + t * I).re = 1 / 2 := by simp

private lemma conj_half_add_mul_I (t : ℝ) :
    conj ((1 : ℂ) / 2 + t * I) = 1 - (1 / 2 + t * I) := by
  simp [Complex.ext_iff]; norm_num

private lemma half_add_mul_I_ne_zero (t : ℝ) : (1 : ℂ) / 2 + t * I ≠ 0 := by
  intro h
  have hre : ((1 : ℂ) / 2 + t * I).re = 0 := by rw [h]; simp
  rw [half_add_mul_I_re] at hre
  norm_num at hre

private lemma half_add_mul_I_ne_one (t : ℝ) : (1 : ℂ) / 2 + t * I ≠ 1 := by
  intro h
  have hre : ((1 : ℂ) / 2 + t * I).re = 1 := by rw [h]; simp
  rw [half_add_mul_I_re] at hre
  norm_num at hre

private lemma continuous_half_add_mul_I : Continuous fun t : ℝ ↦ (1 : ℂ) / 2 + t * I :=
  continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

/-- The completed zeta function is real on the critical line. -/
theorem conj_completedRiemannZeta_half_add_mul_I (t : ℝ) :
    conj (completedRiemannZeta (1 / 2 + t * I)) = completedRiemannZeta (1 / 2 + t * I) := by
  rw [← completedRiemannZeta_conj, conj_half_add_mul_I, completedRiemannZeta_one_sub]

theorem completedRiemannZeta_half_add_mul_I_im (t : ℝ) :
    (completedRiemannZeta (1 / 2 + t * I)).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_completedRiemannZeta_half_add_mul_I t)

private theorem ofReal_completedRiemannZeta_half_add_mul_I_re (t : ℝ) :
    ((completedRiemannZeta (1 / 2 + t * I)).re : ℂ) = completedRiemannZeta (1 / 2 + t * I) :=
  Complex.conj_eq_iff_re.mp (conj_completedRiemannZeta_half_add_mul_I t)

private theorem Gammaℝ_half_add_mul_I_ne_zero (t : ℝ) : Gammaℝ (1 / 2 + t * I) ≠ 0 :=
  Gammaℝ_ne_zero_of_re_pos (by rw [half_add_mul_I_re]; norm_num)

/-- **Hardy's Z function**: the real-valued function on `ℝ` obtained by dividing `Λ` on the
critical line by the modulus of its archimedean factor. Its zeros are exactly the heights of
the zeros of `ζ` on the critical line. -/
noncomputable def hardyZ (t : ℝ) : ℝ :=
  (completedRiemannZeta (1 / 2 + t * I)).re / ‖Gammaℝ (1 / 2 + t * I)‖

theorem ofReal_hardyZ (t : ℝ) :
    (hardyZ t : ℂ) =
      completedRiemannZeta (1 / 2 + t * I) / (‖Gammaℝ (1 / 2 + t * I)‖ : ℝ) := by
  rw [hardyZ, Complex.ofReal_div, ofReal_completedRiemannZeta_half_add_mul_I_re]

/-- `Z` has the same modulus as `ζ` on the critical line. -/
theorem abs_hardyZ (t : ℝ) : |hardyZ t| = ‖riemannZeta (1 / 2 + t * I)‖ := by
  have hg := Gammaℝ_half_add_mul_I_ne_zero t
  have hL : completedRiemannZeta (1 / 2 + t * I) =
      riemannZeta (1 / 2 + t * I) * Gammaℝ (1 / 2 + t * I) := by
    rw [riemannZeta_def_of_ne_zero (half_add_mul_I_ne_zero t)]
    exact (div_mul_cancel₀ _ hg).symm
  have h1 : |(completedRiemannZeta (1 / 2 + t * I)).re| =
      ‖completedRiemannZeta (1 / 2 + t * I)‖ := by
    rw [Complex.norm_def, Complex.normSq_apply, completedRiemannZeta_half_add_mul_I_im]
    simp [Real.sqrt_mul_self_eq_abs]
  rw [hardyZ, abs_div, h1, hL, norm_mul, abs_norm, mul_div_assoc,
    div_self (norm_ne_zero_iff.mpr hg), mul_one]

/-- `Z` is an even function. -/
theorem hardyZ_neg (t : ℝ) : hardyZ (-t) = hardyZ t := by
  have hnum : completedRiemannZeta (1 / 2 + (-t : ℝ) * I) =
      completedRiemannZeta (1 / 2 + t * I) := by
    have h : ((1 : ℂ) / 2 + (-t : ℝ) * I) = 1 - (1 / 2 + t * I) := by
      simp [Complex.ext_iff]; norm_num
    rw [h, completedRiemannZeta_one_sub]
  have hden : ‖Gammaℝ (1 / 2 + (-t : ℝ) * I)‖ = ‖Gammaℝ (1 / 2 + t * I)‖ := by
    have h : ((1 : ℂ) / 2 + (-t : ℝ) * I) = conj (1 / 2 + t * I) := by
      simp [Complex.ext_iff]
    rw [h, Complex.Gammaℝ_conj, Complex.norm_conj]
  rw [hardyZ, hardyZ, hnum, hden]

/-- The zeros of `Z` on `ℝ` are exactly the heights of the zeros of `ζ` on the critical line. -/
theorem hardyZ_eq_zero_iff (t : ℝ) :
    hardyZ t = 0 ↔ riemannZeta (1 / 2 + t * I) = 0 := by
  rw [← abs_eq_zero (a := hardyZ t), abs_hardyZ, norm_eq_zero]

/-- `Z` is continuous, so the intermediate value theorem applies to it. -/
theorem continuous_hardyZ : Continuous hardyZ := by
  have hnum : Continuous fun t : ℝ ↦ (completedRiemannZeta (1 / 2 + t * I)).re :=
    Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun t ↦
      ContinuousAt.comp (g := completedRiemannZeta) (f := fun t : ℝ ↦ (1 : ℂ) / 2 + t * I)
        (x := t) (differentiableAt_completedZeta (half_add_mul_I_ne_zero t)
          (half_add_mul_I_ne_one t)).continuousAt continuous_half_add_mul_I.continuousAt)
  have hden : Continuous fun t : ℝ ↦ ‖Gammaℝ (1 / 2 + t * I)‖ := by
    refine continuous_norm.comp (continuous_iff_continuousAt.mpr fun t ↦ ?_)
    have hne : ∀ m : ℕ, ((1 : ℂ) / 2 + t * I) / 2 ≠ -m := by
      intro m hm
      have hre : (((1 : ℂ) / 2 + t * I) / 2).re = (-(m : ℂ)).re := by rw [hm]
      rw [Complex.div_ofNat_re, half_add_mul_I_re] at hre
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hG : ContinuousAt Gammaℝ (1 / 2 + t * I) := by
      rw [continuousAt_congr (Filter.Eventually.of_forall Gammaℝ_def)]
      refine ContinuousAt.mul ?_ ?_
      · exact (continuousAt_const_cpow (by exact_mod_cast Real.pi_ne_zero)).comp
          (continuousAt_id.neg.div_const 2)
      · have h2 : ContinuousAt (fun z : ℂ ↦ z / 2) (1 / 2 + t * I) :=
          continuousAt_id.div_const 2
        exact ContinuousAt.comp (g := Complex.Gamma) (f := fun z : ℂ ↦ z / 2)
          (x := 1 / 2 + t * I) (Complex.continuousAt_Gamma _ hne) h2
    exact ContinuousAt.comp (g := Gammaℝ) (f := fun t : ℝ ↦ (1 : ℂ) / 2 + t * I) (x := t) hG
      continuous_half_add_mul_I.continuousAt
  exact hnum.div hden fun t ↦ norm_ne_zero_iff.mpr (Gammaℝ_half_add_mul_I_ne_zero t)
