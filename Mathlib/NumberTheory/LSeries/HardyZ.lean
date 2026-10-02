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

### Main results

* `hardyZ`: the definition, as a function `ℝ → ℝ`.
* `abs_hardyZ`: `|Z t| = ‖ζ (1/2 + i t)‖`.
* `hardyZ_neg`: `Z` is even.
* `hardyZ_eq_zero_iff`: `Z t = 0 ↔ ζ (1/2 + i t) = 0`, the reason the definition exists.
* `continuous_hardyZ`: `Z` is continuous, so the intermediate value theorem applies to it and
  sign changes of `Z` locate zeros of `ζ` on the critical line.

### TODO

* Add the relation to the Riemann–Siegel theta function, see
  <https://en.wikipedia.org/wiki/Riemann%E2%80%93Siegel_theta_function>.

### References

* [E. C. Titchmarsh, *The theory of the Riemann zeta-function*, §4.17][Titchmarsh1986]
-/

@[expose] public section

open Complex Real Filter Topology
open scoped ComplexConjugate

private lemma half_add_mul_I_re (t : ℝ) : ((1 : ℂ) / 2 + t * I).re = 1 / 2 := by simp

private lemma half_add_mul_I_ne_zero (t : ℝ) : (1 : ℂ) / 2 + t * I ≠ 0 := by
  intro h
  have hre : ((1 : ℂ) / 2 + t * I).re = 0 := by rw [h]; simp
  rw [half_add_mul_I_re] at hre
  norm_num at hre

/-- The completed zeta function is real on the critical line. -/
theorem conj_completedRiemannZeta_half_add_mul_I (t : ℝ) :
    conj (completedRiemannZeta (1 / 2 + t * I)) = completedRiemannZeta (1 / 2 + t * I) :=
  calc
    _ = completedRiemannZeta (conj (1 / 2 + t * I)) := by rw [completedRiemannZeta_conj]
    _ = completedRiemannZeta (1 - (1 / 2 + t * I)) := by simp [conj_ofNat]; ring_nf
    _ = _ := by rw [completedRiemannZeta_one_sub]

theorem completedRiemannZeta_half_add_mul_I_im (t : ℝ) :
    (completedRiemannZeta (1 / 2 + t * I)).im = 0 :=
  conj_eq_iff_im.mp (conj_completedRiemannZeta_half_add_mul_I t)

private theorem ofReal_completedRiemannZeta_half_add_mul_I_re (t : ℝ) :
    ((completedRiemannZeta (1 / 2 + t * I)).re : ℂ) = completedRiemannZeta (1 / 2 + t * I) :=
  conj_eq_iff_re.mp (conj_completedRiemannZeta_half_add_mul_I t)

private theorem Gammaℝ_half_add_mul_I_ne_zero (t : ℝ) : Gammaℝ (1 / 2 + t * I) ≠ 0 :=
  Gammaℝ_ne_zero_of_re_pos (by simp)

/-- **Hardy's Z function**: the real-valued function on `ℝ` obtained by dividing `Λ` on the
critical line by the modulus of its archimedean factor. Its zeros are exactly the heights of
the zeros of `ζ` on the critical line. -/
noncomputable def hardyZ (t : ℝ) : ℝ :=
  (completedRiemannZeta (1 / 2 + t * I)).re / ‖Gammaℝ (1 / 2 + t * I)‖

theorem ofReal_hardyZ (t : ℝ) :
    (hardyZ t : ℂ) =
      completedRiemannZeta (1 / 2 + t * I) / (‖Gammaℝ (1 / 2 + t * I)‖ : ℝ) := by
  rw [hardyZ, ofReal_div, ofReal_completedRiemannZeta_half_add_mul_I_re]

/-- `Z` has the same modulus as `ζ` on the critical line. -/
theorem abs_hardyZ (t : ℝ) : |hardyZ t| = ‖riemannZeta (1 / 2 + t * I)‖ := by
  have hg := Gammaℝ_half_add_mul_I_ne_zero t
  have hL : completedRiemannZeta (1 / 2 + t * I) =
      riemannZeta (1 / 2 + t * I) * Gammaℝ (1 / 2 + t * I) := by
    grind [riemannZeta_def_of_ne_zero (half_add_mul_I_ne_zero t)]
  have h1 : |(completedRiemannZeta (1 / 2 + t * I)).re| =
      ‖completedRiemannZeta (1 / 2 + t * I)‖ := by
    rw [norm_def, normSq_apply, completedRiemannZeta_half_add_mul_I_im]
    simp [Real.sqrt_mul_self_eq_abs]
  rw [hardyZ, abs_div, h1, hL, norm_mul, abs_norm, mul_div_assoc,
    div_self (norm_ne_zero_iff.mpr hg), mul_one]

/-- `Z` is an even function. -/
theorem hardyZ_neg (t : ℝ) : hardyZ (-t) = hardyZ t := by
  have hnum : completedRiemannZeta (1 / 2 + (-t : ℝ) * I) =
      completedRiemannZeta (1 / 2 + t * I) := by
    have h : ((1 : ℂ) / 2 + (-t : ℝ) * I) = 1 - (1 / 2 + t * I) := by
      simp [ext_iff]; norm_num
    rw [h, completedRiemannZeta_one_sub]
  have hden : ‖Gammaℝ (1 / 2 + (-t : ℝ) * I)‖ = ‖Gammaℝ (1 / 2 + t * I)‖ := by
    have h : ((1 : ℂ) / 2 + (-t : ℝ) * I) = conj (1 / 2 + t * I) := by
      simp [ext_iff]
    rw [h, Gammaℝ_conj, norm_conj]
  rw [hardyZ, hardyZ, hnum, hden]

/-- The zeros of `Z` on `ℝ` are exactly the heights of the zeros of `ζ` on the critical line. -/
theorem hardyZ_eq_zero_iff (t : ℝ) :
    hardyZ t = 0 ↔ riemannZeta (1 / 2 + t * I) = 0 := by
  rw [← abs_eq_zero (a := hardyZ t), abs_hardyZ, norm_eq_zero]

private lemma half_add_mul_I_ne_one (t : ℝ) : (1 : ℂ) / 2 + t * I ≠ 1 := by
  intro h
  have hre : ((1 : ℂ) / 2 + t * I).re = 1 := by rw [h]; simp
  rw [half_add_mul_I_re] at hre
  norm_num at hre

/-- Hardy's `Z`-function is continuous. -/
theorem continuous_hardyZ : Continuous hardyZ := by
  have hnum : Continuous fun t : ℝ ↦ (completedRiemannZeta (1 / 2 + t * I)).re :=
    Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun t ↦
      ContinuousAt.comp (g := completedRiemannZeta) (f := fun t : ℝ ↦ (1 : ℂ) / 2 + t * I)
        (x := t) (differentiableAt_completedZeta (half_add_mul_I_ne_zero t)
          (half_add_mul_I_ne_one t)).continuousAt (by fun_prop))
  have hden : Continuous fun t : ℝ ↦ ‖Gammaℝ (1 / 2 + t * I)‖ := by
    refine continuous_norm.comp (continuous_iff_continuousAt.mpr fun t ↦ ?_)
    have hne : ∀ m : ℕ, ((1 : ℂ) / 2 + t * I) / 2 ≠ -m := by
      intro m hm
      have hre : (((1 : ℂ) / 2 + t * I) / 2).re = (-(m : ℂ)).re := by rw [hm]
      rw [Complex.div_ofNat_re, half_add_mul_I_re] at hre
      grind [Complex.neg_re, Complex.natCast_re]
    have hG : ContinuousAt Gammaℝ (1 / 2 + t * I) := by
      rw [funext Gammaℝ_def]
      apply ((continuousAt_const_cpow (by simp)).comp (by fun_prop)).mul
      exact .comp (continuousAt_Gamma _ hne) (by fun_prop)
    exact hG.comp (f := fun t : ℝ ↦ _ + t * I) (by fun_prop)
  exact hnum.div hden fun t ↦ norm_ne_zero_iff.mpr (Gammaℝ_half_add_mul_I_ne_zero t)
