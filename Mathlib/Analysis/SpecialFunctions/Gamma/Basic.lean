/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.MellinTransform

#align_import analysis.special_functions.gamma.basic from "leanprover-community/mathlib"@"cca40788df1b8755d5baf17ab2f27dacc2e17acb"

/-!
# The Gamma function

This file defines the `Γ` function (of a real or complex variable `s`). We define this by Euler's
integral `Γ(s) = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1)` in the range where this integral converges
(i.e., for `0 < s` in the real case, and `0 < re s` in the complex case).

We show that this integral satisfies `Γ(1) = 1` and `Γ(s + 1) = s * Γ(s)`; hence we can define
`Γ(s)` for all `s` as the unique function satisfying this recurrence and agreeing with Euler's
integral in the convergence range. (If `s = -n` for `n ∈ ℕ`, then the function is undefined, and we
set it to be `0` by convention.)

## Gamma function: main statements (complex case)

* `Complex.Gamma`: the `Γ` function (of a complex variable).
* `Complex.Gamma_eq_integral`: for `0 < re s`, `Γ(s)` agrees with Euler's integral.
* `Complex.Gamma_add_one`: for all `s : ℂ` with `s ≠ 0`, we have `Γ (s + 1) = s Γ(s)`.
* `Complex.Gamma_nat_eq_factorial`: for all `n : ℕ` we have `Γ (n + 1) = n!`.
* `Complex.differentiableAt_Gamma`: `Γ` is complex-differentiable at all `s : ℂ` with
  `s ∉ {-n : n ∈ ℕ}`.

## Gamma function: main statements (real case)

* `Real.Gamma`: the `Γ` function (of a real variable).
* Real counterparts of all the properties of the complex Gamma function listed above:
  `Real.Gamma_eq_integral`, `Real.Gamma_add_one`, `Real.Gamma_nat_eq_factorial`,
  `Real.differentiableAt_Gamma`.

## Tags

Gamma
-/


noncomputable section

set_option linter.uppercaseLean3 false

open Filter intervalIntegral Set Real MeasureTheory Asymptotics

open scoped Nat Topology ComplexConjugate

namespace Real

/-- Asymptotic bound for the `Γ` function integrand. -/
theorem Gamma_integrand_isLittleO (s : ℝ) :
    (fun x : ℝ => exp (-x) * x ^ s) =o[atTop] fun x : ℝ => exp (-(1 / 2) * x) := by
  refine' isLittleO_of_tendsto (fun x hx => _) _
  -- ⊢ exp (-x) * x ^ s = 0
  · exfalso; exact (exp_pos (-(1 / 2) * x)).ne' hx
    -- ⊢ False
             -- 🎉 no goals
  have : (fun x : ℝ => exp (-x) * x ^ s / exp (-(1 / 2) * x)) =
      (fun x : ℝ => exp (1 / 2 * x) / x ^ s)⁻¹ := by
    ext1 x
    field_simp [exp_ne_zero, exp_neg, ← Real.exp_add]
    left
    ring
  rw [this]
  -- ⊢ Tendsto (fun x => exp (1 / 2 * x) / x ^ s)⁻¹ atTop (𝓝 0)
  exact (tendsto_exp_mul_div_rpow_atTop s (1 / 2) one_half_pos).inv_tendsto_atTop
  -- 🎉 no goals
#align real.Gamma_integrand_is_o Real.Gamma_integrand_isLittleO

/-- The Euler integral for the `Γ` function converges for positive real `s`. -/
theorem GammaIntegral_convergent {s : ℝ} (h : 0 < s) :
    IntegrableOn (fun x : ℝ => exp (-x) * x ^ (s - 1)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (@zero_le_one ℝ _ _ _ _), integrableOn_union]
  -- ⊢ IntegrableOn (fun x => exp (-x) * x ^ (s - 1)) (Ioc 0 1) ∧ IntegrableOn (fun …
  constructor
  -- ⊢ IntegrableOn (fun x => exp (-x) * x ^ (s - 1)) (Ioc 0 1)
  · rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    -- ⊢ IntegrableOn (fun x => exp (-x) * x ^ (s - 1)) (Icc 0 1)
    refine' IntegrableOn.continuousOn_mul continuousOn_id.neg.exp _ isCompact_Icc
    -- ⊢ IntegrableOn (fun x => x ^ (s - 1)) (Icc 0 1)
    refine' (intervalIntegrable_iff_integrable_Icc_of_le zero_le_one).mp _
    -- ⊢ IntervalIntegrable (fun x => x ^ (s - 1)) volume 0 1
    exact intervalIntegrable_rpow' (by linarith)
    -- 🎉 no goals
  · refine' integrable_of_isBigO_exp_neg one_half_pos _ (Gamma_integrand_isLittleO _).isBigO
    -- ⊢ ContinuousOn (fun x => exp (-x) * x ^ (s - 1)) (Ici 1)
    refine' continuousOn_id.neg.exp.mul (continuousOn_id.rpow_const _)
    -- ⊢ ∀ (x : ℝ), x ∈ Ici 1 → id x ≠ 0 ∨ 0 ≤ s - 1
    intro x hx
    -- ⊢ id x ≠ 0 ∨ 0 ≤ s - 1
    exact Or.inl ((zero_lt_one : (0 : ℝ) < 1).trans_le hx).ne'
    -- 🎉 no goals
#align real.Gamma_integral_convergent Real.GammaIntegral_convergent

end Real

namespace Complex

/- Technical note: In defining the Gamma integrand exp (-x) * x ^ (s - 1) for s complex, we have to
make a choice between ↑(Real.exp (-x)), Complex.exp (↑(-x)), and Complex.exp (-↑x), all of which are
equal but not definitionally so. We use the first of these throughout. -/
/-- The integral defining the `Γ` function converges for complex `s` with `0 < re s`.

This is proved by reduction to the real case. -/
theorem GammaIntegral_convergent {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x => (-x).exp * x ^ (s - 1) : ℝ → ℂ) (Ioi 0) := by
  constructor
  -- ⊢ AEStronglyMeasurable (fun x => ↑(Real.exp (-x)) * ↑x ^ (s - 1)) (Measure.res …
  · refine' ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    -- ⊢ ContinuousOn (fun x => ↑(Real.exp (-x)) * ↑x ^ (s - 1)) (Ioi 0)
    apply (continuous_ofReal.comp continuous_neg.exp).continuousOn.mul
    -- ⊢ ContinuousOn (fun x => ↑x ^ (s - 1)) (Ioi 0)
    apply ContinuousAt.continuousOn
    -- ⊢ ∀ (x : ℝ), x ∈ Ioi 0 → ContinuousAt (fun x => ↑x ^ (s - 1)) x
    intro x hx
    -- ⊢ ContinuousAt (fun x => ↑x ^ (s - 1)) x
    have : ContinuousAt (fun x : ℂ => x ^ (s - 1)) ↑x := by
      apply continuousAt_cpow_const; rw [ofReal_re]; exact Or.inl hx
    exact ContinuousAt.comp this continuous_ofReal.continuousAt
    -- 🎉 no goals
  · rw [← hasFiniteIntegral_norm_iff]
    -- ⊢ HasFiniteIntegral fun a => ‖↑(Real.exp (-a)) * ↑a ^ (s - 1)‖
    refine' HasFiniteIntegral.congr (Real.GammaIntegral_convergent hs).2 _
    -- ⊢ (fun x => Real.exp (-x) * x ^ (s.re - 1)) =ᵐ[Measure.restrict volume (Ioi 0) …
    refine' (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => _)
    -- ⊢ (fun x => Real.exp (-x) * x ^ (s.re - 1)) x = (fun a => ‖↑(Real.exp (-a)) *  …
    dsimp only
    -- ⊢ Real.exp (-x) * x ^ (s.re - 1) = ‖↑(Real.exp (-x)) * ↑x ^ (s - 1)‖
    rw [norm_eq_abs, map_mul, abs_of_nonneg <| le_of_lt <| exp_pos <| -x,
      abs_cpow_eq_rpow_re_of_pos hx _]
    simp
    -- 🎉 no goals
#align complex.Gamma_integral_convergent Complex.GammaIntegral_convergent

/-- Euler's integral for the `Γ` function (of a complex variable `s`), defined as
`∫ x in Ioi 0, exp (-x) * x ^ (s - 1)`.

See `Complex.GammaIntegral_convergent` for a proof of the convergence of the integral for
`0 < re s`. -/
def GammaIntegral (s : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), ↑(-x).exp * ↑x ^ (s - 1)
#align complex.Gamma_integral Complex.GammaIntegral

theorem GammaIntegral_conj (s : ℂ) : GammaIntegral (conj s) = conj (GammaIntegral s) := by
  rw [GammaIntegral, GammaIntegral, ← integral_conj]
  -- ⊢ ∫ (x : ℝ) in Ioi 0, ↑(Real.exp (-x)) * ↑x ^ (↑(starRingEnd ℂ) s - 1) = ∫ (a  …
  refine' set_integral_congr measurableSet_Ioi fun x hx => _
  -- ⊢ ↑(Real.exp (-x)) * ↑x ^ (↑(starRingEnd ℂ) s - 1) = ↑(starRingEnd ℂ) (↑(Real. …
  dsimp only
  -- ⊢ ↑(Real.exp (-x)) * ↑x ^ (↑(starRingEnd ℂ) s - 1) = ↑(starRingEnd ℂ) (↑(Real. …
  rw [RingHom.map_mul, conj_ofReal, cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)), ← exp_conj, RingHom.map_mul, ←
    ofReal_log (le_of_lt hx), conj_ofReal, RingHom.map_sub, RingHom.map_one]
#align complex.Gamma_integral_conj Complex.GammaIntegral_conj

theorem GammaIntegral_ofReal (s : ℝ) :
    GammaIntegral ↑s = ↑(∫ x : ℝ in Ioi 0, Real.exp (-x) * x ^ (s - 1)) := by
  have : ∀ r : ℝ, Complex.ofReal' r = @IsROrC.ofReal ℂ _ r := fun r => rfl
  -- ⊢ GammaIntegral ↑s = ↑(∫ (x : ℝ) in Ioi 0, Real.exp (-x) * x ^ (s - 1))
  rw [GammaIntegral]
  -- ⊢ ∫ (x : ℝ) in Ioi 0, ↑(Real.exp (-x)) * ↑x ^ (↑s - 1) = ↑(∫ (x : ℝ) in Ioi 0, …
  conv_rhs => rw [this, ← _root_.integral_ofReal]
  -- ⊢ ∫ (x : ℝ) in Ioi 0, ↑(Real.exp (-x)) * ↑x ^ (↑s - 1) = ∫ (a : ℝ) in Ioi 0, ↑ …
  refine' set_integral_congr measurableSet_Ioi _
  -- ⊢ EqOn (fun x => ↑(Real.exp (-x)) * ↑x ^ (↑s - 1)) (fun a => ↑(Real.exp (-a) * …
  intro x hx; dsimp only
  -- ⊢ (fun x => ↑(Real.exp (-x)) * ↑x ^ (↑s - 1)) x = (fun a => ↑(Real.exp (-a) *  …
              -- ⊢ ↑(Real.exp (-x)) * ↑x ^ (↑s - 1) = ↑(Real.exp (-x) * x ^ (s - 1))
  conv_rhs => rw [← this]
  -- ⊢ ↑(Real.exp (-x)) * ↑x ^ (↑s - 1) = ↑(Real.exp (-x) * x ^ (s - 1))
  rw [ofReal_mul, ofReal_cpow (mem_Ioi.mp hx).le]
  -- ⊢ ↑(Real.exp (-x)) * ↑x ^ (↑s - 1) = ↑(Real.exp (-x)) * ↑x ^ ↑(s - 1)
  simp
  -- 🎉 no goals
#align complex.Gamma_integral_of_real Complex.GammaIntegral_ofReal

theorem GammaIntegral_one : GammaIntegral 1 = 1 := by
  simpa only [← ofReal_one, GammaIntegral_ofReal, ofReal_inj, sub_self, rpow_zero,
    mul_one] using integral_exp_neg_Ioi_zero
#align complex.Gamma_integral_one Complex.GammaIntegral_one

end Complex

/-! Now we establish the recurrence relation `Γ(s + 1) = s * Γ(s)` using integration by parts. -/


namespace Complex

section GammaRecurrence

/-- The indefinite version of the `Γ` function, `Γ(s, X) = ∫ x ∈ 0..X, exp(-x) x ^ (s - 1)`. -/
def partialGamma (s : ℂ) (X : ℝ) : ℂ :=
  ∫ x in (0)..X, (-x).exp * x ^ (s - 1)
#align complex.partial_Gamma Complex.partialGamma

theorem tendsto_partialGamma {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun X : ℝ => partialGamma s X) atTop (𝓝 <| GammaIntegral s) :=
  intervalIntegral_tendsto_integral_Ioi 0 (GammaIntegral_convergent hs) tendsto_id
#align complex.tendsto_partial_Gamma Complex.tendsto_partialGamma

private theorem Gamma_integrand_interval_integrable (s : ℂ) {X : ℝ} (hs : 0 < s.re) (hX : 0 ≤ X) :
    IntervalIntegrable (fun x => (-x).exp * x ^ (s - 1) : ℝ → ℂ) volume 0 X := by
  rw [intervalIntegrable_iff_integrable_Ioc_of_le hX]
  -- ⊢ IntegrableOn (fun x => ↑(Real.exp (-x)) * ↑x ^ (s - 1)) (Ioc 0 X)
  exact IntegrableOn.mono_set (GammaIntegral_convergent hs) Ioc_subset_Ioi_self
  -- 🎉 no goals

private theorem Gamma_integrand_deriv_integrable_A {s : ℂ} (hs : 0 < s.re) {X : ℝ} (hX : 0 ≤ X) :
    IntervalIntegrable (fun x => -((-x).exp * x ^ s) : ℝ → ℂ) volume 0 X := by
  convert (Gamma_integrand_interval_integrable (s + 1) _ hX).neg
  -- ⊢ -(↑(Real.exp (-x✝)) * ↑x✝ ^ s) = (-fun x => ↑(Real.exp (-x)) * ↑x ^ (s + 1 - …
  · simp only [ofReal_exp, ofReal_neg, add_sub_cancel]; rfl
    -- ⊢ -(exp (-↑x✝) * ↑x✝ ^ s) = (-fun x => exp (-↑x) * ↑x ^ s) x✝
                                                        -- 🎉 no goals
  · simp only [add_re, one_re]; linarith
    -- ⊢ 0 < s.re + 1
                                -- 🎉 no goals

private theorem Gamma_integrand_deriv_integrable_B {s : ℂ} (hs : 0 < s.re) {Y : ℝ} (hY : 0 ≤ Y) :
    IntervalIntegrable (fun x : ℝ => (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) volume 0 Y := by
  have : (fun x => (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) =
      (fun x => s * ((-x).exp * x ^ (s - 1)) : ℝ → ℂ) := by ext1; ring
  rw [this, intervalIntegrable_iff_integrable_Ioc_of_le hY]
  -- ⊢ IntegrableOn (fun x => s * (↑(Real.exp (-x)) * ↑x ^ (s - 1))) (Ioc 0 Y)
  constructor
  -- ⊢ AEStronglyMeasurable (fun x => s * (↑(Real.exp (-x)) * ↑x ^ (s - 1))) (Measu …
  · refine' (continuousOn_const.mul _).aestronglyMeasurable measurableSet_Ioc
    -- ⊢ ContinuousOn (fun x => ↑(Real.exp (-x)) * ↑x ^ (s - 1)) (Ioc 0 Y)
    apply (continuous_ofReal.comp continuous_neg.exp).continuousOn.mul
    -- ⊢ ContinuousOn (fun x => ↑x ^ (s - 1)) (Ioc 0 Y)
    apply ContinuousAt.continuousOn
    -- ⊢ ∀ (x : ℝ), x ∈ Ioc 0 Y → ContinuousAt (fun x => ↑x ^ (s - 1)) x
    intro x hx
    -- ⊢ ContinuousAt (fun x => ↑x ^ (s - 1)) x
    refine' (_ : ContinuousAt (fun x : ℂ => x ^ (s - 1)) _).comp continuous_ofReal.continuousAt
    -- ⊢ ContinuousAt (fun x => x ^ (s - 1)) ↑x
    apply continuousAt_cpow_const; rw [ofReal_re]; exact Or.inl hx.1
    -- ⊢ 0 < (↑x).re ∨ (↑x).im ≠ 0
                                   -- ⊢ 0 < x ∨ (↑x).im ≠ 0
                                                   -- 🎉 no goals
  rw [← hasFiniteIntegral_norm_iff]
  -- ⊢ HasFiniteIntegral fun a => ‖s * (↑(Real.exp (-a)) * ↑a ^ (s - 1))‖
  simp_rw [norm_eq_abs, map_mul]
  -- ⊢ HasFiniteIntegral fun a => ↑abs s * (↑abs ↑(Real.exp (-a)) * ↑abs (↑a ^ (s - …
  refine' (((Real.GammaIntegral_convergent hs).mono_set
    Ioc_subset_Ioi_self).hasFiniteIntegral.congr _).const_mul _
  rw [EventuallyEq, ae_restrict_iff']
  -- ⊢ ∀ᵐ (x : ℝ), x ∈ Ioc 0 Y → Real.exp (-x) * x ^ (s.re - 1) = ↑abs ↑(Real.exp ( …
  · apply ae_of_all; intro x hx
    -- ⊢ ∀ (a : ℝ), a ∈ Ioc 0 Y → Real.exp (-a) * a ^ (s.re - 1) = ↑abs ↑(Real.exp (- …
                     -- ⊢ Real.exp (-x) * x ^ (s.re - 1) = ↑abs ↑(Real.exp (-x)) * ↑abs (↑x ^ (s - 1))
    rw [abs_of_nonneg (exp_pos _).le, abs_cpow_eq_rpow_re_of_pos hx.1]
    -- ⊢ Real.exp (-x) * x ^ (s.re - 1) = Real.exp (-x) * x ^ (s - 1).re
    simp
    -- 🎉 no goals
  · exact measurableSet_Ioc
    -- 🎉 no goals

/-- The recurrence relation for the indefinite version of the `Γ` function. -/
theorem partialGamma_add_one {s : ℂ} (hs : 0 < s.re) {X : ℝ} (hX : 0 ≤ X) :
    partialGamma (s + 1) X = s * partialGamma s X - (-X).exp * X ^ s := by
  rw [partialGamma, partialGamma, add_sub_cancel]
  -- ⊢ ∫ (x : ℝ) in 0 ..X, ↑(Real.exp (-x)) * ↑x ^ s = (s * ∫ (x : ℝ) in 0 ..X, ↑(R …
  have F_der_I : ∀ x : ℝ, x ∈ Ioo 0 X → HasDerivAt (fun x => (-x).exp * x ^ s : ℝ → ℂ)
      (-((-x).exp * x ^ s) + (-x).exp * (s * x ^ (s - 1))) x := by
    intro x hx
    have d1 : HasDerivAt (fun y : ℝ => (-y).exp) (-(-x).exp) x := by
      simpa using (hasDerivAt_neg x).exp
    have d2 : HasDerivAt (fun y : ℝ => ↑y ^ s) (s * x ^ (s - 1)) x := by
      have t := @HasDerivAt.cpow_const _ _ _ s (hasDerivAt_id ↑x) ?_
      simpa only [mul_one] using t.comp_ofReal
      simpa only [id.def, ofReal_re, ofReal_im, Ne.def, eq_self_iff_true, not_true, or_false_iff,
        mul_one] using hx.1
    simpa only [ofReal_neg, neg_mul] using d1.ofReal_comp.mul d2
  have cont := (continuous_ofReal.comp continuous_neg.exp).mul (continuous_ofReal_cpow_const hs)
  -- ⊢ ∫ (x : ℝ) in 0 ..X, ↑(Real.exp (-x)) * ↑x ^ s = (s * ∫ (x : ℝ) in 0 ..X, ↑(R …
  have der_ible :=
    (Gamma_integrand_deriv_integrable_A hs hX).add (Gamma_integrand_deriv_integrable_B hs hX)
  have int_eval := integral_eq_sub_of_hasDerivAt_of_le hX cont.continuousOn F_der_I der_ible
  -- ⊢ ∫ (x : ℝ) in 0 ..X, ↑(Real.exp (-x)) * ↑x ^ s = (s * ∫ (x : ℝ) in 0 ..X, ↑(R …
  -- We are basically done here but manipulating the output into the right form is fiddly.
  apply_fun fun x : ℂ => -x at int_eval
  -- ⊢ ∫ (x : ℝ) in 0 ..X, ↑(Real.exp (-x)) * ↑x ^ s = (s * ∫ (x : ℝ) in 0 ..X, ↑(R …
  rw [intervalIntegral.integral_add (Gamma_integrand_deriv_integrable_A hs hX)
      (Gamma_integrand_deriv_integrable_B hs hX),
    intervalIntegral.integral_neg, neg_add, neg_neg] at int_eval
  rw [eq_sub_of_add_eq int_eval, sub_neg_eq_add, neg_sub, add_comm, add_sub]
  -- ⊢ (∫ (x : ℝ) in 0 ..X, ↑(Real.exp (-x)) * (s * ↑x ^ (s - 1))) + (ofReal' ∘ fun …
  have : (fun x => (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) =
      (fun x => s * (-x).exp * x ^ (s - 1) : ℝ → ℂ) := by ext1; ring
  rw [this]
  -- ⊢ (∫ (x : ℝ) in 0 ..X, s * ↑(Real.exp (-x)) * ↑x ^ (s - 1)) + (ofReal' ∘ fun y …
  have t := @integral_const_mul 0 X volume _ _ s fun x : ℝ => (-x).exp * x ^ (s - 1)
  -- ⊢ (∫ (x : ℝ) in 0 ..X, s * ↑(Real.exp (-x)) * ↑x ^ (s - 1)) + (ofReal' ∘ fun y …
  rw [← t, ofReal_zero, zero_cpow]
  -- ⊢ (∫ (x : ℝ) in 0 ..X, s * ↑(Real.exp (-x)) * ↑x ^ (s - 1)) + (ofReal' ∘ fun y …
  · rw [mul_zero, add_zero]; congr 2; ext1; ring
    -- ⊢ (∫ (x : ℝ) in 0 ..X, s * ↑(Real.exp (-x)) * ↑x ^ (s - 1)) - (ofReal' ∘ fun y …
                             -- ⊢ (fun x => s * ↑(Real.exp (-x)) * ↑x ^ (s - 1)) = fun x => s * (↑(Real.exp (- …
                                      -- ⊢ s * ↑(Real.exp (-x✝)) * ↑x✝ ^ (s - 1) = s * (↑(Real.exp (-x✝)) * ↑x✝ ^ (s -  …
                                            -- 🎉 no goals
  · contrapose! hs; rw [hs, zero_re]
    -- ⊢ s.re ≤ 0
                    -- 🎉 no goals
#align complex.partial_Gamma_add_one Complex.partialGamma_add_one

/-- The recurrence relation for the `Γ` integral. -/
theorem GammaIntegral_add_one {s : ℂ} (hs : 0 < s.re) :
    GammaIntegral (s + 1) = s * GammaIntegral s := by
  suffices Tendsto (s + 1).partialGamma atTop (𝓝 <| s * GammaIntegral s) by
    refine' tendsto_nhds_unique _ this
    apply tendsto_partialGamma; rw [add_re, one_re]; linarith
  have : (fun X : ℝ => s * partialGamma s X - X ^ s * (-X).exp) =ᶠ[atTop]
      (s + 1).partialGamma := by
    apply eventuallyEq_of_mem (Ici_mem_atTop (0 : ℝ))
    intro X hX
    rw [partialGamma_add_one hs (mem_Ici.mp hX)]
    ring_nf
  refine' Tendsto.congr' this _
  -- ⊢ Tendsto (fun X => s * partialGamma s X - ↑X ^ s * ↑(Real.exp (-X))) atTop (𝓝 …
  suffices Tendsto (fun X => -X ^ s * (-X).exp : ℝ → ℂ) atTop (𝓝 0) by
    simpa using Tendsto.add (Tendsto.const_mul s (tendsto_partialGamma hs)) this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  -- ⊢ Tendsto (fun e => ‖-↑e ^ s * ↑(Real.exp (-e))‖) atTop (𝓝 0)
  have :
      (fun e : ℝ => ‖-(e : ℂ) ^ s * (-e).exp‖) =ᶠ[atTop] fun e : ℝ => e ^ s.re * (-1 * e).exp := by
    refine' eventuallyEq_of_mem (Ioi_mem_atTop 0) _
    intro x hx; dsimp only
    rw [norm_eq_abs, map_mul, abs.map_neg, abs_cpow_eq_rpow_re_of_pos hx,
      abs_of_nonneg (exp_pos (-x)).le, neg_mul, one_mul]
  exact (tendsto_congr' this).mpr (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_0 _ _ zero_lt_one)
  -- 🎉 no goals
#align complex.Gamma_integral_add_one Complex.GammaIntegral_add_one

end GammaRecurrence

/-! Now we define `Γ(s)` on the whole complex plane, by recursion. -/


section GammaDef

/-- The `n`th function in this family is `Γ(s)` if `-n < s.re`, and junk otherwise. -/
noncomputable def GammaAux : ℕ → ℂ → ℂ
  | 0 => GammaIntegral
  | n + 1 => fun s : ℂ => GammaAux n (s + 1) / s
#align complex.Gamma_aux Complex.GammaAux

theorem GammaAux_recurrence1 (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) :
    GammaAux n s = GammaAux n (s + 1) / s := by
  induction' n with n hn generalizing s
  -- ⊢ GammaAux Nat.zero s = GammaAux Nat.zero (s + 1) / s
  · simp only [Nat.zero_eq, CharP.cast_eq_zero, Left.neg_neg_iff] at h1
    -- ⊢ GammaAux Nat.zero s = GammaAux Nat.zero (s + 1) / s
    dsimp only [GammaAux]; rw [GammaIntegral_add_one h1]
    -- ⊢ GammaIntegral s = GammaIntegral (s + 1) / s
                           -- ⊢ GammaIntegral s = s * GammaIntegral s / s
    rw [mul_comm, mul_div_cancel]; contrapose! h1; rw [h1]
    -- ⊢ s ≠ 0
                                   -- ⊢ s.re ≤ 0
                                                   -- ⊢ 0.re ≤ 0
    simp
    -- 🎉 no goals
  · dsimp only [GammaAux]
    -- ⊢ GammaAux n (s + 1) / s = GammaAux n (s + 1 + 1) / (s + 1) / s
    have hh1 : -(s + 1).re < n := by
      rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at h1
      rw [add_re, one_re]; linarith
    rw [← hn (s + 1) hh1]
    -- 🎉 no goals
#align complex.Gamma_aux_recurrence1 Complex.GammaAux_recurrence1

theorem GammaAux_recurrence2 (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) :
    GammaAux n s = GammaAux (n + 1) s := by
  cases' n with n n
  -- ⊢ GammaAux Nat.zero s = GammaAux (Nat.zero + 1) s
  · simp only [Nat.zero_eq, CharP.cast_eq_zero, Left.neg_neg_iff] at h1
    -- ⊢ GammaAux Nat.zero s = GammaAux (Nat.zero + 1) s
    dsimp only [GammaAux]
    -- ⊢ GammaIntegral s = GammaIntegral (s + 1) / s
    rw [GammaIntegral_add_one h1, mul_div_cancel_left]
    -- ⊢ s ≠ 0
    rintro rfl
    -- ⊢ False
    rw [zero_re] at h1
    -- ⊢ False
    exact h1.false
    -- 🎉 no goals
  · dsimp only [GammaAux]
    -- ⊢ GammaAux n (s + 1) / s = GammaAux n (s + 1 + 1) / (s + 1) / s
    have : GammaAux n (s + 1 + 1) / (s + 1) = GammaAux n (s + 1) := by
      have hh1 : -(s + 1).re < n := by
        rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at h1
        rw [add_re, one_re]; linarith
      rw [GammaAux_recurrence1 (s + 1) n hh1]
    rw [this]
    -- 🎉 no goals
#align complex.Gamma_aux_recurrence2 Complex.GammaAux_recurrence2

/-- The `Γ` function (of a complex variable `s`). -/
-- @[pp_nodot] -- Porting note: removed
def Gamma (s : ℂ) : ℂ :=
  GammaAux ⌊1 - s.re⌋₊ s
#align complex.Gamma Complex.Gamma

theorem Gamma_eq_GammaAux (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) : Gamma s = GammaAux n s := by
  have u : ∀ k : ℕ, GammaAux (⌊1 - s.re⌋₊ + k) s = Gamma s := by
    intro k; induction' k with k hk
    · simp [Gamma]
    · rw [← hk, Nat.succ_eq_add_one, ← add_assoc]
      refine' (GammaAux_recurrence2 s (⌊1 - s.re⌋₊ + k) _).symm
      rw [Nat.cast_add]
      have i0 := Nat.sub_one_lt_floor (1 - s.re)
      simp only [sub_sub_cancel_left] at i0
      refine' lt_add_of_lt_of_nonneg i0 _
      rw [← Nat.cast_zero, Nat.cast_le]; exact Nat.zero_le k
  convert (u <| n - ⌊1 - s.re⌋₊).symm; rw [Nat.add_sub_of_le]
  -- ⊢ n = ⌊1 - s.re⌋₊ + (n - ⌊1 - s.re⌋₊)
                                       -- ⊢ ⌊1 - s.re⌋₊ ≤ n
  by_cases 0 ≤ 1 - s.re
  -- ⊢ ⌊1 - s.re⌋₊ ≤ n
  -- ⊢ ⌊1 - s.re⌋₊ ≤ n
  · apply Nat.le_of_lt_succ
    -- ⊢ ⌊1 - s.re⌋₊ < Nat.succ n
    exact_mod_cast lt_of_le_of_lt (Nat.floor_le h) (by linarith : 1 - s.re < n + 1)
    -- 🎉 no goals
  · rw [Nat.floor_of_nonpos]; linarith; linarith
    -- ⊢ 0 ≤ n
                              -- ⊢ 1 - s.re ≤ 0
                                        -- 🎉 no goals
#align complex.Gamma_eq_Gamma_aux Complex.Gamma_eq_GammaAux

/-- The recurrence relation for the `Γ` function. -/
theorem Gamma_add_one (s : ℂ) (h2 : s ≠ 0) : Gamma (s + 1) = s * Gamma s := by
  let n := ⌊1 - s.re⌋₊
  -- ⊢ Gamma (s + 1) = s * Gamma s
  have t1 : -s.re < n := by simpa only [sub_sub_cancel_left] using Nat.sub_one_lt_floor (1 - s.re)
  -- ⊢ Gamma (s + 1) = s * Gamma s
  have t2 : -(s + 1).re < n := by rw [add_re, one_re]; linarith
  -- ⊢ Gamma (s + 1) = s * Gamma s
  rw [Gamma_eq_GammaAux s n t1, Gamma_eq_GammaAux (s + 1) n t2, GammaAux_recurrence1 s n t1]
  -- ⊢ GammaAux n (s + 1) = s * (GammaAux n (s + 1) / s)
  field_simp; ring
  -- ⊢ GammaAux ⌊1 - s.re⌋₊ (s + 1) * s = s * GammaAux ⌊1 - s.re⌋₊ (s + 1)
              -- 🎉 no goals
#align complex.Gamma_add_one Complex.Gamma_add_one

theorem Gamma_eq_integral {s : ℂ} (hs : 0 < s.re) : Gamma s = GammaIntegral s :=
  Gamma_eq_GammaAux s 0 (by norm_cast; linarith)
                            -- ⊢ -s.re < 0
                                       -- 🎉 no goals
#align complex.Gamma_eq_integral Complex.Gamma_eq_integral

theorem Gamma_one : Gamma 1 = 1 := by rw [Gamma_eq_integral]; simpa using GammaIntegral_one; simp
                                                              -- ⊢ 0 < 1.re
                                                                                             -- 🎉 no goals
#align complex.Gamma_one Complex.Gamma_one

theorem Gamma_nat_eq_factorial (n : ℕ) : Gamma (n + 1) = n ! := by
  induction' n with n hn
  -- ⊢ Gamma (↑Nat.zero + 1) = ↑Nat.zero !
  · simpa using Gamma_one
    -- 🎉 no goals
  · rw [Gamma_add_one n.succ <| Nat.cast_ne_zero.mpr <| Nat.succ_ne_zero n]
    -- ⊢ ↑(Nat.succ n) * Gamma ↑(Nat.succ n) = ↑(Nat.succ n)!
    simp only [Nat.cast_succ, Nat.factorial_succ, Nat.cast_mul]; congr
    -- ⊢ (↑n + 1) * Gamma (↑n + 1) = (↑n + 1) * ↑n !
                                                                 -- 🎉 no goals
#align complex.Gamma_nat_eq_factorial Complex.Gamma_nat_eq_factorial

/-- At `0` the Gamma function is undefined; by convention we assign it the value `0`. -/
theorem Gamma_zero : Gamma 0 = 0 := by
  simp_rw [Gamma, zero_re, sub_zero, Nat.floor_one, GammaAux, div_zero]
  -- 🎉 no goals
#align complex.Gamma_zero Complex.Gamma_zero

/-- At `-n` for `n ∈ ℕ`, the Gamma function is undefined; by convention we assign it the value 0. -/
theorem Gamma_neg_nat_eq_zero (n : ℕ) : Gamma (-n) = 0 := by
  induction' n with n IH
  -- ⊢ Gamma (-↑Nat.zero) = 0
  · rw [Nat.cast_zero, neg_zero, Gamma_zero]
    -- 🎉 no goals
  · have A : -(n.succ : ℂ) ≠ 0 := by
      rw [neg_ne_zero, Nat.cast_ne_zero]
      apply Nat.succ_ne_zero
    have : -(n : ℂ) = -↑n.succ + 1 := by simp
    -- ⊢ Gamma (-↑(Nat.succ n)) = 0
    rw [this, Gamma_add_one _ A] at IH
    -- ⊢ Gamma (-↑(Nat.succ n)) = 0
    contrapose! IH
    -- ⊢ -↑(Nat.succ n) * Gamma (-↑(Nat.succ n)) ≠ 0
    exact mul_ne_zero A IH
    -- 🎉 no goals
#align complex.Gamma_neg_nat_eq_zero Complex.Gamma_neg_nat_eq_zero

theorem Gamma_conj (s : ℂ) : Gamma (conj s) = conj (Gamma s) := by
  suffices : ∀ (n : ℕ) (s : ℂ), GammaAux n (conj s) = conj (GammaAux n s); exact this _ _
  -- ⊢ Gamma (↑(starRingEnd ℂ) s) = ↑(starRingEnd ℂ) (Gamma s)
                                                                           -- ⊢ ∀ (n : ℕ) (s : ℂ), GammaAux n (↑(starRingEnd ℂ) s) = ↑(starRingEnd ℂ) (Gamma …
  intro n
  -- ⊢ ∀ (s : ℂ), GammaAux n (↑(starRingEnd ℂ) s) = ↑(starRingEnd ℂ) (GammaAux n s)
  induction' n with n IH
  -- ⊢ ∀ (s : ℂ), GammaAux Nat.zero (↑(starRingEnd ℂ) s) = ↑(starRingEnd ℂ) (GammaA …
  · rw [GammaAux]; exact GammaIntegral_conj
    -- ⊢ ∀ (s : ℂ), GammaIntegral (↑(starRingEnd ℂ) s) = ↑(starRingEnd ℂ) (GammaInteg …
                   -- 🎉 no goals
  · intro s
    -- ⊢ GammaAux (Nat.succ n) (↑(starRingEnd ℂ) s) = ↑(starRingEnd ℂ) (GammaAux (Nat …
    rw [GammaAux]
    -- ⊢ (fun s => GammaAux n (s + 1) / s) (↑(starRingEnd ℂ) s) = ↑(starRingEnd ℂ) (( …
    dsimp only
    -- ⊢ GammaAux n (↑(starRingEnd ℂ) s + 1) / ↑(starRingEnd ℂ) s = ↑(starRingEnd ℂ)  …
    rw [div_eq_mul_inv _ s, RingHom.map_mul, conj_inv, ← div_eq_mul_inv]
    -- ⊢ GammaAux n (↑(starRingEnd ℂ) s + 1) / ↑(starRingEnd ℂ) s = ↑(starRingEnd ℂ)  …
    suffices conj s + 1 = conj (s + 1) by rw [this, IH]
    -- ⊢ ↑(starRingEnd ℂ) s + 1 = ↑(starRingEnd ℂ) (s + 1)
    rw [RingHom.map_add, RingHom.map_one]
    -- 🎉 no goals
#align complex.Gamma_conj Complex.Gamma_conj

end GammaDef

/-! Now check that the `Γ` function is differentiable, wherever this makes sense. -/


section GammaHasDeriv

/-- Rewrite the Gamma integral as an example of a Mellin transform. -/
theorem GammaIntegral_eq_mellin : GammaIntegral = mellin fun x => ↑(Real.exp (-x)) :=
  funext fun s => by simp only [mellin, GammaIntegral, smul_eq_mul, mul_comm]
                     -- 🎉 no goals
#align complex.Gamma_integral_eq_mellin Complex.GammaIntegral_eq_mellin

/-- The derivative of the `Γ` integral, at any `s ∈ ℂ` with `1 < re s`, is given by the Melllin
transform of `log t * exp (-t)`. -/
theorem hasDerivAt_GammaIntegral {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt GammaIntegral (∫ t : ℝ in Ioi 0, t ^ (s - 1) * (Real.log t * Real.exp (-t))) s := by
  rw [GammaIntegral_eq_mellin]
  -- ⊢ HasDerivAt (mellin fun x => ↑(Real.exp (-x))) (∫ (t : ℝ) in Ioi 0, ↑t ^ (s - …
  convert (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ) _ _ (lt_add_one _) _ hs).2
  · refine' (Continuous.continuousOn _).locallyIntegrableOn measurableSet_Ioi
    -- ⊢ Continuous fun x => ↑(Real.exp (-x))
    exact continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)
    -- 🎉 no goals
  · rw [← isBigO_norm_left]
    -- ⊢ (fun x => ‖↑(Real.exp (-x))‖) =O[atTop] fun x => x ^ (-(s.re + 1))
    simp_rw [Complex.norm_eq_abs, abs_ofReal, ← Real.norm_eq_abs, isBigO_norm_left]
    -- ⊢ (fun x => Real.exp (-x)) =O[atTop] fun x => x ^ (-(s.re + 1))
    simpa only [neg_one_mul] using (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one _).isBigO
    -- 🎉 no goals
  · simp_rw [neg_zero, rpow_zero]
    -- ⊢ (fun x => ↑(Real.exp (-x))) =O[𝓝[Ioi 0] 0] fun x => 1
    refine' isBigO_const_of_tendsto (_ : Tendsto _ _ (𝓝 (1 : ℂ))) one_ne_zero
    -- ⊢ Tendsto (fun x => ↑(Real.exp (-x))) (𝓝[Ioi 0] 0) (𝓝 1)
    rw [(by simp : (1 : ℂ) = Real.exp (-0))]
    -- ⊢ Tendsto (fun x => ↑(Real.exp (-x))) (𝓝[Ioi 0] 0) (𝓝 ↑(Real.exp (-0)))
    exact (continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousWithinAt
    -- 🎉 no goals
#align complex.has_deriv_at_Gamma_integral Complex.hasDerivAt_GammaIntegral

theorem differentiableAt_GammaAux (s : ℂ) (n : ℕ) (h1 : 1 - s.re < n) (h2 : ∀ m : ℕ, s ≠ -m) :
    DifferentiableAt ℂ (GammaAux n) s := by
  induction' n with n hn generalizing s
  -- ⊢ DifferentiableAt ℂ (GammaAux Nat.zero) s
  · refine' (hasDerivAt_GammaIntegral _).differentiableAt
    -- ⊢ 0 < s.re
    rw [Nat.cast_zero] at h1; linarith
    -- ⊢ 0 < s.re
                              -- 🎉 no goals
  · dsimp only [GammaAux]
    -- ⊢ DifferentiableAt ℂ (fun s => GammaAux n (s + 1) / s) s
    specialize hn (s + 1)
    -- ⊢ DifferentiableAt ℂ (fun s => GammaAux n (s + 1) / s) s
    have a : 1 - (s + 1).re < ↑n := by
      rw [Nat.cast_succ] at h1; rw [Complex.add_re, Complex.one_re]; linarith
    have b : ∀ m : ℕ, s + 1 ≠ -m := by
      intro m; have := h2 (1 + m)
      contrapose! this
      rw [← eq_sub_iff_add_eq] at this
      simpa using this
    refine' DifferentiableAt.div (DifferentiableAt.comp _ (hn a b) _) _ _
    · rw [differentiableAt_add_const_iff (1 : ℂ)]; exact differentiableAt_id
      -- ⊢ DifferentiableAt ℂ (fun s => s) s
                                                   -- 🎉 no goals
    · exact differentiableAt_id
      -- 🎉 no goals
    · simpa using h2 0
      -- 🎉 no goals
#align complex.differentiable_at_Gamma_aux Complex.differentiableAt_GammaAux

theorem differentiableAt_Gamma (s : ℂ) (hs : ∀ m : ℕ, s ≠ -m) : DifferentiableAt ℂ Gamma s := by
  let n := ⌊1 - s.re⌋₊ + 1
  -- ⊢ DifferentiableAt ℂ Gamma s
  have hn : 1 - s.re < n := by exact_mod_cast Nat.lt_floor_add_one (1 - s.re)
  -- ⊢ DifferentiableAt ℂ Gamma s
  apply (differentiableAt_GammaAux s n hn hs).congr_of_eventuallyEq
  -- ⊢ Gamma =ᶠ[𝓝 s] GammaAux n
  let S := {t : ℂ | 1 - t.re < n}
  -- ⊢ Gamma =ᶠ[𝓝 s] GammaAux n
  have : S ∈ 𝓝 s := by
    rw [mem_nhds_iff]; use S
    refine' ⟨Subset.rfl, _, hn⟩
    have : S = re ⁻¹' Ioi (1 - n : ℝ) := by
      ext; rw [preimage, Ioi, mem_setOf_eq, mem_setOf_eq, mem_setOf_eq]; exact sub_lt_comm
    rw [this]
    refine' Continuous.isOpen_preimage continuous_re _ isOpen_Ioi
  apply eventuallyEq_of_mem this
  -- ⊢ EqOn Gamma (GammaAux n) S
  intro t ht; rw [mem_setOf_eq] at ht
  -- ⊢ Gamma t = GammaAux n t
              -- ⊢ Gamma t = GammaAux n t
  apply Gamma_eq_GammaAux; linarith
  -- ⊢ -t.re < ↑n
                           -- 🎉 no goals
#align complex.differentiable_at_Gamma Complex.differentiableAt_Gamma

end GammaHasDeriv

/-- At `s = 0`, the Gamma function has a simple pole with residue 1. -/
theorem tendsto_self_mul_Gamma_nhds_zero : Tendsto (fun z : ℂ => z * Gamma z) (𝓝[≠] 0) (𝓝 1) := by
  rw [show 𝓝 (1 : ℂ) = 𝓝 (Gamma (0 + 1)) by simp only [zero_add, Complex.Gamma_one]]
  -- ⊢ Tendsto (fun z => z * Gamma z) (𝓝[{0}ᶜ] 0) (𝓝 (Gamma (0 + 1)))
  convert (Tendsto.mono_left _ nhdsWithin_le_nhds).congr'
    (eventuallyEq_of_mem self_mem_nhdsWithin Complex.Gamma_add_one)
  refine' ContinuousAt.comp (g := Gamma) _ (continuous_id.add continuous_const).continuousAt
  -- ⊢ ContinuousAt Gamma (0 + 1)
  refine' (Complex.differentiableAt_Gamma _ fun m => _).continuousAt
  -- ⊢ 0 + 1 ≠ -↑m
  rw [zero_add, ← ofReal_nat_cast, ← ofReal_neg, ← ofReal_one, Ne.def, ofReal_inj]
  -- ⊢ ¬1 = -↑m
  refine' (lt_of_le_of_lt _ zero_lt_one).ne'
  -- ⊢ -↑m ≤ 0
  exact neg_nonpos.mpr (Nat.cast_nonneg _)
  -- 🎉 no goals
#align complex.tendsto_self_mul_Gamma_nhds_zero Complex.tendsto_self_mul_Gamma_nhds_zero

end Complex

namespace Real

/-- The `Γ` function (of a real variable `s`). -/
-- @[pp_nodot] -- Porting note: removed
def Gamma (s : ℝ) : ℝ :=
  (Complex.Gamma s).re
#align real.Gamma Real.Gamma

theorem Gamma_eq_integral {s : ℝ} (hs : 0 < s) :
    Gamma s = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1) := by
  rw [Gamma, Complex.Gamma_eq_integral (by rwa [Complex.ofReal_re] : 0 < Complex.re s)]
  -- ⊢ (Complex.GammaIntegral ↑s).re = ∫ (x : ℝ) in Ioi 0, exp (-x) * x ^ (s - 1)
  dsimp only [Complex.GammaIntegral]
  -- ⊢ (∫ (x : ℝ) in Ioi 0, ↑(exp (-x)) * ↑x ^ (↑s - 1)).re = ∫ (x : ℝ) in Ioi 0, e …
  simp_rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
  -- ⊢ (∫ (x : ℝ) in Ioi 0, ↑(exp (-x)) * ↑x ^ ↑(s - 1)).re = ∫ (x : ℝ) in Ioi 0, e …
  suffices ∫ x : ℝ in Ioi 0, ↑(exp (-x)) * (x : ℂ) ^ ((s - 1 : ℝ) : ℂ) =
      ∫ x : ℝ in Ioi 0, ((exp (-x) * x ^ (s - 1) : ℝ) : ℂ) by
    have cc : ∀ r : ℝ, Complex.ofReal' r = @IsROrC.ofReal ℂ _ r := fun r => rfl
    conv_lhs => rw [this]; enter [1, 2, x]; rw [cc]
    rw [_root_.integral_ofReal, ← cc, Complex.ofReal_re]
  refine' set_integral_congr measurableSet_Ioi fun x hx => _
  -- ⊢ ↑(exp (-x)) * ↑x ^ ↑(s - 1) = ↑(exp (-x) * x ^ (s - 1))
  push_cast
  -- ⊢ Complex.exp (-↑x) * ↑x ^ (↑s - 1) = Complex.exp (-↑x) * ↑(x ^ (s - 1))
  rw [Complex.ofReal_cpow (le_of_lt hx)]
  -- ⊢ Complex.exp (-↑x) * ↑x ^ (↑s - 1) = Complex.exp (-↑x) * ↑x ^ ↑(s - 1)
  push_cast; rfl
  -- ⊢ Complex.exp (-↑x) * ↑x ^ (↑s - 1) = Complex.exp (-↑x) * ↑x ^ (↑s - 1)
             -- 🎉 no goals
#align real.Gamma_eq_integral Real.Gamma_eq_integral

theorem Gamma_add_one {s : ℝ} (hs : s ≠ 0) : Gamma (s + 1) = s * Gamma s := by
  simp_rw [Gamma]
  -- ⊢ (Complex.Gamma ↑(s + 1)).re = s * (Complex.Gamma ↑s).re
  rw [Complex.ofReal_add, Complex.ofReal_one, Complex.Gamma_add_one, Complex.ofReal_mul_re]
  -- ⊢ ↑s ≠ 0
  rwa [Complex.ofReal_ne_zero]
  -- 🎉 no goals
#align real.Gamma_add_one Real.Gamma_add_one

theorem Gamma_one : Gamma 1 = 1 := by
  rw [Gamma, Complex.ofReal_one, Complex.Gamma_one, Complex.one_re]
  -- 🎉 no goals
#align real.Gamma_one Real.Gamma_one

theorem _root_.Complex.Gamma_ofReal (s : ℝ) : Complex.Gamma (s : ℂ) = Gamma s := by
  rw [Gamma, eq_comm, ← Complex.conj_eq_iff_re, ← Complex.Gamma_conj, Complex.conj_ofReal]
  -- 🎉 no goals
#align complex.Gamma_of_real Complex.Gamma_ofReal

theorem Gamma_nat_eq_factorial (n : ℕ) : Gamma (n + 1) = n ! := by
  rw [Gamma, Complex.ofReal_add, Complex.ofReal_nat_cast, Complex.ofReal_one,
    Complex.Gamma_nat_eq_factorial, ← Complex.ofReal_nat_cast, Complex.ofReal_re]
#align real.Gamma_nat_eq_factorial Real.Gamma_nat_eq_factorial

/-- At `0` the Gamma function is undefined; by convention we assign it the value `0`. -/
theorem Gamma_zero : Gamma 0 = 0 := by
  simpa only [← Complex.ofReal_zero, Complex.Gamma_ofReal, Complex.ofReal_inj] using
    Complex.Gamma_zero
#align real.Gamma_zero Real.Gamma_zero

/-- At `-n` for `n ∈ ℕ`, the Gamma function is undefined; by convention we assign it the value `0`.
-/
theorem Gamma_neg_nat_eq_zero (n : ℕ) : Gamma (-n) = 0 := by
  simpa only [← Complex.ofReal_nat_cast, ← Complex.ofReal_neg, Complex.Gamma_ofReal,
    Complex.ofReal_eq_zero] using Complex.Gamma_neg_nat_eq_zero n
#align real.Gamma_neg_nat_eq_zero Real.Gamma_neg_nat_eq_zero

theorem Gamma_pos_of_pos {s : ℝ} (hs : 0 < s) : 0 < Gamma s := by
  rw [Gamma_eq_integral hs]
  -- ⊢ 0 < ∫ (x : ℝ) in Ioi 0, exp (-x) * x ^ (s - 1)
  have : (Function.support fun x : ℝ => exp (-x) * x ^ (s - 1)) ∩ Ioi 0 = Ioi 0 := by
    rw [inter_eq_right_iff_subset]
    intro x hx
    rw [Function.mem_support]
    exact mul_ne_zero (exp_pos _).ne' (rpow_pos_of_pos hx _).ne'
  rw [set_integral_pos_iff_support_of_nonneg_ae]
  · rw [this, volume_Ioi, ← ENNReal.ofReal_zero]
    -- ⊢ ENNReal.ofReal 0 < ⊤
    exact ENNReal.ofReal_lt_top
    -- 🎉 no goals
  · refine' eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) _
    -- ⊢ ∀ (x : ℝ), x ∈ Ioi 0 → OfNat.ofNat 0 x ≤ (fun x => exp (-x) * x ^ (s - 1)) x
    exact fun x hx => (mul_pos (exp_pos _) (rpow_pos_of_pos hx _)).le
    -- 🎉 no goals
  · exact GammaIntegral_convergent hs
    -- 🎉 no goals
#align real.Gamma_pos_of_pos Real.Gamma_pos_of_pos

/-- The Gamma function does not vanish on `ℝ` (except at non-positive integers, where the function
is mathematically undefined and we set it to `0` by convention). -/
theorem Gamma_ne_zero {s : ℝ} (hs : ∀ m : ℕ, s ≠ -m) : Gamma s ≠ 0 := by
  suffices ∀ {n : ℕ}, -(n : ℝ) < s → Gamma s ≠ 0 by
    apply this
    swap; exact ⌊-s⌋₊ + 1
    rw [neg_lt, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  intro n
  -- ⊢ -↑n < s → Gamma s ≠ 0
  induction' n with _ n_ih generalizing s
  -- ⊢ -↑Nat.zero < s → Gamma s ≠ 0
  · intro hs
    -- ⊢ Gamma s ≠ 0
    refine' (Gamma_pos_of_pos _).ne'
    -- ⊢ 0 < s
    rwa [Nat.cast_zero, neg_zero] at hs
    -- 🎉 no goals
  · intro hs'
    -- ⊢ Gamma s ≠ 0
    have : Gamma (s + 1) ≠ 0 := by
      apply n_ih
      · intro m
        specialize hs (1 + m)
        contrapose! hs
        rw [← eq_sub_iff_add_eq] at hs
        rw [hs]
        push_cast
        ring
      · rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, neg_add] at hs'
        linarith
    rw [Gamma_add_one, mul_ne_zero_iff] at this
    -- ⊢ Gamma s ≠ 0
    · exact this.2
      -- 🎉 no goals
    · simpa using hs 0
      -- 🎉 no goals
#align real.Gamma_ne_zero Real.Gamma_ne_zero

theorem Gamma_eq_zero_iff (s : ℝ) : Gamma s = 0 ↔ ∃ m : ℕ, s = -m :=
  ⟨by contrapose!; exact Gamma_ne_zero, by rintro ⟨m, rfl⟩; exact Gamma_neg_nat_eq_zero m⟩
      -- ⊢ (∀ (m : ℕ), s ≠ -↑m) → Gamma s ≠ 0
                   -- 🎉 no goals
                                           -- ⊢ Gamma (-↑m) = 0
                                                            -- 🎉 no goals
#align real.Gamma_eq_zero_iff Real.Gamma_eq_zero_iff

theorem differentiableAt_Gamma {s : ℝ} (hs : ∀ m : ℕ, s ≠ -m) : DifferentiableAt ℝ Gamma s := by
  refine' (Complex.differentiableAt_Gamma _ _).hasDerivAt.real_of_complex.differentiableAt
  -- ⊢ ∀ (m : ℕ), ↑s ≠ -↑m
  simp_rw [← Complex.ofReal_nat_cast, ← Complex.ofReal_neg, Ne.def, Complex.ofReal_inj]
  -- ⊢ ∀ (m : ℕ), ¬s = -↑m
  exact hs
  -- 🎉 no goals
#align real.differentiable_at_Gamma Real.differentiableAt_Gamma

end Real
