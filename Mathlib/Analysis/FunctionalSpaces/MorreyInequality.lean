/-
Copyright (c) 2026 Octavian Halmaghi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Octavian Halmaghi
-/
module

public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Morrey's inequality

This file proves **Morrey's inequality**, the supercritical companion of the
Gagliardo–Nirenberg–Sobolev inequality in
`Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`.

That file bounds the `Lᵍ` norm of a compactly supported `C¹` function by the `Lᵖ` norm of
its derivative under the hypothesis `p < finrank ℝ E`. Morrey's inequality is the
complementary statement for `finrank ℝ E < p`: the function is then bounded, indeed Hölder
continuous of exponent `1 - n / p`, with the Hölder seminorm controlled by the same `Lᵖ`
norm of the derivative.

Together the two files cover the whole range of exponents apart from the critical case
`p = finrank ℝ E`.

## Main results

* `MeasureTheory.enorm_sub_le_morreyConst_mul_rpow_mul_eLpNorm_fderiv`: the Hölder estimate
  `‖u x - u z‖ₑ ≤ C * ‖x - z‖ₑ ^ (1 - n / p) * eLpNorm (fderiv ℝ u) p μ`.
* `MeasureTheory.eLpNorm_top_le_eLpNorm_fderiv`: the resulting bound on the essential
  supremum, for a function supported in a bounded set.

Two lemmas of independent interest are proved on the way:

* `MeasureTheory.setLIntegral_ball_rpow_neg`: the exact value of the integral of the Riesz
  kernel `y ↦ ‖y - x‖ ^ (-a)` over a ball, for `a < n`.
* `MeasureTheory.lintegral_ball_enorm_sub_le_lintegral_riesz`: the mean oscillation of a `C¹`
  function on a ball is bounded by the Riesz potential of its derivative.

## Proof outline

The classical route, in three steps. The analytic tool underlying the first two is the
generalized polar coordinate change of
`Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`, which represents an additive Haar
measure on an `n`-dimensional normed space as the product of the sphere measure
`MeasureTheory.Measure.toSphere` and Lebesgue measure on `(0, ∞)` taken with density
`r ^ (n - 1)` (`MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd`).

Its general `lintegral` form, `MeasureTheory.lintegral_addHaar_eq_lintegral_toSphere_lintegral_Ioi`,
and the version localised to a ball,
`MeasureTheory.setLIntegral_ball_eq_lintegral_toSphere_lintegral_Ioo`, are the two tools used
below.

1. `MeasureTheory.setLIntegral_ball_rpow_neg`: in polar coordinates the Riesz kernel
   `y ↦ ‖y - x‖ ^ (-a)` becomes `ρ ^ (n - 1 - a)`, so its integral over `ball x r` is
   `n / (n - a) * μ (ball 0 1) * r ^ (n - a)`, finite as soon as `a < n`. Applied with
   `a = (n - 1) * q`, where `q` is the conjugate exponent of `p`, the condition `a < n` is
   exactly the hypothesis `n < p`. **This is where supercriticality enters**, and it is the
   only place it is used.

2. `MeasureTheory.lintegral_ball_enorm_sub_le_lintegral_riesz`: for `u` of class `C¹` and a
   ball `B = ball x r`, averaging the fundamental theorem of calculus along the rays out of
   `x` gives
   `∫⁻ y in B, ‖u y - u x‖ₑ ∂μ ≤ r ^ n / n * ∫⁻ y in B, ‖fderiv ℝ u y‖ₑ / ‖y - x‖ₑ ^ (n-1) ∂μ`.
   The right-hand side is a Riesz potential of the derivative. The integrand here is not
   radial, so this step uses the polar decomposition itself rather than its radial corollary:
   in polar coordinates the density `ρ ^ (n - 1)` cancels the Riesz kernel exactly, and what
   is left on each ray is the fundamental theorem of calculus.

3. Hölder's inequality against that kernel, with the exponents `p` and `q`, turns step 2 into
   `∫⁻ y in B, ‖u y - u x‖ₑ ∂μ ≤ r ^ n / n * ‖fderiv ℝ u‖_{Lᵖ} * (kernel integral) ^ (1 / q)`,
   and the kernel integral is the constant of step 1. Averaging that over the two balls of
   radius `d = ‖x - z‖ ` around `x` and around `z`, and comparing with the average over
   `ball ((x + z) / 2) (d / 2)`, which is contained in both and has measure at least
   `2 ^ (-n)` times theirs, gives the Hölder estimate. Finally, for a function supported in a
   bounded set `s`, walking out of `s` along a ray from `x` produces a point `z` at distance
   `Metric.diam s` at which `u` vanishes, and that turns the Hölder estimate into the bound
   on the essential supremum.

## References

* [L. C. Evans, *Partial Differential Equations*][evans2010], §5.6.2
* [E. H. Lieb and M. Loss, *Analysis*][liebLoss2001], §8.4
-/

@[expose] public section

open scoped ENNReal NNReal
open Set Function MeasureTheory Measure Filter Module Metric

noncomputable section

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]


section RieszKernel

/-- The value of the integral in `lintegral_ball_rpow_neg_lt_top`, as a constant depending
only on `E`, `μ` and the exponents. Keeping it named, rather than existential, is what lets
the constants in the main statements below be written down explicitly. -/
def rieszKernelConst (a : ℝ) (r : ℝ) : ℝ≥0 :=
  ((finrank ℝ E : ℝ) / (finrank ℝ E - a)).toNNReal *
    (μ (ball (0 : E) 1)).toNNReal * r.toNNReal ^ (finrank ℝ E - a)

/-- **The value of the Riesz kernel integral on a ball.**

The quantitative companion of `lintegral_ball_rpow_neg_lt_top`: when `a < n` the integral of
`y ↦ ‖y - x‖ ^ (-a)` over `ball x r` is exactly `rieszKernelConst μ a r`, that is
`n / (n - a) * μ (ball 0 1) * r ^ (n - a)`.

In polar coordinates the integrand becomes `ρ ^ (n - 1 - a)`, whose integral over `(0, r)` is
`r ^ (n - a) / (n - a)`, and the sphere contributes the factor
`μ.toSphere univ = n * μ (ball 0 1)`. -/
theorem setLIntegral_ball_rpow_neg [Nontrivial E] (x : E) {r a : ℝ} (hr : 0 < r)
    (han : a < finrank ℝ E) :
    (∫⁻ y in ball x r, ‖y - x‖ₑ ^ (-a) ∂μ) = rieszKernelConst μ a r := by
  have hn : 1 ≤ finrank ℝ E := Module.finrank_pos
  have hna : (0 : ℝ) < (finrank ℝ E : ℝ) - a := by linarith
  have hofReal : ∀ t : ℝ, ((t.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal t := fun _ ↦ rfl
  have hcast : ((finrank ℝ E - 1 : ℕ) : ℝ) = (finrank ℝ E : ℝ) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  have hm : Measurable fun y : E ↦ ‖y - x‖ₑ ^ (-a) :=
    (((continuous_id.sub continuous_const).enorm).measurable).pow_const _
  -- the radial integral
  have hrad : (∫⁻ ρ in Ioo (0 : ℝ) r, ENNReal.ofReal (ρ ^ ((finrank ℝ E : ℝ) - 1 - a)))
      = ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) - a) / ((finrank ℝ E : ℝ) - a)) := by
    have hint : IntegrableOn (fun ρ : ℝ ↦ ρ ^ ((finrank ℝ E : ℝ) - 1 - a)) (Ioo 0 r) volume :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hr).2 (by linarith)
    have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) r)]
        fun ρ : ℝ ↦ ρ ^ ((finrank ℝ E : ℝ) - 1 - a) :=
      ae_restrict_of_forall_mem measurableSet_Ioo fun ρ hρ ↦ Real.rpow_nonneg hρ.1.le _
    have he : (finrank ℝ E : ℝ) - 1 - a + 1 = (finrank ℝ E : ℝ) - a := by ring
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hr.le,
      integral_rpow (Or.inl (by linarith : (-1 : ℝ) < (finrank ℝ E : ℝ) - 1 - a)), he,
      Real.zero_rpow hna.ne', sub_zero]
  -- polar coordinates
  rw [setLIntegral_ball_eq_lintegral_toSphere_lintegral_Ioo μ x r hm]
  have hinner : ∀ ω : sphere (0 : E) 1,
      (∫⁻ ρ in Ioo (0 : ℝ) r, ENNReal.ofReal (ρ ^ (finrank ℝ E - 1)) *
          ‖x + ρ • (ω : E) - x‖ₑ ^ (-a))
        = ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) - a) / ((finrank ℝ E : ℝ) - a)) := by
    intro ω
    have hω : ‖(ω : E)‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
    rw [← hrad]
    refine setLIntegral_congr_fun measurableSet_Ioo fun ρ hρ ↦ ?_
    have hρ0 : (0 : ℝ) < ρ := hρ.1
    have h1 : x + ρ • (ω : E) - x = ρ • (ω : E) := by abel
    have h2 : ‖ρ • (ω : E)‖ₑ = ENNReal.ofReal ρ := by
      rw [← ofReal_norm, norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hρ0]
    have he2 : ((finrank ℝ E : ℝ) - 1) + -a = (finrank ℝ E : ℝ) - 1 - a := by ring
    rw [h1, h2, ENNReal.ofReal_rpow_of_pos hρ0, ← ENNReal.ofReal_mul (pow_nonneg hρ0.le _),
      ← Real.rpow_natCast ρ (finrank ℝ E - 1), ← Real.rpow_add hρ0, hcast, he2]
  rw [lintegral_congr hinner, lintegral_const, Measure.toSphere_apply_univ]
  -- identify the constant
  have hb : ((μ (ball (0 : E) 1)).toNNReal : ℝ≥0∞) = μ (ball (0 : E) 1) :=
    ENNReal.coe_toNNReal measure_ball_lt_top.ne
  have key : ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) - a) / ((finrank ℝ E : ℝ) - a)) *
        ENNReal.ofReal (finrank ℝ E : ℝ)
      = ENNReal.ofReal ((finrank ℝ E : ℝ) / ((finrank ℝ E : ℝ) - a)) *
        ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) - a)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [rieszKernelConst, ENNReal.coe_mul, ENNReal.coe_mul, hb,
    ENNReal.coe_rpow_of_nonneg _ hna.le]
  simp only [hofReal]
  rw [ENNReal.ofReal_rpow_of_pos hr, ← ENNReal.ofReal_natCast (finrank ℝ E)]
  calc ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) - a) / ((finrank ℝ E : ℝ) - a)) *
        (ENNReal.ofReal (finrank ℝ E : ℝ) * μ (ball (0 : E) 1))
      = (ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) - a) / ((finrank ℝ E : ℝ) - a)) *
          ENNReal.ofReal (finrank ℝ E : ℝ)) * μ (ball (0 : E) 1) := by ring
    _ = (ENNReal.ofReal ((finrank ℝ E : ℝ) / ((finrank ℝ E : ℝ) - a)) *
          ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) - a))) * μ (ball (0 : E) 1) := by rw [key]
    _ = ENNReal.ofReal ((finrank ℝ E : ℝ) / ((finrank ℝ E : ℝ) - a)) * μ (ball (0 : E) 1) *
          ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) - a)) := by ring

/-- **Integrability of the Riesz kernel on a ball.**

The kernel `y ↦ ‖y - x‖ ^ (-a)` is integrable on `ball x r` exactly when `a < n`. In Morrey's
inequality it is applied with `a = (n - 1) * q`, where `q` is the conjugate exponent of `p`;
the condition `a < n` is then equivalent to `n < p`, so this lemma is where the supercritical
hypothesis is consumed.

This is the qualitative form of `setLIntegral_ball_rpow_neg`, which computes the integral. -/
theorem lintegral_ball_rpow_neg_lt_top [Nontrivial E] (x : E) {r a : ℝ} (hr : 0 < r)
    (han : a < finrank ℝ E) :
    (∫⁻ y in ball x r, ‖y - x‖ₑ ^ (-a) ∂μ) < ⊤ := by
  rw [setLIntegral_ball_rpow_neg μ x hr han]
  exact ENNReal.coe_lt_top

end RieszKernel

section Potential

variable (E) in
/-- The constant `r ^ n / n` in the Riesz potential estimate
`lintegral_ball_enorm_sub_le_lintegral_riesz`. It is the value of `∫_0^r ρ ^ (n - 1) dρ`,
which is what integrating the fundamental theorem of calculus along the rays out of the
centre of the ball produces.

Unlike `rieszKernelConst` it does not involve `μ`, and it cannot: both sides of that estimate
are homogeneous of degree one in `μ`, so the constant relating them must be homogeneous of
degree zero. -/
def rieszPotentialConst (r : ℝ) : ℝ≥0 :=
  (r ^ finrank ℝ E / (finrank ℝ E : ℝ)).toNNReal

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Along a ray with unit direction `ω`, the increment of a continuously differentiable
function is bounded by the integral of the enorm of its derivative. This is the fundamental
theorem of calculus in the form needed for Morrey's inequality.

The target space is not assumed complete, so the Bochner integral behind the fundamental
theorem of calculus is taken in `UniformSpace.Completion F`, into which `F` embeds
isometrically. -/
theorem enorm_sub_le_lintegral_Ioc_enorm_fderiv
    {u : E → F} (hu : ContDiff ℝ 1 u) (x : E) {ω : E} (hω : ‖ω‖ = 1) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖u (x + ρ • ω) - u x‖ₑ ≤ ∫⁻ t in Ioc (0 : ℝ) ρ, ‖fderiv ℝ u (x + t • ω)‖ₑ := by
  -- the derivative of `u` along the ray through `x` in the direction `ω`
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ ↦ u (x + s • ω)) (fderiv ℝ u (x + t • ω) ω) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ ↦ x + s • ω) ω t := by
      simpa using ((hasDerivAt_id t).smul_const ω).const_add x
    exact HasFDerivAt.comp_hasDerivAt t
      ((hu.differentiable one_ne_zero) (x + t • ω)).hasFDerivAt h1
  set I : F →L[ℝ] UniformSpace.Completion F := UniformSpace.Completion.toComplL with hI
  have hIe : ∀ y : F, ‖I y‖ₑ = ‖y‖ₑ := by
    intro y
    rw [hI, UniformSpace.Completion.coe_toComplL, UniformSpace.Completion.enorm_coe]
  have hdI : ∀ t : ℝ, HasDerivAt (fun s : ℝ ↦ I (u (x + s • ω)))
      (I (fderiv ℝ u (x + t • ω) ω)) t := fun t =>
    HasFDerivAt.comp_hasDerivAt t I.hasFDerivAt (hd t)
  have hcontI : Continuous fun t : ℝ ↦ I (fderiv ℝ u (x + t • ω) ω) := by
    have h0 : Continuous fun t : ℝ ↦ fderiv ℝ u (x + t • ω) :=
      (hu.continuous_fderiv one_ne_zero).comp (by fun_prop)
    exact I.continuous.comp (h0.clm_apply continuous_const)
  have hFTC : I (u (x + ρ • ω)) - I (u x)
      = ∫ t in (0 : ℝ)..ρ, I (fderiv ℝ u (x + t • ω) ω) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ ↦ I (u (x + s • ω)))
      (f' := fun t : ℝ ↦ I (fderiv ℝ u (x + t • ω) ω)) (fun t _ ↦ hdI t)
      (hcontI.intervalIntegrable 0 ρ)
    rw [h]
    simp
  calc ‖u (x + ρ • ω) - u x‖ₑ = ‖I (u (x + ρ • ω)) - I (u x)‖ₑ := by
        rw [← map_sub I, hIe]
    _ = ‖∫ t in Ioc (0 : ℝ) ρ, I (fderiv ℝ u (x + t • ω) ω)‖ₑ := by
        rw [hFTC, intervalIntegral.integral_of_le hρ]
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) ρ, ‖I (fderiv ℝ u (x + t • ω) ω)‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) ρ, ‖fderiv ℝ u (x + t • ω)‖ₑ := by
      refine lintegral_mono fun t ↦ ?_
      rw [hIe]
      refine (ContinuousLinearMap.le_opENorm _ _).trans_eq ?_
      rw [← ofReal_norm ω, hω, ENNReal.ofReal_one, mul_one]

/-- **The Riesz potential estimate.**

For `u` of class `C¹`, the mean oscillation of `u` on a ball is controlled by the Riesz
potential of its derivative:
`∫⁻ y in ball x r, ‖u y - u x‖ₑ ∂μ ≤ (r ^ n / n) * (Riesz potential of the derivative)`.

The proof reads both sides in polar coordinates about `x`, using
`setLIntegral_ball_eq_lintegral_toSphere_lintegral_Ioo`. On the right the radial density
`ρ ^ (n - 1)` cancels the Riesz kernel exactly, leaving
`∫_0^r ‖fderiv ℝ u (x + t ω)‖ dt` on each ray; on the left the fundamental theorem of
calculus (`enorm_sub_le_lintegral_Ioc_enorm_fderiv`) bounds the integrand on each ray by that
same quantity, and integrating the density `ρ ^ (n - 1)` over `(0, r)` produces the factor
`rieszPotentialConst E r = r ^ n / n`. -/
theorem lintegral_ball_enorm_sub_le_lintegral_riesz [Nontrivial E]
    {u : E → F} (hu : ContDiff ℝ 1 u) (x : E) {r : ℝ} (hr : 0 < r) :
    (∫⁻ y in ball x r, ‖u y - u x‖ₑ ∂μ) ≤
      rieszPotentialConst E r *
        ∫⁻ y in ball x r, ‖fderiv ℝ u y‖ₑ / ‖y - x‖ₑ ^ ((finrank ℝ E : ℝ) - 1) ∂μ := by
  have hn : 1 ≤ finrank ℝ E := Module.finrank_pos
  have hn0 : finrank ℝ E ≠ 0 := Nat.one_le_iff_ne_zero.1 hn
  have hofReal : ∀ t : ℝ, ((t.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal t := fun _ ↦ rfl
  have hcast : ((finrank ℝ E : ℝ) - 1) = ((finrank ℝ E - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  -- measurability of the two integrands
  have hLm : Measurable fun y : E ↦ ‖u y - u x‖ₑ :=
    ((hu.continuous.sub continuous_const).enorm).measurable
  have hDu : Measurable fun y : E ↦ ‖fderiv ℝ u y‖ₑ :=
    ((hu.continuous_fderiv one_ne_zero).enorm).measurable
  have hRm : Measurable fun y : E =>
      ‖fderiv ℝ u y‖ₑ / ‖y - x‖ₑ ^ ((finrank ℝ E : ℝ) - 1) := by
    simp only [div_eq_mul_inv]
    exact hDu.mul ((((continuous_id.sub continuous_const).enorm).measurable).pow_const _).inv
  -- the radial density integrates to `r ^ n / n`
  have hpow : (∫⁻ ρ in Ioo (0 : ℝ) r, ENNReal.ofReal (ρ ^ (finrank ℝ E - 1)))
      = (rieszPotentialConst E r : ℝ≥0∞) := by
    have hc : Continuous fun ρ : ℝ ↦ ρ ^ (finrank ℝ E - 1) := by fun_prop
    have hint : IntegrableOn (fun ρ : ℝ ↦ ρ ^ (finrank ℝ E - 1)) (Ioo 0 r) volume :=
      (hc.integrableOn_Icc (a := 0) (b := r)).mono_set Ioo_subset_Icc_self
    have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) r)] fun ρ : ℝ ↦ ρ ^ (finrank ℝ E - 1) :=
      ae_restrict_of_forall_mem measurableSet_Ioo fun ρ hρ ↦ pow_nonneg hρ.1.le _
    have hval : (∫ ρ in Ioo (0 : ℝ) r, ρ ^ (finrank ℝ E - 1))
        = r ^ finrank ℝ E / (finrank ℝ E : ℝ) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le, integral_pow,
        Nat.sub_add_cancel hn, zero_pow hn0, sub_zero, Nat.cast_sub hn]
      norm_num
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hval, rieszPotentialConst, hofReal]
  -- polar form of the right-hand side: the radial density cancels the Riesz kernel
  have hRHS : (∫⁻ y in ball x r, ‖fderiv ℝ u y‖ₑ / ‖y - x‖ₑ ^ ((finrank ℝ E : ℝ) - 1) ∂μ)
      = ∫⁻ ω : sphere (0 : E) 1,
          (∫⁻ ρ in Ioo (0 : ℝ) r, ‖fderiv ℝ u (x + ρ • (ω : E))‖ₑ) ∂μ.toSphere := by
    rw [setLIntegral_ball_eq_lintegral_toSphere_lintegral_Ioo μ x r hRm]
    refine lintegral_congr fun ω ↦ ?_
    refine setLIntegral_congr_fun measurableSet_Ioo fun ρ hρ ↦ ?_
    have hρ0 : (0 : ℝ) < ρ := hρ.1
    have hω : ‖(ω : E)‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
    have h1 : x + ρ • (ω : E) - x = ρ • (ω : E) := by abel
    have h2 : ‖ρ • (ω : E)‖ₑ = ENNReal.ofReal ρ := by
      rw [← ofReal_norm, norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hρ0]
    have h4 : (ENNReal.ofReal ρ) ^ ((finrank ℝ E : ℝ) - 1)
        = ENNReal.ofReal (ρ ^ (finrank ℝ E - 1)) := by
      rw [ENNReal.ofReal_rpow_of_pos hρ0, hcast, Real.rpow_natCast]
    rw [h1, h2, h4]
    exact ENNReal.mul_div_cancel (ENNReal.ofReal_pos.2 (pow_pos hρ0 _)).ne'
      ENNReal.ofReal_ne_top
  -- compare the two ray integrals
  rw [setLIntegral_ball_eq_lintegral_toSphere_lintegral_Ioo μ x r hLm, hRHS,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_mono fun ω ↦ ?_
  have hω : ‖(ω : E)‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
  have hstep : ∀ ρ ∈ Ioo (0 : ℝ) r,
      ‖u (x + ρ • (ω : E)) - u x‖ₑ
        ≤ ∫⁻ t in Ioo (0 : ℝ) r, ‖fderiv ℝ u (x + t • (ω : E))‖ₑ := fun ρ hρ =>
    (enorm_sub_le_lintegral_Ioc_enorm_fderiv hu x hω hρ.1.le).trans
      (lintegral_mono_set fun t ht ↦ ⟨ht.1, lt_of_le_of_lt ht.2 hρ.2⟩)
  calc (∫⁻ ρ in Ioo (0 : ℝ) r,
          ENNReal.ofReal (ρ ^ (finrank ℝ E - 1)) * ‖u (x + ρ • (ω : E)) - u x‖ₑ)
      ≤ ∫⁻ _ρ in Ioo (0 : ℝ) r, ENNReal.ofReal (_ρ ^ (finrank ℝ E - 1)) *
          ∫⁻ t in Ioo (0 : ℝ) r, ‖fderiv ℝ u (x + t • (ω : E))‖ₑ :=
        setLIntegral_mono' measurableSet_Ioo fun ρ hρ ↦ mul_le_mul_right (hstep ρ hρ) _
    _ = (∫⁻ ρ in Ioo (0 : ℝ) r, ENNReal.ofReal (ρ ^ (finrank ℝ E - 1))) *
          ∫⁻ t in Ioo (0 : ℝ) r, ‖fderiv ℝ u (x + t • (ω : E))‖ₑ :=
        lintegral_mul_const'' _ (by fun_prop)
    _ = _ := by rw [hpow]

end Potential

section Morrey

variable (E) in
/-- The constant in the Hölder estimate of Morrey's inequality. It depends only on `E`, `μ`
and `p`.

Its three factors are the three steps of the proof: `2 ^ (n + 1) / n` collects the constant
`r ^ n / n` of the Riesz potential estimate and the two-fold comparison of the averages over
`ball x ‖x - z‖` and `ball z ‖x - z‖` with the average over their intersection, which
contains a ball of half the radius; `rieszKernelConst μ ((n - 1) * q) 1 ^ (1 / q)` is the
kernel factor coming out of Hölder's inequality, for `q` the conjugate exponent of `p`; and
`(μ (ball 0 1)).toNNReal⁻¹` normalises the averages. Note the resulting homogeneity in `μ`:
the constant is homogeneous of degree `1 / q - 1 = -1 / p`, which is what makes the estimate
itself invariant under rescaling `μ`, since `eLpNorm · p` is homogeneous of degree `1 / p`.

This is exactly the constant the proof produces: the identity
`2 * rieszPotentialConst E d * rieszKernelConst μ ((n - 1) * q) d ^ (1 / q)
  = morreyConst E μ p * d ^ (1 - n / p) * μ (ball ((x + z) / 2) (d / 2))`,
for `d = ‖x - z‖`, is where it is pinned down. -/
def morreyConst (p : ℝ≥0) : ℝ≥0 :=
  let n : ℝ := finrank ℝ E
  let q : ℝ := (1 - 1 / p)⁻¹          -- the conjugate exponent of `p`
  ((2 : ℝ) ^ (finrank ℝ E + 1) / n).toNNReal *
    rieszKernelConst μ ((n - 1) * q) 1 ^ (1 / q) * (μ (ball (0 : E) 1)).toNNReal⁻¹

/-- **Morrey's inequality, Hölder form.**

Let `u` be a continuously differentiable function on a normed space `E` of finite dimension
`n`, equipped with a Haar measure, and let `finrank ℝ E < p`. Then `u` is Hölder continuous
of exponent `1 - n / p`, with seminorm bounded by the `Lᵖ` norm of its derivative.

This is the supercritical counterpart of `MeasureTheory.eLpNorm_le_eLpNorm_fderiv`, whose
hypothesis is `p < finrank ℝ E`.

The proof compares the averages of `u` over `ball x d` and `ball z d`, where `d = ‖x - z‖`,
with the average over `ball ((x + z) / 2) (d / 2)`, which is contained in both. On each of the
two balls the mean oscillation is controlled by `lintegral_ball_enorm_sub_le_lintegral_riesz`,
and Hölder's inequality against the Riesz kernel — whose integral is evaluated by
`setLIntegral_ball_rpow_neg`, the finiteness of which is exactly `finrank ℝ E < p` — turns
that into the `Lᵖ` norm of the derivative.

No support hypothesis is needed for this estimate. -/
theorem enorm_sub_le_morreyConst_mul_rpow_mul_eLpNorm_fderiv [Nontrivial E]
    {u : E → F} (hu : ContDiff ℝ 1 u) {p : ℝ≥0} (hp : (finrank ℝ E : ℝ≥0) < p) (x z : E) :
    ‖u x - u z‖ₑ ≤
      morreyConst E μ p * ‖x - z‖ₑ ^ (1 - (finrank ℝ E : ℝ) / p) *
        eLpNorm (fderiv ℝ u) p μ := by
  rcases eq_or_ne x z with rfl | hxz
  · simp
  -- numerical preliminaries
  have hn : 1 ≤ finrank ℝ E := Module.finrank_pos
  have hN1 : (1 : ℝ) ≤ (finrank ℝ E : ℝ) := by exact_mod_cast hn
  have hNP : (finrank ℝ E : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hP1 : (1 : ℝ) < (p : ℝ) := lt_of_le_of_lt hN1 hNP
  have hP0 : (0 : ℝ) < (p : ℝ) := lt_trans one_pos hP1
  have hPne : (p : ℝ) ≠ 0 := hP0.ne'
  have hP1' : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hP1ne : (p : ℝ) - 1 ≠ 0 := hP1'.ne'
  have hp0 : (0 : ℝ≥0) < p := by exact_mod_cast hP0
  have hd : (0 : ℝ) < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hxz)
  have hofReal : ∀ t : ℝ, ((t.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal t := fun _ ↦ rfl
  have hb0 : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hbt : μ (ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hb : ((μ (ball (0 : E) 1)).toNNReal : ℝ≥0∞) = μ (ball (0 : E) 1) := ENNReal.coe_toNNReal hbt
  have hbb : (μ (ball (0 : E) 1))⁻¹ * μ (ball (0 : E) 1) = 1 := ENNReal.inv_mul_cancel hb0 hbt
  -- the conjugate exponent `q` of `p`
  have hq : ((1 : ℝ) - 1 / (p : ℝ))⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by
    rw [show (1 : ℝ) - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) by field_simp, inv_div]
  have hq0 : (0 : ℝ) < ((1 : ℝ) - 1 / (p : ℝ))⁻¹ := by rw [hq]; exact div_pos hP0 hP1'
  have hqinv0 : (0 : ℝ) ≤ ((1 : ℝ) / ((1 : ℝ) - 1 / (p : ℝ))⁻¹) :=
    le_of_lt (by rw [one_div]; exact inv_pos.2 hq0)
  have hpq : Real.HolderConjugate (p : ℝ) ((1 : ℝ) - 1 / (p : ℝ))⁻¹ := by
    refine ⟨?_, hP0, hq0⟩
    rw [inv_inv, one_div, inv_one]
    ring
  have hNaval : (finrank ℝ E : ℝ) - ((finrank ℝ E : ℝ) - 1) * ((1 : ℝ) - 1 / (p : ℝ))⁻¹
      = ((p : ℝ) - (finrank ℝ E : ℝ)) / ((p : ℝ) - 1) := by
    rw [hq]
    field_simp
    ring
  have hNa : (0 : ℝ) <
      (finrank ℝ E : ℝ) - ((finrank ℝ E : ℝ) - 1) * ((1 : ℝ) - 1 / (p : ℝ))⁻¹ := by
    rw [hNaval]
    exact div_pos (by linarith) hP1'
  have haN : ((finrank ℝ E : ℝ) - 1) * ((1 : ℝ) - 1 / (p : ℝ))⁻¹ < (finrank ℝ E : ℝ) := by
    linarith
  have hexp : ((finrank ℝ E : ℝ) - ((finrank ℝ E : ℝ) - 1) * ((1 : ℝ) - 1 / (p : ℝ))⁻¹) *
      ((1 : ℝ) / ((1 : ℝ) - 1 / (p : ℝ))⁻¹) = 1 - (finrank ℝ E : ℝ) / (p : ℝ) := by
    rw [hNaval, one_div, inv_inv]
    field_simp
  -- abbreviations: `q` is the conjugate exponent of `p`, `a` the exponent of the Riesz kernel
  set q : ℝ := ((1 : ℝ) - 1 / (p : ℝ))⁻¹ with hqdef
  set a : ℝ := ((finrank ℝ E : ℝ) - 1) * q with hadef
  -- the shape of the two constants
  have hKform : ∀ t : ℝ, ((rieszKernelConst μ a t : ℝ≥0) : ℝ≥0∞)
      = ENNReal.ofReal ((finrank ℝ E : ℝ) / ((finrank ℝ E : ℝ) - a)) * μ (ball (0 : E) 1) *
        (ENNReal.ofReal t) ^ ((finrank ℝ E : ℝ) - a) := by
    intro t
    rw [rieszKernelConst, ENNReal.coe_mul, ENNReal.coe_mul, hb,
      ENNReal.coe_rpow_of_nonneg _ hNa.le]
    simp only [hofReal]
  have hbn0 : (μ (ball (0 : E) 1)).toNNReal ≠ 0 := by
    simp [ENNReal.toNNReal_eq_zero_iff, hb0, hbt]
  have hmc : ((morreyConst E μ p : ℝ≥0) : ℝ≥0∞)
      = ENNReal.ofReal ((2 : ℝ) ^ (finrank ℝ E + 1) / (finrank ℝ E : ℝ)) *
        (ENNReal.ofReal ((finrank ℝ E : ℝ) / ((finrank ℝ E : ℝ) - a)) ^ ((1 : ℝ) / q) *
          μ (ball (0 : E) 1) ^ ((1 : ℝ) / q)) * (μ (ball (0 : E) 1))⁻¹ := by
    simp only [morreyConst]
    rw [← hqdef, ← hadef, ENNReal.coe_mul, ENNReal.coe_mul,
      ENNReal.coe_rpow_of_nonneg _ hqinv0, ENNReal.coe_inv hbn0, hb, hKform 1,
      ENNReal.ofReal_one, ENNReal.one_rpow, mul_one, ENNReal.mul_rpow_of_nonneg _ _ hqinv0]
    simp only [hofReal]
  -- the `Lᵖ` norm of the derivative as a Lebesgue integral
  have hDu : Measurable fun y : E ↦ ‖fderiv ℝ u y‖ₑ :=
    ((hu.continuous_fderiv one_ne_zero).enorm).measurable
  have heL : eLpNorm (fderiv ℝ u) p μ
      = (∫⁻ y, ‖fderiv ℝ u y‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.coe_ne_zero.2 hp0.ne')
      ENNReal.coe_ne_top (hu.continuous_fderiv one_ne_zero).aestronglyMeasurable,
      ENNReal.coe_toReal]
  -- the mean oscillation on a ball of radius `‖x - z‖`, by Hölder against the Riesz kernel
  have hosc : ∀ c : E, (∫⁻ y in ball c ‖x - z‖, ‖u y - u c‖ₑ ∂μ)
      ≤ ((rieszPotentialConst E ‖x - z‖ : ℝ≥0) : ℝ≥0∞) *
        (eLpNorm (fderiv ℝ u) p μ *
          ((rieszKernelConst μ a ‖x - z‖ : ℝ≥0) : ℝ≥0∞) ^ ((1 : ℝ) / q)) := by
    intro c
    refine (lintegral_ball_enorm_sub_le_lintegral_riesz μ hu c hd).trans (mul_le_mul_right ?_ _)
    have hg : Measurable fun y : E ↦ ‖y - c‖ₑ ^ (-((finrank ℝ E : ℝ) - 1)) :=
      (((continuous_id.sub continuous_const).enorm).measurable).pow_const _
    have hker : (∫⁻ y in ball c ‖x - z‖, (‖y - c‖ₑ ^ (-((finrank ℝ E : ℝ) - 1))) ^ q ∂μ)
        = ((rieszKernelConst μ a ‖x - z‖ : ℝ≥0) : ℝ≥0∞) := by
      rw [← setLIntegral_ball_rpow_neg μ c hd haN]
      refine setLIntegral_congr_fun measurableSet_ball fun y _ ↦ ?_
      rw [← ENNReal.rpow_mul]
      congr 1
      rw [hadef]
      ring
    calc (∫⁻ y in ball c ‖x - z‖, ‖fderiv ℝ u y‖ₑ / ‖y - c‖ₑ ^ ((finrank ℝ E : ℝ) - 1) ∂μ)
        = ∫⁻ y in ball c ‖x - z‖, ((fun w : E ↦ ‖fderiv ℝ u w‖ₑ) *
            fun w : E ↦ ‖w - c‖ₑ ^ (-((finrank ℝ E : ℝ) - 1))) y ∂μ := by
          refine lintegral_congr fun y ↦ ?_
          simp only [Pi.mul_apply]
          rw [ENNReal.rpow_neg, div_eq_mul_inv]
      _ ≤ (∫⁻ y in ball c ‖x - z‖, ‖fderiv ℝ u y‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) *
            (∫⁻ y in ball c ‖x - z‖, (‖y - c‖ₑ ^ (-((finrank ℝ E : ℝ) - 1))) ^ q ∂μ) ^
              ((1 : ℝ) / q) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq hDu.aemeasurable hg.aemeasurable
      _ ≤ eLpNorm (fderiv ℝ u) p μ *
            (∫⁻ y in ball c ‖x - z‖, (‖y - c‖ₑ ^ (-((finrank ℝ E : ℝ) - 1))) ^ q ∂μ) ^
              ((1 : ℝ) / q) := by
          refine mul_le_mul_left ?_ _
          rw [heL]
          exact ENNReal.rpow_le_rpow (setLIntegral_le_lintegral _ _) (by positivity)
      _ = eLpNorm (fderiv ℝ u) p μ *
            ((rieszKernelConst μ a ‖x - z‖ : ℝ≥0) : ℝ≥0∞) ^ ((1 : ℝ) / q) := by rw [hker]
  -- the ball about the midpoint, contained in both balls of radius `‖x - z‖`
  have hmx : ‖(2 : ℝ)⁻¹ • (x + z) - x‖ = ‖x - z‖ / 2 := by
    have h : (2 : ℝ)⁻¹ • (x + z) - x = (2 : ℝ)⁻¹ • (z - x) := by module
    rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹),
      norm_sub_rev z x]
    ring
  have hmz : ‖(2 : ℝ)⁻¹ • (x + z) - z‖ = ‖x - z‖ / 2 := by
    have h : (2 : ℝ)⁻¹ • (x + z) - z = (2 : ℝ)⁻¹ • (x - z) := by module
    rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
    ring
  have hVx : ball ((2 : ℝ)⁻¹ • (x + z)) (‖x - z‖ / 2) ⊆ ball x ‖x - z‖ := by
    intro y hy
    have h1 : dist y ((2 : ℝ)⁻¹ • (x + z)) < ‖x - z‖ / 2 := hy
    have h2 : dist ((2 : ℝ)⁻¹ • (x + z)) x = ‖x - z‖ / 2 := by rw [dist_eq_norm, hmx]
    have h3 := dist_triangle y ((2 : ℝ)⁻¹ • (x + z)) x
    simp only [mem_ball]
    linarith
  have hVz : ball ((2 : ℝ)⁻¹ • (x + z)) (‖x - z‖ / 2) ⊆ ball z ‖x - z‖ := by
    intro y hy
    have h1 : dist y ((2 : ℝ)⁻¹ • (x + z)) < ‖x - z‖ / 2 := hy
    have h2 : dist ((2 : ℝ)⁻¹ • (x + z)) z = ‖x - z‖ / 2 := by rw [dist_eq_norm, hmz]
    have h3 := dist_triangle y ((2 : ℝ)⁻¹ • (x + z)) z
    simp only [mem_ball]
    linarith
  have hV0 : μ (ball ((2 : ℝ)⁻¹ • (x + z)) (‖x - z‖ / 2)) ≠ 0 :=
    (measure_ball_pos μ _ (by positivity)).ne'
  have hVt : μ (ball ((2 : ℝ)⁻¹ • (x + z)) (‖x - z‖ / 2)) ≠ ⊤ := measure_ball_lt_top.ne
  -- the constant identity: this is where the value of `morreyConst` is pinned down
  have hconst : 2 * ((rieszPotentialConst E ‖x - z‖ : ℝ≥0) : ℝ≥0∞) *
        ((rieszKernelConst μ a ‖x - z‖ : ℝ≥0) : ℝ≥0∞) ^ ((1 : ℝ) / q)
      = ((morreyConst E μ p : ℝ≥0) : ℝ≥0∞) *
        (ENNReal.ofReal ‖x - z‖) ^ (1 - (finrank ℝ E : ℝ) / (p : ℝ)) *
        μ (ball ((2 : ℝ)⁻¹ • (x + z)) (‖x - z‖ / 2)) := by
    have hscal : (2 : ℝ≥0∞) * ENNReal.ofReal (‖x - z‖ ^ finrank ℝ E / (finrank ℝ E : ℝ))
        = ENNReal.ofReal ((2 : ℝ) ^ (finrank ℝ E + 1) / (finrank ℝ E : ℝ)) *
          ENNReal.ofReal ((‖x - z‖ / 2) ^ finrank ℝ E) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have hNne : (finrank ℝ E : ℝ) ≠ 0 := by linarith
      have h2n : ((2 : ℝ) ^ finrank ℝ E) ≠ 0 := by positivity
      rw [div_pow, pow_succ]
      field_simp
    rw [hKform ‖x - z‖, hmc, μ.addHaar_ball _ (by positivity : (0 : ℝ) ≤ ‖x - z‖ / 2),
      rieszPotentialConst]
    simp only [hofReal]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hqinv0, ENNReal.mul_rpow_of_nonneg _ _ hqinv0,
      ← ENNReal.rpow_mul, hexp]
    -- abbreviate the six factors that are now common to the two sides
    set A : ℝ≥0∞ := ENNReal.ofReal ((finrank ℝ E : ℝ) / ((finrank ℝ E : ℝ) - a)) ^
      ((1 : ℝ) / q) with hA
    set B : ℝ≥0∞ := μ (ball (0 : E) 1) ^ ((1 : ℝ) / q) with hB
    set D : ℝ≥0∞ := ENNReal.ofReal ‖x - z‖ ^ (1 - (finrank ℝ E : ℝ) / (p : ℝ)) with hD
    set C : ℝ≥0∞ := ENNReal.ofReal (‖x - z‖ ^ finrank ℝ E / (finrank ℝ E : ℝ)) with hC
    set G : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (finrank ℝ E + 1) / (finrank ℝ E : ℝ)) with hG
    set H : ℝ≥0∞ := ENNReal.ofReal ((‖x - z‖ / 2) ^ finrank ℝ E) with hH
    calc 2 * C * (A * B * D)
        = (2 * C) * (A * B * D) := by ring
      _ = (G * H) * (A * B * D) := by rw [hscal]
      _ = (G * H) * (A * B * D) * 1 := by rw [mul_one]
      _ = (G * H) * (A * B * D) * ((μ (ball (0 : E) 1))⁻¹ * μ (ball (0 : E) 1)) := by rw [hbb]
      _ = G * (A * B) * (μ (ball (0 : E) 1))⁻¹ * D * (H * μ (ball (0 : E) 1)) := by ring
  -- the triangle inequality, averaged over the middle ball
  have hLmx : Measurable fun y : E ↦ ‖u y - u x‖ₑ :=
    ((hu.continuous.sub continuous_const).enorm).measurable
  have htri : ∀ y : E, ‖u x - u z‖ₑ ≤ ‖u y - u x‖ₑ + ‖u y - u z‖ₑ := by
    intro y
    have he : u x - u z = -(u y - u x) + (u y - u z) := by abel
    rw [he]
    exact (enorm_add_le _ _).trans_eq (by rw [enorm_neg])
  have hkey : ‖u x - u z‖ₑ * μ (ball ((2 : ℝ)⁻¹ • (x + z)) (‖x - z‖ / 2))
      ≤ (((morreyConst E μ p : ℝ≥0) : ℝ≥0∞) * ‖x - z‖ₑ ^ (1 - (finrank ℝ E : ℝ) / (p : ℝ)) *
          eLpNorm (fderiv ℝ u) p μ) * μ (ball ((2 : ℝ)⁻¹ • (x + z)) (‖x - z‖ / 2)) := by
    calc ‖u x - u z‖ₑ * μ (ball ((2 : ℝ)⁻¹ • (x + z)) (‖x - z‖ / 2))
        = ∫⁻ _y in ball ((2 : ℝ)⁻¹ • (x + z)) (‖x - z‖ / 2), ‖u x - u z‖ₑ ∂μ :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ y in ball ((2 : ℝ)⁻¹ • (x + z)) (‖x - z‖ / 2),
            (‖u y - u x‖ₑ + ‖u y - u z‖ₑ) ∂μ := lintegral_mono htri
      _ = (∫⁻ y in ball ((2 : ℝ)⁻¹ • (x + z)) (‖x - z‖ / 2), ‖u y - u x‖ₑ ∂μ)
            + ∫⁻ y in ball ((2 : ℝ)⁻¹ • (x + z)) (‖x - z‖ / 2), ‖u y - u z‖ₑ ∂μ :=
          lintegral_add_left hLmx _
      _ ≤ (∫⁻ y in ball x ‖x - z‖, ‖u y - u x‖ₑ ∂μ)
            + ∫⁻ y in ball z ‖x - z‖, ‖u y - u z‖ₑ ∂μ :=
          add_le_add (lintegral_mono_set hVx) (lintegral_mono_set hVz)
      _ ≤ ((rieszPotentialConst E ‖x - z‖ : ℝ≥0) : ℝ≥0∞) * (eLpNorm (fderiv ℝ u) p μ *
              ((rieszKernelConst μ a ‖x - z‖ : ℝ≥0) : ℝ≥0∞) ^ ((1 : ℝ) / q))
            + ((rieszPotentialConst E ‖x - z‖ : ℝ≥0) : ℝ≥0∞) * (eLpNorm (fderiv ℝ u) p μ *
              ((rieszKernelConst μ a ‖x - z‖ : ℝ≥0) : ℝ≥0∞) ^ ((1 : ℝ) / q)) :=
          add_le_add (hosc x) (hosc z)
      _ = (2 * ((rieszPotentialConst E ‖x - z‖ : ℝ≥0) : ℝ≥0∞) *
            ((rieszKernelConst μ a ‖x - z‖ : ℝ≥0) : ℝ≥0∞) ^ ((1 : ℝ) / q)) *
            eLpNorm (fderiv ℝ u) p μ := by ring
      _ = (((morreyConst E μ p : ℝ≥0) : ℝ≥0∞) *
            (ENNReal.ofReal ‖x - z‖) ^ (1 - (finrank ℝ E : ℝ) / (p : ℝ)) *
            μ (ball ((2 : ℝ)⁻¹ • (x + z)) (‖x - z‖ / 2))) * eLpNorm (fderiv ℝ u) p μ := by
          rw [hconst]
      _ = (((morreyConst E μ p : ℝ≥0) : ℝ≥0∞) * ‖x - z‖ₑ ^ (1 - (finrank ℝ E : ℝ) / (p : ℝ)) *
            eLpNorm (fderiv ℝ u) p μ) * μ (ball ((2 : ℝ)⁻¹ • (x + z)) (‖x - z‖ / 2)) := by
          rw [ofReal_norm (x - z)]
          ring
  have hfin := (ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inl hVt)).2 hkey
  rwa [ENNReal.mul_div_cancel_right hV0 hVt] at hfin

variable (E) in
/-- The constant in the essential-supremum form of Morrey's inequality. Besides `E`, `μ` and
`p` it depends on the support `s`, through its diameter — exactly as the constant of
`eLpNorm_le_eLpNorm_fderiv_of_le` depends on `s` through its measure. -/
def morreyEssSupConst (s : Set E) (p : ℝ≥0) : ℝ≥0 :=
  morreyConst E μ p * (Metric.diam s).toNNReal ^ (1 - (finrank ℝ E : ℝ) / p)

/-- **Morrey's inequality.**

A continuously differentiable function supported in a bounded set, on a space of dimension
`n < p`, is essentially bounded by a constant times the `Lᵖ` norm of its derivative.

This is the statement that supplies the Sobolev embedding `W^{1,p} ↪ L^∞` for `p > n`. -/
theorem eLpNorm_top_le_eLpNorm_fderiv [Nontrivial E]
    {u : E → F} {s : Set E} (hu : ContDiff ℝ 1 u) (h2u : u.support ⊆ s)
    {p : ℝ≥0} (hp : (finrank ℝ E : ℝ≥0) < p) (hs : Bornology.IsBounded s) :
    eLpNorm u ⊤ μ ≤ morreyEssSupConst E μ s p * eLpNorm (fderiv ℝ u) p μ := by
  have hnp : (finrank ℝ E : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_le_of_lt (Nat.cast_nonneg _) hnp
  have hexp : (0 : ℝ) ≤ 1 - (finrank ℝ E : ℝ) / (p : ℝ) :=
    sub_nonneg.2 ((div_le_one hp0).2 hnp.le)
  have hd0 : (0 : ℝ) ≤ Metric.diam s := Metric.diam_nonneg
  have hofReal : ∀ t : ℝ, ((t.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal t := fun _ ↦ rfl
  -- A unit vector, along which we walk out of `s`.
  obtain ⟨v, hv1⟩ : ∃ v : E, ‖v‖ = 1 := by
    obtain ⟨w, hw⟩ := exists_ne (0 : E)
    exact ⟨‖w‖⁻¹ • w, by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)]⟩
  rw [eLpNorm_exponent_top hu.continuous.aestronglyMeasurable]
  refine eLpNormEssSup_le_of_ae_enorm_bound (.of_forall fun x ↦ ?_)
  rcases eq_or_ne (u x) 0 with hux | hux
  · simp [hux]
  have hxs : x ∈ s := h2u (Function.mem_support.mpr hux)
  have hnormsub : ∀ θ : ℝ, 0 ≤ θ → ‖x - (x + θ • v)‖ = θ := by
    intro θ hθ
    have hxx : x - (x + θ • v) = -(θ • v) := by abel
    rw [hxx, norm_neg, norm_smul, hv1, mul_one, Real.norm_eq_abs, abs_of_nonneg hθ]
  -- Beyond distance `diam s` from `x` the function vanishes.
  have hzero : ∀ θ : ℝ, Metric.diam s < θ → u (x + θ • v) = 0 := by
    intro θ hθ
    by_contra hne
    have hmem : x + θ • v ∈ s := h2u (Function.mem_support.mpr hne)
    have hle : dist x (x + θ • v) ≤ Metric.diam s := Metric.dist_le_diam_of_mem hs hxs hmem
    rw [dist_eq_norm, hnormsub θ (hd0.trans hθ.le)] at hle
    exact absurd hle (not_le.2 hθ)
  -- By continuity it already vanishes at distance exactly `diam s`.
  have huz : u (x + Metric.diam s • v) = 0 := by
    have hgc : Continuous fun θ : ℝ ↦ u (x + θ • v) := by fun_prop
    have hcl : IsClosed {θ : ℝ | u (x + θ • v) = 0} := isClosed_eq hgc continuous_const
    have hsub : Ioi (Metric.diam s) ⊆ {θ : ℝ | u (x + θ • v) = 0} := fun θ hθ ↦ hzero θ hθ
    have hcls := hcl.closure_subset_iff.2 hsub
    rw [closure_Ioi] at hcls
    exact hcls self_mem_Ici
  have key := enorm_sub_le_morreyConst_mul_rpow_mul_eLpNorm_fderiv μ hu hp x
    (x + Metric.diam s • v)
  rw [huz, sub_zero] at key
  refine key.trans (le_of_eq ?_)
  have hnorm : ‖x - (x + Metric.diam s • v)‖ₑ = ENNReal.ofReal (Metric.diam s) := by
    rw [← ofReal_norm, hnormsub _ hd0]
  rw [hnorm, morreyEssSupConst, ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ hexp,
    hofReal]

end Morrey

end MeasureTheory

end
