/-
Copyright (c) 2026 Octavian Halmaghi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Octavian Halmaghi
-/
module

public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
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

The classical route, in three steps. The analytic tool underlying the first two is polar
coordinates on a ball, `MeasureTheory.setLIntegral_ball_eq_lintegral_toSphere_lintegral_Ioo`
from `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`: an additive Haar measure on an
`n`-dimensional normed space is the product of the sphere measure
`MeasureTheory.Measure.toSphere` and Lebesgue measure on `(0, ∞)` with density `r ^ (n - 1)`.

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
   The right-hand side is a Riesz potential of the derivative: in polar coordinates the
   density `ρ ^ (n - 1)` cancels the Riesz kernel exactly, and what is left on each ray is the
   fundamental theorem of calculus.

3. Hölder's inequality against that kernel, with the exponents `p` and `q`, turns step 2 into
   `∫⁻ y in B, ‖u y - u x‖ₑ ∂μ ≤ r ^ n / n * ‖fderiv ℝ u‖_{Lᵖ} * (kernel integral) ^ (1 / q)`,
   and the kernel integral is the constant of step 1. Averaging that over the two balls of
   radius `d = ‖x - z‖` around `x` and around `z`, and comparing with the average over
   `ball (midpoint ℝ x z) (d / 2)`, which is contained in both and has measure at least
   `2 ^ (-n)` times theirs, gives the Hölder estimate. Finally, for a function supported in a
   bounded set `s`, a boundary point `z` of the (open, bounded) support of `u` lies within
   `diam s` of any point `x` of the support and `u` vanishes there, and that turns the Hölder
   estimate into the bound on the essential supremum.

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

/-- The constant `n / (n - a) * μ (ball 0 1) * r ^ (n - a)`, for `n = finrank ℝ E`. When
`0 < r` and `a < n` it is the exact value of the integral of the Riesz kernel
`y ↦ ‖y - x‖ ^ (-a)` over `ball x r`: see `setLIntegral_ball_rpow_neg`. Outside that range the
factors are truncated by `Real.toNNReal` and the value has no meaning.

It depends only on `E`, `μ`, `a` and `r`, and is homogeneous of degree one in `μ`. Keeping it
named, rather than existential, is what lets the constants in the main statements below, such
as `morreyConst`, be written down explicitly. -/
def rieszKernelConst (a r : ℝ) : ℝ≥0 :=
  ((finrank ℝ E : ℝ) / (finrank ℝ E - a)).toNNReal * (μ (ball (0 : E) 1)).toNNReal *
    r.toNNReal ^ (finrank ℝ E - a)

omit [BorelSpace E] in
/-- For `a ≤ n`, the constant `rieszKernelConst μ a r` read in `ℝ≥0∞` is
`ENNReal.ofReal (n / (n - a)) * μ (ball 0 1) * ENNReal.ofReal r ^ (n - a)`: the `Real.toNNReal`
truncations of the definition become `ENNReal.ofReal`, and the unit ball keeps its measure. -/
theorem coe_rieszKernelConst {a : ℝ} (ha : a ≤ finrank ℝ E) (r : ℝ) :
    (rieszKernelConst μ a r : ℝ≥0∞) = ENNReal.ofReal (finrank ℝ E / (finrank ℝ E - a)) *
      μ (ball (0 : E) 1) * ENNReal.ofReal r ^ ((finrank ℝ E : ℝ) - a) := by
  rw [rieszKernelConst, ENNReal.coe_mul, ENNReal.coe_mul,
    ENNReal.coe_toNNReal measure_ball_lt_top.ne, ENNReal.coe_rpow_of_nonneg _ (sub_nonneg.2 ha)]
  simp only [ENNReal.ofNNReal_toNNReal]

/-- The radial integral `∫⁻ ρ in (0, r), ρ ^ s = r ^ (s + 1) / (s + 1)`, for `-1 < s`. -/
private theorem lintegral_Ioo_ofReal_rpow {r s : ℝ} (hr : 0 < r) (hs : -1 < s) :
    ∫⁻ ρ in Ioo 0 r, ENNReal.ofReal (ρ ^ s) = ENNReal.ofReal (r ^ (s + 1) / (s + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal ((intervalIntegral.integrableOn_Ioo_rpow_iff hr).2 hs)
      (ae_restrict_of_forall_mem measurableSet_Ioo fun ρ hρ ↦ Real.rpow_nonneg hρ.1.le _),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
    integral_rpow (.inl hs), Real.zero_rpow (by linarith), sub_zero]

/-- **The value of the Riesz kernel integral on a ball.**

The quantitative companion of `setLIntegral_ball_rpow_neg_lt_top`: when `a < n` the integral of
`y ↦ ‖y - x‖ ^ (-a)` over `ball x r` is exactly `rieszKernelConst μ a r`, that is
`n / (n - a) * μ (ball 0 1) * r ^ (n - a)` (see `coe_rieszKernelConst` for that form). -/
theorem setLIntegral_ball_rpow_neg [Nontrivial E] (x : E) {r a : ℝ} (hr : 0 < r)
    (han : a < finrank ℝ E) : (∫⁻ y in ball x r, ‖y - x‖ₑ ^ (-a) ∂μ) = rieszKernelConst μ a r := by
  -- polar coordinates: on each ray the integrand becomes `ρ ^ (n - a - 1)`
  rw [setLIntegral_ball_eq_lintegral_toSphere_lintegral_Ioo μ x r (by fun_prop)]
  have hinner (ω : sphere (0 : E) 1) : ∫⁻ ρ in Ioo 0 r,
      ENNReal.ofReal (ρ ^ (finrank ℝ E - 1)) * ‖x + ρ • (ω : E) - x‖ₑ ^ (-a) =
        ∫⁻ ρ in Ioo 0 r, ENNReal.ofReal (ρ ^ ((finrank ℝ E : ℝ) - a - 1)) := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun ρ hρ ↦ ?_
    rw [add_sub_cancel_left, ← ofReal_norm, norm_smul, norm_eq_of_mem_sphere, mul_one,
      Real.norm_of_nonneg hρ.1.le, ENNReal.ofReal_rpow_of_pos hρ.1,
      ← ENNReal.ofReal_mul (pow_nonneg hρ.1.le _), ← Real.rpow_natCast, ← Real.rpow_add hρ.1,
      Nat.cast_pred finrank_pos, ← sub_eq_add_neg, sub_right_comm]
  -- the radial integral; the sphere contributes `μ.toSphere univ = n * μ (ball 0 1)`
  rw [lintegral_congr hinner, lintegral_Ioo_ofReal_rpow hr (by linarith), sub_add_cancel,
    lintegral_const, toSphere_apply_univ, coe_rieszKernelConst μ han.le,
    ENNReal.ofReal_rpow_of_pos hr, ← ENNReal.ofReal_natCast]
  -- identify the constant
  rw [← mul_assoc, ← ENNReal.ofReal_mul' (by positivity), mul_right_comm,
    ← ENNReal.ofReal_mul' (by positivity)]
  congr 2
  ring

/-- **Integrability of the Riesz kernel on a ball.** For `a < n`, the integral of
`y ↦ ‖y - x‖ₑ ^ (-a)` over `ball x r` is finite.

This is the qualitative form of `setLIntegral_ball_rpow_neg`, which computes the integral; use that
lemma when the value matters, and `.ne` of this one for the `≠ ∞` side conditions of `ℝ≥0∞`
arithmetic. Only the direction `a < n` is stated: for `n ≤ a` the integral is infinite. Compare
`integrableOn_ball_of_norm_le_rpow`, the Bochner-integrability form centred at `0`. -/
theorem setLIntegral_ball_rpow_neg_lt_top [Nontrivial E] (x : E) {r a : ℝ} (hr : 0 < r)
    (han : a < finrank ℝ E) : ∫⁻ y in ball x r, ‖y - x‖ₑ ^ (-a) ∂μ < ∞ :=
  (setLIntegral_ball_rpow_neg μ x hr han).trans_lt ENNReal.coe_lt_top

end RieszKernel

section Potential

variable (E) in
/-- The constant `r ^ n / n`, for `n = finrank ℝ E`, in the Riesz potential estimate
`lintegral_ball_enorm_sub_le_lintegral_riesz`. For `0 < r` it is `∫_0^r ρ ^ (n - 1) dρ`, the
radial integral of the polar-coordinates density on `ball x r`. For `r < 0` the value is the
`Real.toNNReal` truncation of `r ^ n / n` and has no meaning.

Unlike `rieszKernelConst` it does not depend on `μ`: both sides of that estimate are
homogeneous of degree one in `μ`. -/
def rieszPotentialConst (r : ℝ) : ℝ≥0 :=
  (r ^ finrank ℝ E / (finrank ℝ E : ℝ)).toNNReal

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The constant `rieszPotentialConst E r` read in `ℝ≥0∞` is `ENNReal.ofReal (r ^ n / n)`: the
`Real.toNNReal` truncation of the definition becomes `ENNReal.ofReal`. -/
theorem coe_rieszPotentialConst (r : ℝ) :
    (rieszPotentialConst E r : ℝ≥0∞) = ENNReal.ofReal (r ^ finrank ℝ E / finrank ℝ E) := rfl

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- **Fundamental theorem of calculus along a ray.** For a `C¹` function `u` and a unit
vector `ω`, the increment `‖u (x + ρ • ω) - u x‖ₑ` is at most the integral over `(0, ρ]` of
the operator enorm of `fderiv ℝ u` along the ray from `x` in the direction `ω`.

This is the several-variable counterpart of `enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc`.
The target space `F` need not be complete. -/
theorem enorm_sub_le_lintegral_Ioc_enorm_fderiv {u : E → F} (hu : ContDiff ℝ 1 u) (x : E) {ω : E}
    (hω : ‖ω‖ = 1) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖u (x + ρ • ω) - u x‖ₑ ≤ ∫⁻ t in Ioc (0 : ℝ) ρ, ‖fderiv ℝ u (x + t • ω)‖ₑ := by
  -- the fundamental theorem of calculus for `u` restricted to the ray
  have h := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc
    (f := fun s : ℝ ↦ u (x + s • ω)) (hu.comp (by fun_prop)).contDiffOn hρ
  simp only [zero_smul, add_zero] at h
  rw [restrict_Ioc_eq_restrict_Icc]
  refine h.trans <| lintegral_mono fun t ↦ ?_
  -- the derivative of `u` along the ray through `x` in the direction `ω`
  have hd : HasDerivAt (fun s : ℝ ↦ u (x + s • ω)) (fderiv ℝ u (x + t • ω) ω) t :=
    (hu.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t <| by
      simpa using ((hasDerivAt_id t).smul_const ω).const_add x
  rw [hd.deriv]
  simpa [← ofReal_norm, hω] using (fderiv ℝ u (x + t • ω)).le_opENorm ω

/-- **The Riesz potential estimate.**

For `u` of class `C¹`, the mean oscillation of `u` on a ball is controlled by the Riesz
potential of its derivative:
`∫⁻ y in ball x r, ‖u y - u x‖ₑ ∂μ ≤ (r ^ n / n) * (Riesz potential of the derivative)`,
with the constant `rieszPotentialConst E r = r ^ n / n`.

The right-hand side is finite once `fderiv ℝ u` is in `Lᵖ` for some `p > n`, by Hölder's
inequality against `setLIntegral_ball_rpow_neg`; this is how Morrey's inequality uses it. The
target space `F` need not be complete. -/
theorem lintegral_ball_enorm_sub_le_lintegral_riesz [Nontrivial E] {u : E → F} (hu : ContDiff ℝ 1 u)
    (x : E) {r : ℝ} (hr : 0 < r) : (∫⁻ y in ball x r, ‖u y - u x‖ₑ ∂μ) ≤ rieszPotentialConst E r *
      ∫⁻ y in ball x r, ‖fderiv ℝ u y‖ₑ / ‖y - x‖ₑ ^ ((finrank ℝ E : ℝ) - 1) ∂μ := by
  have hn : ((finrank ℝ E - 1 : ℕ) : ℝ) = finrank ℝ E - 1 := Nat.cast_pred finrank_pos
  -- the radial density integrates to `r ^ n / n`
  have hpow : ∫⁻ ρ in Ioo 0 r, ENNReal.ofReal (ρ ^ (finrank ℝ E - 1)) =
      rieszPotentialConst E r := by
    simp_rw [← Real.rpow_natCast]
    rw [lintegral_Ioo_ofReal_rpow hr (neg_one_lt_zero.trans_le (Nat.cast_nonneg _)), hn,
      sub_add_cancel, Real.rpow_natCast, coe_rieszPotentialConst]
  -- polar coordinates about `x` on both sides
  have := hu.continuous
  rw [setLIntegral_ball_eq_lintegral_toSphere_lintegral_Ioo μ x r
      (by fun_prop : Continuous _).measurable,
    setLIntegral_ball_eq_lintegral_toSphere_lintegral_Ioo μ x r
      ((hu.continuous_fderiv one_ne_zero).enorm.measurable.fun_div (by fun_prop)),
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_mono fun ω ↦ ?_
  -- compare the two ray integrals, by the fundamental theorem of calculus along each ray
  calc _ ≤ ∫⁻ ρ in Ioo 0 r, ENNReal.ofReal (ρ ^ (finrank ℝ E - 1)) *
          ∫⁻ t in Ioo 0 r, ‖fderiv ℝ u (x + t • (ω : E))‖ₑ :=
        setLIntegral_mono' measurableSet_Ioo fun ρ hρ ↦ mul_le_mul_right
          ((enorm_sub_le_lintegral_Ioc_enorm_fderiv hu x (norm_eq_of_mem_sphere ω) hρ.1.le).trans
            (lintegral_mono_set (Ioc_subset_Ioo_right hρ.2))) _
    _ = _ := by
      rw [lintegral_mul_const'' _ (by fun_prop), hpow]
      congr 1
      -- polar form of the right-hand side: the radial density cancels the Riesz kernel
      refine (setLIntegral_congr_fun measurableSet_Ioo fun ρ hρ ↦ ?_).symm
      rw [add_sub_cancel_left, enorm_smul, Real.enorm_of_nonneg hρ.1.le, ← ofReal_norm (ω : E),
        norm_eq_of_mem_sphere, ENNReal.ofReal_one, mul_one, ENNReal.ofReal_rpow_of_pos hρ.1, ← hn,
        Real.rpow_natCast, ENNReal.mul_div_cancel (by simp [hρ.1]) ENNReal.ofReal_ne_top]

end Potential

section Morrey

variable (E) in
/-- The constant `2 ^ (n + 1) / n * rieszKernelConst μ ((n - 1) * q) 1 ^ (1 / q) / μ (ball 0 1)`,
for `n = finrank ℝ E` and `q` the conjugate exponent of `p`, in the Hölder estimate of Morrey's
inequality, `enorm_sub_le_morreyConst_mul_rpow_mul_eLpNorm_fderiv`. Outside the range `n < p`
of that estimate the value has no meaning.

It depends only on `E`, `μ` and `p`, and is homogeneous of degree `1 / q - 1 = -1 / p` in `μ`,
which is what makes the estimate invariant under rescaling `μ`, since `eLpNorm · p μ` is
homogeneous of degree `1 / p`. -/
def morreyConst (p : ℝ≥0) : ℝ≥0 :=
  let n : ℝ := finrank ℝ E
  let q : ℝ := (1 - 1 / p)⁻¹  -- the conjugate exponent of `p`
  ((2 : ℝ) ^ (finrank ℝ E + 1) / n).toNNReal * rieszKernelConst μ ((n - 1) * q) 1 ^ (1 / q) *
    (μ (ball (0 : E) 1)).toNNReal⁻¹

omit [BorelSpace E] in
/-- For `1 ≤ p`, the constant `morreyConst E μ p` read in `ℝ≥0∞`: the `Real.toNNReal`
truncations of the definition become `ENNReal.ofReal`, the unit ball keeps its measure, and the
power `1 / q` is distributed over the two factors of `rieszKernelConst μ ((n - 1) * q) 1`. -/
theorem coe_morreyConst {p : ℝ≥0} (hp : 1 ≤ p) :
    (morreyConst E μ p : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ (finrank ℝ E + 1) / finrank ℝ E) *
      (ENNReal.ofReal (finrank ℝ E / (finrank ℝ E - (finrank ℝ E - 1) * (1 - 1 / (p : ℝ))⁻¹)) ^
        (1 / (1 - 1 / (p : ℝ))⁻¹) * μ (ball (0 : E) 1) ^ (1 / (1 - 1 / (p : ℝ))⁻¹)) *
      (μ (ball (0 : E) 1))⁻¹ := by
  have hq : 0 ≤ 1 / (1 - 1 / (p : ℝ))⁻¹ := by
    simpa using inv_le_one_of_one_le₀ (mod_cast hp : (1 : ℝ) ≤ p)
  simp only [morreyConst, rieszKernelConst, Real.toNNReal_one, NNReal.one_rpow, mul_one,
    ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ hq, ENNReal.mul_rpow_of_nonneg _ _ hq,
    ENNReal.coe_inv (ENNReal.toNNReal_ne_zero.2 ⟨(measure_ball_pos μ 0 one_pos).ne',
      measure_ball_lt_top.ne⟩), ENNReal.coe_toNNReal measure_ball_lt_top.ne,
    ENNReal.ofNNReal_toNNReal]

private theorem sub_one_mul_conj_lt_of_lt {n p q : ℝ} (hpq : p.HolderConjugate q) (hnp : n < p) :
    (n - 1) * q < n := by nlinarith [hpq.sub_one_mul_conj, hpq.symm.lt]

omit [MeasurableSpace E] [BorelSpace E] in
private theorem holderConjugate_of_finrank_lt [Nontrivial E] {p : ℝ≥0}
    (hp : (finrank ℝ E : ℝ≥0) < p) : (p : ℝ).HolderConjugate (1 - 1 / (p : ℝ))⁻¹ :=
  Real.holderConjugate_iff.2 ⟨mod_cast (Nat.one_le_cast.2 finrank_pos).trans_lt hp, by simp⟩

private theorem lintegral_ball_enorm_sub_le_eLpNorm_fderiv [Nontrivial E] {u : E → F}
    (hu : ContDiff ℝ 1 u) {p : ℝ≥0} (hp : (finrank ℝ E : ℝ≥0) < p) {q : ℝ}
    (hpq : (p : ℝ).HolderConjugate q) (c : E) {r : ℝ} (hr : 0 < r) :
    ∫⁻ y in ball c r, ‖u y - u c‖ₑ ∂μ ≤ rieszPotentialConst E r * (eLpNorm (fderiv ℝ u) p μ *
      (rieszKernelConst μ ((finrank ℝ E - 1) * q) r : ℝ≥0∞) ^ (1 / q)) := by
  -- the mean oscillation on the ball is controlled by the Riesz potential of the derivative, and
  -- Hölder's inequality against the Riesz kernel turns that into the `Lᵖ` norm of the derivative:
  -- `q` is the conjugate exponent of `p`, `(n - 1) * q` the exponent of the Riesz kernel, and the
  -- kernel is integrable exactly because `n < p`
  refine (lintegral_ball_enorm_sub_le_lintegral_riesz μ hu c hr).trans (mul_le_mul_right ?_ _)
  have hDu := hu.continuous_fderiv one_ne_zero
  have := secondCountableTopologyEither_of_left E (E →L[ℝ] F)
  rw [← setLIntegral_ball_rpow_neg μ c hr (sub_one_mul_conj_lt_of_lt hpq (mod_cast hp))]
  calc _ = ∫⁻ y in ball c r, ‖fderiv ℝ u y‖ₑ * ‖y - c‖ₑ ^ (-((finrank ℝ E : ℝ) - 1)) ∂μ := by
        simp_rw [ENNReal.rpow_neg, div_eq_mul_inv]
    _ ≤ (∫⁻ y in ball c r, ‖fderiv ℝ u y‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) *
          (∫⁻ y in ball c r, (‖y - c‖ₑ ^ (-((finrank ℝ E : ℝ) - 1))) ^ q ∂μ) ^ (1 / q) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq (f := fun y ↦ ‖fderiv ℝ u y‖ₑ)
          (g := fun y : E ↦ ‖y - c‖ₑ ^ (-((finrank ℝ E : ℝ) - 1))) hDu.enorm.aemeasurable
          (by fun_prop)
    -- the `Lᵖ` norm of the derivative as a Lebesgue integral
    _ ≤ _ := by
        rw [← eLpNorm_nnreal_eq_lintegral (mod_cast hpq.ne_zero) hDu.aestronglyMeasurable]
        simp_rw [← ENNReal.rpow_mul, neg_mul]
        gcongr
        exact restrict_le_self

omit [FiniteDimensional ℝ E] [IsAddHaarMeasure μ] [NormedSpace ℝ F] in
private theorem enorm_sub_mul_measure_ball_midpoint_le {u : E → F} (hu : Continuous u) (x z : E) :
    ‖u x - u z‖ₑ * μ (ball (midpoint ℝ x z) (‖x - z‖ / 2)) ≤
      (∫⁻ y in ball x ‖x - z‖, ‖u y - u x‖ₑ ∂μ) + ∫⁻ y in ball z ‖x - z‖, ‖u y - u z‖ₑ ∂μ := by
  -- the triangle inequality, averaged over the middle ball
  rw [← setLIntegral_const]
  calc _ ≤ ∫⁻ y in ball (midpoint ℝ x z) (‖x - z‖ / 2), ‖u y - u x‖ₑ + ‖u y - u z‖ₑ ∂μ :=
        lintegral_mono fun y ↦ by
          simpa only [edist_eq_enorm_sub] using edist_triangle_left (u x) (u z) (u y)
    _ = (∫⁻ y in ball (midpoint ℝ x z) (‖x - z‖ / 2), ‖u y - u x‖ₑ ∂μ) +
          ∫⁻ y in ball (midpoint ℝ x z) (‖x - z‖ / 2), ‖u y - u z‖ₑ ∂μ :=
        lintegral_add_left (hu.sub continuous_const).enorm.measurable _
    -- the ball about the midpoint, contained in both balls of radius `‖x - z‖`
    _ ≤ _ := by
        gcongr <;> refine ball_subset_ball' ?_ <;>
          simp only [dist_midpoint_left (𝕜 := ℝ), dist_midpoint_right (𝕜 := ℝ), Real.norm_ofNat,
            dist_eq_norm] <;> linarith

private theorem coe_morreyConst_mul_rpow_mul_measure_ball [Nontrivial E] {p : ℝ≥0}
    (hp : (finrank ℝ E : ℝ≥0) < p) (m : E) {d : ℝ} (hd : 0 ≤ d) : (morreyConst E μ p : ℝ≥0∞) *
      ENNReal.ofReal d ^ (1 - (finrank ℝ E : ℝ) / p) * μ (ball m (d / 2)) =
        2 * rieszPotentialConst E d *
          (rieszKernelConst μ ((finrank ℝ E - 1) * (1 - 1 / (p : ℝ))⁻¹) d : ℝ≥0∞) ^
            (1 / (1 - 1 / (p : ℝ))⁻¹) := by
  -- the three factors of `morreyConst` are `2 ^ (n + 1) / n` (the constant `r ^ n / n` of the
  -- Riesz potential estimate and the two-fold comparison of the averages over `ball x d` and
  -- `ball z d` with the average over `ball (midpoint ℝ x z) (d / 2)`),
  -- `rieszKernelConst μ ((n - 1) * q) 1 ^ (1 / q)` (the kernel factor from Hölder's inequality),
  -- and `(μ (ball 0 1))⁻¹` (normalising the averages)
  -- numerical preliminaries
  have hpq := holderConjugate_of_finrank_lt hp
  have hp1 : 1 < p := mod_cast hpq.lt
  have hq : 0 ≤ 1 / (1 - 1 / (p : ℝ))⁻¹ := hpq.symm.one_div_nonneg
  have hexp : ((finrank ℝ E : ℝ) - (finrank ℝ E - 1) * (1 - 1 / (p : ℝ))⁻¹) *
      (1 / (1 - 1 / (p : ℝ))⁻¹) = 1 - finrank ℝ E / p := by
    have := hpq.sub_one_ne_zero
    field_simp
    ring
  have hscal : 2 * ENNReal.ofReal (d ^ finrank ℝ E / finrank ℝ E) =
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) / finrank ℝ E) *
        ENNReal.ofReal ((d / 2) ^ finrank ℝ E) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_pow, pow_succ]
    field_simp
  -- the shape of the two constants
  rw [coe_morreyConst μ hp1.le, μ.addHaar_ball _ (div_nonneg hd zero_le_two),
    coe_rieszKernelConst μ (sub_one_mul_conj_lt_of_lt hpq (mod_cast hp)).le,
    ENNReal.mul_rpow_of_nonneg _ _ hq, ENNReal.mul_rpow_of_nonneg _ _ hq, ← ENNReal.rpow_mul, hexp,
    coe_rieszPotentialConst, hscal]
  -- the six factors are now common to the two sides, once `μ (ball 0 1)` cancels
  simp only [mul_assoc]
  rw [mul_comm (ENNReal.ofReal _) (μ (ball (0 : E) 1)), mul_left_comm _ (μ (ball (0 : E) 1)),
    ENNReal.inv_mul_cancel_left (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne]
  ring

/-- **Morrey's inequality, Hölder form.**

Let `u` be a continuously differentiable function on a normed space `E` of finite dimension
`n`, equipped with a Haar measure, and let `finrank ℝ E < p`. Then `u` is Hölder continuous
of exponent `1 - n / p`, with seminorm bounded by the `Lᵖ` norm of its derivative.

This is the supercritical counterpart of `MeasureTheory.eLpNorm_le_eLpNorm_fderiv`, whose
hypothesis is `p < finrank ℝ E`.

No support hypothesis is needed for this estimate. -/
theorem enorm_sub_le_morreyConst_mul_rpow_mul_eLpNorm_fderiv [Nontrivial E] {u : E → F}
    (hu : ContDiff ℝ 1 u) {p : ℝ≥0} (hp : (finrank ℝ E : ℝ≥0) < p) (x z : E) : ‖u x - u z‖ₑ ≤
      morreyConst E μ p * ‖x - z‖ₑ ^ (1 - (finrank ℝ E : ℝ) / p) * eLpNorm (fderiv ℝ u) p μ := by
  rcases eq_or_ne x z with rfl | hxz
  · simp
  have hpq := holderConjugate_of_finrank_lt hp
  have hd : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hxz)
  -- the triangle inequality, averaged over the middle ball, and the mean oscillation on a ball of
  -- radius `‖x - z‖`, by Hölder against the Riesz kernel
  refine (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ _ (half_pos hd)).ne'
    measure_ball_lt_top.ne).1 <| (enorm_sub_mul_measure_ball_midpoint_le μ hu.continuous x z).trans
    ((add_le_add (lintegral_ball_enorm_sub_le_eLpNorm_fderiv μ hu hp hpq x hd)
      (lintegral_ball_enorm_sub_le_eLpNorm_fderiv μ hu hp hpq z hd)).trans_eq ?_)
  -- the constant identity: this is where the value of `morreyConst` is pinned down
  rw [← ofReal_norm (x - z), mul_right_comm _ (eLpNorm _ _ _),
    coe_morreyConst_mul_rpow_mul_measure_ball μ hp _ hd.le]
  ring

variable (E) in
/-- The constant `morreyConst E μ p * diam s ^ (1 - n / p)`, for `n = finrank ℝ E`, in the
essential-supremum form of Morrey's inequality, `eLpNorm_top_le_eLpNorm_fderiv`. Besides `E`, `μ`
and `p` it depends on the support `s`, through its diameter, just as the constant of
`eLpNorm_le_eLpNorm_fderiv_of_le` depends on `s` through its measure. -/
def morreyEssSupConst (s : Set E) (p : ℝ≥0) : ℝ≥0 :=
  morreyConst E μ p * (diam s).toNNReal ^ (1 - (finrank ℝ E : ℝ) / p)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
private theorem one_sub_finrank_div_nonneg {p : ℝ≥0} (hp : (finrank ℝ E : ℝ≥0) ≤ p) :
    0 ≤ 1 - (finrank ℝ E : ℝ) / p :=
  sub_nonneg.2 (div_le_one_of_le₀ (mod_cast hp) p.coe_nonneg)

omit [BorelSpace E] [FiniteDimensional ℝ E] [IsAddHaarMeasure μ] in
/-- For `n ≤ p`, the constant `morreyEssSupConst E μ s p` read in `ℝ≥0∞`, with the diameter
entering through `ENNReal.ofReal`. -/
theorem coe_morreyEssSupConst {s : Set E} {p : ℝ≥0} (hp : (finrank ℝ E : ℝ≥0) ≤ p) :
    (morreyEssSupConst E μ s p : ℝ≥0∞) = morreyConst E μ p * ENNReal.ofReal (diam s) ^
      (1 - (finrank ℝ E : ℝ) / p) := by
  rw [morreyEssSupConst, ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _
    (one_sub_finrank_div_nonneg hp), ENNReal.ofNNReal_toNNReal]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
/-- A continuous function supported in a bounded set `s` of a nontrivial real normed space
vanishes somewhere within `diam s` of each point of its support: at a boundary point of the
support, which is open, nonempty and not the whole space. -/
private theorem exists_eq_zero_dist_le_diam [Nontrivial E] {u : E → F} {s : Set E}
    (hu : Continuous u) (h2u : u.support ⊆ s) (hs : Bornology.IsBounded s) {x : E} (hx : u x ≠ 0) :
    ∃ z, u z = 0 ∧ dist x z ≤ diam s := by
  obtain ⟨z, hzc, hzs⟩ : (closure u.support \ u.support).Nonempty :=
    hu.isOpen_support.frontier_eq ▸ nonempty_frontier_iff.2
      ⟨⟨x, hx⟩, fun h ↦ NormedSpace.unbounded_univ ℝ E (h ▸ hs.subset h2u)⟩
  exact ⟨z, notMem_support.1 hzs, diam_closure s ▸ dist_le_diam_of_mem hs.closure
    (subset_closure (h2u hx)) (closure_mono h2u hzc)⟩

/-- **Morrey's inequality.**

A continuously differentiable function supported in a bounded set `s`, on a space of
dimension `n < p`, is essentially bounded by the `Lᵖ` norm of its derivative times the
constant `morreyEssSupConst E μ s p = morreyConst E μ p * diam s ^ (1 - n / p)`.

This is the statement that supplies the Sobolev embedding `W^{1,p} ↪ L^∞` for `p > n`. -/
theorem eLpNorm_top_le_eLpNorm_fderiv [Nontrivial E] {u : E → F} {s : Set E} (hu : ContDiff ℝ 1 u)
    (h2u : u.support ⊆ s) {p : ℝ≥0} (hp : (finrank ℝ E : ℝ≥0) < p) (hs : Bornology.IsBounded s) :
    eLpNorm u ⊤ μ ≤ morreyEssSupConst E μ s p * eLpNorm (fderiv ℝ u) p μ := by
  have := secondCountableTopologyEither_of_left E F
  rw [eLpNorm_exponent_top hu.continuous.aestronglyMeasurable]
  refine eLpNormEssSup_le_of_ae_enorm_bound (.of_forall fun x ↦ ?_)
  by_cases hux : u x = 0
  · simp [hux]
  -- Compare `x` with a point `z` where `u` vanishes, within `diam s` of `x`.
  obtain ⟨z, huz, hxz⟩ := exists_eq_zero_dist_le_diam hu.continuous h2u hs hux
  calc ‖u x‖ₑ = ‖u x - u z‖ₑ := by rw [huz, sub_zero]
    _ ≤ _ := enorm_sub_le_morreyConst_mul_rpow_mul_eLpNorm_fderiv μ hu hp x z
    _ ≤ _ := by
      rw [coe_morreyEssSupConst μ hp.le, ← edist_eq_enorm_sub]
      gcongr
      · exact one_sub_finrank_div_nonneg hp.le
      · exact (edist_le_ofReal diam_nonneg).2 hxz

end Morrey

end MeasureTheory

end
