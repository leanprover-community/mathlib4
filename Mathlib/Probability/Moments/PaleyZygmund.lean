/-
Copyright (c) 2026 Yanxin Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yanxin Zhou, Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The Paley–Zygmund inequality

The Paley–Zygmund inequality bounds from below the probability that a nonnegative random variable
`Z` exceeds a fraction of its mean: for `0 ≤ θ ≤ 1`,
`(1 - θ) ^ 2 * 𝔼[Z] ^ 2 / 𝔼[Z ^ 2] ≤ ℙ(θ * 𝔼[Z] < Z)`.

We prove it in the following generality. For a function `Y` with values in a normed lattice with
solid norm and nonnegative integral, Hölder's inequality on the set `{Y ≤ 0}ᶜ` gives
`‖∫ Y‖ ≤ ‖Y‖_{L^p({Y ≤ 0}ᶜ)} * μ {Y ≤ 0}ᶜ ^ (1 - 1 / p)`. For real `Y = Z - a` this yields, for
`1 ≤ p < ∞` and `0 ≤ a ≤ 𝔼[Z] / ℙ(0 < Z)`,
`(𝔼[Z] - a * ℙ(0 < Z)) ^ p / 𝔼[Z ^ p] ≤ ℙ(a < Z) ^ (p - 1)`,
from which the usual forms follow by taking `a = θ * 𝔼[Z]` or `a = θ * 𝔼[Z] / ℙ(0 < Z)`.

All statements are written with real division, so that no positivity assumption on the
denominators is needed: when a denominator vanishes, the left-hand side is `0` and the inequality
is trivial.

## Main results

* `MeasureTheory.enorm_integral_le_eLpNorm_restrict_mul_rpow_measure`: the Hölder bound underlying
  the Paley–Zygmund inequality, for functions with values in a normed lattice with solid norm.
* `MeasureTheory.rpow_integral_le_setIntegral_rpow_mul_rpow_meas`: its real-valued version.
* `ProbabilityTheory.rpow_div_integral_rpow_le_rpow_meas_gt`: the `L^p` Paley–Zygmund inequality
  with an arbitrary threshold `a`, and `ProbabilityTheory.sq_div_le_meas_gt`: its `L^2` version,
  with the sharper denominator `𝔼[Z ^ 2] - 2 * a * 𝔼[Z] + a ^ 2 * ℙ(0 < Z)`.
* `ProbabilityTheory.rpow_div_integral_rpow_le_rpow_meas_gt_mul_integral_div_meas`,
  `ProbabilityTheory.sq_mul_sq_div_le_meas_gt_mul_integral_div_meas`: the `L^p` and `L^2`
  Paley–Zygmund inequalities for the threshold `θ * (𝔼[Z] / ℙ(0 < Z))`, where `𝔼[Z] / ℙ(0 < Z)` is
  the expectation of `Z` conditioned on `0 < Z`; the `L^2` version has the sharper denominator
  `𝔼[Z ^ 2] - θ * (2 - θ) * 𝔼[Z] ^ 2 / ℙ(0 < Z)`.
* `ProbabilityTheory.rpow_div_integral_rpow_le_rpow_meas_gt_mul_integral`,
  `ProbabilityTheory.sq_mul_sq_div_integral_sq_le_meas_gt_mul_integral`: the `L^p` and `L^2`
  Paley–Zygmund inequalities for the threshold `θ * 𝔼[Z]`.

## References

* [Wikipedia, *Paley–Zygmund inequality*](https://en.wikipedia.org/wiki/Paley–Zygmund_inequality)
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {p : ℝ≥0∞}

namespace MeasureTheory

section SolidNorm

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E] [HasSolidNorm E]
  [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] {Y : Ω → E}

/-- The Hölder bound underlying the Paley–Zygmund inequality: if `Y` takes values in a normed
lattice with solid norm and has nonnegative integral, then the norm of its integral is controlled by
its `L^p` norm on the set `{Y ≤ 0}ᶜ` and the measure of that set. No integrability assumption is
needed, since the integral of a non-integrable function is `0`. -/
theorem enorm_integral_le_eLpNorm_restrict_mul_rpow_measure (h0 : 0 ≤ ∫ ω, Y ω ∂μ) (hp : 1 ≤ p) :
    ‖∫ ω, Y ω ∂μ‖ₑ ≤ eLpNorm Y p (μ.restrict {ω | Y ω ≤ 0}ᶜ) *
      μ {ω | Y ω ≤ 0}ᶜ ^ (1 - 1 / p.toReal) := by
  by_cases! hY : ¬ Integrable Y μ
  · simp [integral_undef hY]
  calc
    ‖∫ ω, Y ω ∂μ‖ₑ ≤ ‖∫ ω in {ω | Y ω ≤ 0}ᶜ, Y ω ∂μ‖ₑ :=
      enorm_le_iff_norm_le.2 <| norm_le_norm_of_abs_le_abs <|
        abs_le_abs_of_nonneg h0 (integral_le_setIntegral_compl_setOf_le_zero hY)
    _ ≤ eLpNorm Y 1 (μ.restrict {ω | Y ω ≤ 0}ᶜ) :=
      (enorm_integral_le_lintegral_enorm _).trans lintegral_enorm_le_eLpNorm_one
    _ ≤ _ := (eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos hp zero_lt_one).trans_eq (by simp)

end SolidNorm

section Real

variable [IsFiniteMeasure μ] {Y : Ω → ℝ}

/-- The Hölder bound underlying the Paley–Zygmund inequality, for real functions: if `Y ∈ L^p` has
nonnegative integral, where `1 ≤ p < ∞`, then
`(∫ Y) ^ p ≤ (∫ Y ^ p over {0 < Y}) * μ {0 < Y} ^ (p - 1)`. -/
theorem rpow_integral_le_setIntegral_rpow_mul_rpow_meas (hY : MemLp Y p μ)
    (h0 : 0 ≤ ∫ ω, Y ω ∂μ) (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    (∫ ω, Y ω ∂μ) ^ p.toReal ≤
      (∫ ω in {ω | 0 < Y ω}, Y ω ^ p.toReal ∂μ) * μ.real {ω | 0 < Y ω} ^ (p.toReal - 1) := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp'
  have hp1 : 0 ≤ p.toReal - 1 := sub_nonneg.2 (ENNReal.toReal_mono hp' hp)
  have hs : {ω | Y ω ≤ 0}ᶜ = {ω | 0 < Y ω} := by ext; simp
  -- on `{0 < Y}`, `Y ^ p = ‖Y‖ ^ p`
  rw [← setIntegral_congr_fun₀ (nullMeasurableSet_lt aemeasurable_const hY.aemeasurable)
    fun ω hω ↦ congrArg (· ^ p.toReal) (Real.norm_of_nonneg hω.le)]
  -- the general inequality raised to the power `p`, with both sides converted to real numbers
  have key :=
    ENNReal.rpow_le_rpow (enorm_integral_le_eLpNorm_restrict_mul_rpow_measure h0 hp) hp0.le
  rw [hs, ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_sub_div hp0.ne',
    div_mul_cancel₀ _ hp0.ne', (hY.restrict _).rpow_eLpNorm_eq_integral_rpow_norm hp₀ hp',
    Real.enorm_eq_ofReal h0, ENNReal.ofReal_rpow_of_nonneg h0 hp0.le, ← ofReal_measureReal,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hp1, ← ENNReal.ofReal_mul (by positivity)] at key
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 key

end Real

end MeasureTheory

namespace ProbabilityTheory

variable {Z : Ω → ℝ} {a θ : ℝ}

-- A nonnegative function vanishes off the set where it is positive.
private theorem ae_eq_zero_of_not_pos_aux (hZ : 0 ≤ᵐ[μ] Z) : ∀ᵐ ω ∂μ, ω ∉ {ω | 0 < Z ω} → Z ω = 0 :=
  hZ.mono fun _ hω hω' ↦ (not_lt.1 hω').antisymm hω

section FiniteMeasure

variable [IsFiniteMeasure μ]

-- For `Z ≥ 0`, `𝔼[Z] / ℙ(0 < Z) * ℙ(0 < Z) = 𝔼[Z]`, since `𝔼[Z] = 0` when `ℙ(0 < Z) = 0`.
private theorem integral_div_meas_mul_meas_aux (hZ : 0 ≤ᵐ[μ] Z) :
    (∫ ω, Z ω ∂μ) / μ.real {ω | 0 < Z ω} * μ.real {ω | 0 < Z ω} = ∫ ω, Z ω ∂μ :=
  div_mul_cancel_of_imp fun h ↦ integral_eq_zero_of_ae <|
    (measure_eq_zero_iff_ae_notMem.1 ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 h)).mp
      (ae_eq_zero_of_not_pos_aux hZ)

-- Auxiliary form of the Paley–Zygmund inequality, with the integral of `(Z - a) ^ p` over
-- `{a < Z}` on the right-hand side.
private theorem rpow_le_setIntegral_rpow_sub_mul_rpow_meas_aux (hZ : 0 ≤ᵐ[μ] Z)
    (hZp : MemLp Z p μ) (hp : 1 ≤ p) (hp' : p ≠ ∞) (ha : 0 ≤ a)
    (haZ : a ≤ (∫ ω, Z ω ∂μ) / μ.real {ω | 0 < Z ω}) :
    (∫ ω, Z ω ∂μ - a * μ.real {ω | 0 < Z ω}) ^ p.toReal ≤
      (∫ ω in {ω | a < Z ω}, (Z ω - a) ^ p.toReal ∂μ) * μ.real {ω | a < Z ω} ^ (p.toReal - 1) := by
  have hsub : {ω | a < Z ω} ⊆ {ω | 0 < Z ω} := fun ω hω ↦ ha.trans_lt hω
  have hint : ∫ ω in {ω | 0 < Z ω}, (Z ω - a) ∂μ = ∫ ω, Z ω ∂μ - a * μ.real {ω | 0 < Z ω} := by
    rw [integral_sub (hZp.integrable hp).integrableOn (integrableOn_const (by finiteness)),
      setIntegral_const, smul_eq_mul, mul_comm a,
      setIntegral_eq_integral_of_ae_compl_eq_zero (ae_eq_zero_of_not_pos_aux hZ)]
  have hT : (μ.restrict {ω | 0 < Z ω}).real {ω | a < Z ω} = μ.real {ω | a < Z ω} :=
    congrArg ENNReal.toReal (Measure.restrict_eq_self μ hsub)
  have h0 : 0 ≤ ∫ ω in {ω | 0 < Z ω}, (Z ω - a) ∂μ :=
    hint ▸ sub_nonneg.2 (mul_le_of_le_div₀ (integral_nonneg_of_ae hZ) measureReal_nonneg haZ)
  simpa [hint, Measure.restrict_restrict_of_subset hsub, hT] using
    rpow_integral_le_setIntegral_rpow_mul_rpow_meas
      ((hZp.sub (memLp_const a)).restrict {ω | 0 < Z ω}) h0 hp hp'

/-- **Paley–Zygmund inequality**, `L^p` version with an arbitrary threshold: if `Z ≥ 0` is in
`L^p` for some `1 ≤ p < ∞` and `0 ≤ a ≤ 𝔼[Z] / ℙ(0 < Z)`, then
`(𝔼[Z] - a * ℙ(0 < Z)) ^ p / 𝔼[Z ^ p] ≤ ℙ(a < Z) ^ (p - 1)`.

Taking `p = 2` and `a = θ * 𝔼[Z]` on a probability space recovers the classical form
`(1 - θ) ^ 2 * 𝔼[Z] ^ 2 / 𝔼[Z ^ 2] ≤ ℙ(θ * 𝔼[Z] < Z)`, see
`sq_mul_sq_div_integral_sq_le_meas_gt_mul_integral`; for `p = 2`, `sq_div_le_meas_gt`
has the sharper denominator `𝔼[Z ^ 2] - 2 * a * 𝔼[Z] + a ^ 2 * ℙ(0 < Z)`. -/
theorem rpow_div_integral_rpow_le_rpow_meas_gt (hZ : 0 ≤ᵐ[μ] Z) (hZp : MemLp Z p μ)
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (ha : 0 ≤ a) (haZ : a ≤ (∫ ω, Z ω ∂μ) / μ.real {ω | 0 < Z ω}) :
    (∫ ω, Z ω ∂μ - a * μ.real {ω | 0 < Z ω}) ^ p.toReal / ∫ ω, Z ω ^ p.toReal ∂μ ≤
      μ.real {ω | a < Z ω} ^ (p.toReal - 1) := by
  have hZpi : Integrable (fun ω ↦ Z ω ^ p.toReal) μ :=
    hZp.integrable_norm_rpow'.congr (hZ.mono fun ω hω ↦ by simp [Real.norm_of_nonneg hω])
  refine div_le_of_le_mul₀ (integral_nonneg_of_ae (hZ.mono fun ω hω ↦ Real.rpow_nonneg hω _))
    (by positivity)
    ((rpow_le_setIntegral_rpow_sub_mul_rpow_meas_aux hZ hZp hp hp' ha haZ).trans ?_)
  rw [mul_comm, ← integral_indicator₀ (nullMeasurableSet_lt aemeasurable_const hZp.aemeasurable)]
  gcongr _ * ?_
  -- on `{a < Z}` we have `(Z - a) ^ p ≤ Z ^ p`, and off it `0 ≤ Z ^ p`
  exact integral_mono_of_nonneg
    (.of_forall <| Set.indicator_nonneg fun ω hω ↦ Real.rpow_nonneg (sub_pos.2 hω).le _) hZpi
    (hZ.mono fun ω hω ↦ Set.indicator_apply_le'
      (fun hω' ↦ Real.rpow_le_rpow (sub_pos.2 hω').le (sub_le_self _ ha) ENNReal.toReal_nonneg)
      fun _ ↦ Real.rpow_nonneg hω _)

-- For `Z ≥ 0` in `L^2`, the integral of `(Z - a) ^ 2` over `{0 < Z}` is
-- `𝔼[Z ^ 2] - 2 * a * 𝔼[Z] + a ^ 2 * ℙ(0 < Z)`.
private theorem setIntegral_sq_sub_aux (hZ : 0 ≤ᵐ[μ] Z) (hZ2 : MemLp Z 2 μ) :
    ∫ ω in {ω | 0 < Z ω}, (Z ω - a) ^ 2 ∂μ =
      ∫ ω, Z ω ^ 2 ∂μ - 2 * a * ∫ ω, Z ω ∂μ + a ^ 2 * μ.real {ω | 0 < Z ω} := by
  have hZ0 := ae_eq_zero_of_not_pos_aux hZ
  have hsq : Integrable (fun ω ↦ Z ω ^ 2) μ := by
    simpa [sq_abs] using hZ2.integrable_norm_pow'
  have h1 : IntegrableOn (fun ω ↦ 2 * Z ω * a) {ω | 0 < Z ω} μ :=
    (((hZ2.integrable one_le_two).const_mul 2).mul_const a).integrableOn
  have h2 : IntegrableOn (fun ω ↦ Z ω ^ 2 - 2 * Z ω * a) {ω | 0 < Z ω} μ :=
    hsq.integrableOn.sub h1
  simp_rw [sub_sq]
  rw [integral_add h2 (integrableOn_const (by finiteness)), integral_sub hsq.integrableOn h1,
    integral_mul_const, integral_const_mul, setIntegral_const,
    setIntegral_eq_integral_of_ae_compl_eq_zero hZ0,
    setIntegral_eq_integral_of_ae_compl_eq_zero (hZ0.mono fun ω h hω ↦ by simp [h hω]),
    smul_eq_mul]
  ring

/-- **Paley–Zygmund inequality**, `L^2` version with an arbitrary threshold and sharp
denominator: if `Z ≥ 0` is in `L^2` and `0 ≤ a ≤ 𝔼[Z] / ℙ(0 < Z)`, then
`(𝔼[Z] - a * ℙ(0 < Z)) ^ 2 / (𝔼[Z ^ 2] - 2 * a * 𝔼[Z] + a ^ 2 * ℙ(0 < Z)) ≤ ℙ(a < Z)`. -/
theorem sq_div_le_meas_gt (hZ : 0 ≤ᵐ[μ] Z) (hZ2 : MemLp Z 2 μ) (ha : 0 ≤ a)
    (haZ : a ≤ (∫ ω, Z ω ∂μ) / μ.real {ω | 0 < Z ω}) :
    (∫ ω, Z ω ∂μ - a * μ.real {ω | 0 < Z ω}) ^ 2 /
      (∫ ω, Z ω ^ 2 ∂μ - 2 * a * ∫ ω, Z ω ∂μ + a ^ 2 * μ.real {ω | 0 < Z ω}) ≤
        μ.real {ω | a < Z ω} := by
  have key := rpow_le_setIntegral_rpow_sub_mul_rpow_meas_aux hZ hZ2 one_le_two
    ENNReal.ofNat_ne_top ha haZ
  norm_num at key
  have hsq : Integrable (fun ω ↦ (Z ω - a) ^ 2) μ := by
    simpa [sq_abs] using (hZ2.sub (memLp_const a)).integrable_norm_pow'
  -- the denominator is the integral of `(Z - a) ^ 2` over `{0 < Z}`
  rw [← setIntegral_sq_sub_aux hZ hZ2]
  refine div_le_of_le_mul₀ (integral_nonneg fun ω ↦ sq_nonneg _) measureReal_nonneg (key.trans ?_)
  rw [mul_comm]
  gcongr _ * ?_
  exact setIntegral_mono_set hsq.integrableOn (.of_forall fun ω ↦ sq_nonneg _)
    (.of_forall fun ω hω ↦ ha.trans_lt hω)

/-- **Paley–Zygmund inequality**, `L^p` version with the conditional expectation
`𝔼[Z] / ℙ(0 < Z)` of `Z` given `0 < Z` as threshold: if `Z ≥ 0` is in `L^p` for some `1 ≤ p < ∞`
and `0 ≤ θ ≤ 1`, then
`(1 - θ) ^ p * 𝔼[Z] ^ p / 𝔼[Z ^ p] ≤ ℙ(θ * (𝔼[Z] / ℙ(0 < Z)) < Z) ^ (p - 1)`.

On a probability space `𝔼[Z] ≤ 𝔼[Z] / ℙ(0 < Z)`, so the event on the right-hand side is contained
in `{θ * 𝔼[Z] < Z}` and this version dominates
`rpow_div_integral_rpow_le_rpow_meas_gt_mul_integral`. -/
theorem rpow_div_integral_rpow_le_rpow_meas_gt_mul_integral_div_meas (hZ : 0 ≤ᵐ[μ] Z)
    (hZp : MemLp Z p μ) (hp : 1 ≤ p) (hp' : p ≠ ∞) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (1 - θ) ^ p.toReal * (∫ ω, Z ω ∂μ) ^ p.toReal / ∫ ω, Z ω ^ p.toReal ∂μ ≤
      μ.real {ω | θ * ((∫ ω, Z ω ∂μ) / μ.real {ω | 0 < Z ω}) < Z ω} ^ (p.toReal - 1) := by
  have hc : 0 ≤ (∫ ω, Z ω ∂μ) / μ.real {ω | 0 < Z ω} :=
    div_nonneg (integral_nonneg_of_ae hZ) measureReal_nonneg
  have := rpow_div_integral_rpow_le_rpow_meas_gt hZ hZp hp hp' (mul_nonneg hθ₀ hc)
    (mul_le_of_le_one_left hc hθ₁)
  rwa [mul_assoc θ, integral_div_meas_mul_meas_aux hZ, ← one_sub_mul,
    Real.mul_rpow (sub_nonneg.2 hθ₁) (integral_nonneg_of_ae hZ)] at this

/-- **Paley–Zygmund inequality**, `L^2` version with the conditional expectation
`𝔼[Z] / ℙ(0 < Z)` of `Z` given `0 < Z` as threshold and sharp denominator: if `Z ≥ 0` is in `L^2`
and `0 ≤ θ ≤ 1`, then
`(1 - θ) ^ 2 * 𝔼[Z] ^ 2 / (𝔼[Z ^ 2] - θ * (2 - θ) * 𝔼[Z] ^ 2 / ℙ(0 < Z)) ≤
  ℙ(θ * (𝔼[Z] / ℙ(0 < Z)) < Z)`.
Here `𝔼[Z] ^ 2 / ℙ(0 < Z) = 𝔼[Z] * 𝔼[Z ∣ 0 < Z]`, and the denominator is the integral of
`(Z - θ * 𝔼[Z ∣ 0 < Z]) ^ 2` over `{0 < Z}`, hence nonnegative. This is the "strengthened form" of
the Paley–Zygmund inequality of the Wikipedia article, with the sharp denominator of
`sq_div_le_meas_gt`; it dominates every other form of the inequality in this file. -/
theorem sq_mul_sq_div_le_meas_gt_mul_integral_div_meas (hZ : 0 ≤ᵐ[μ] Z)
    (hZ2 : MemLp Z 2 μ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (1 - θ) ^ 2 * (∫ ω, Z ω ∂μ) ^ 2 /
      (∫ ω, Z ω ^ 2 ∂μ - θ * (2 - θ) * (∫ ω, Z ω ∂μ) ^ 2 / μ.real {ω | 0 < Z ω}) ≤
        μ.real {ω | θ * ((∫ ω, Z ω ∂μ) / μ.real {ω | 0 < Z ω}) < Z ω} := by
  have hc : 0 ≤ (∫ ω, Z ω ∂μ) / μ.real {ω | 0 < Z ω} :=
    div_nonneg (integral_nonneg_of_ae hZ) measureReal_nonneg
  -- specialise `sq_div_le_meas_gt` to `a = θ * (𝔼[Z] / ℙ(0 < Z))` and rearrange
  grind [sq_div_le_meas_gt hZ hZ2 (mul_nonneg hθ₀ hc) (mul_le_of_le_one_left hc hθ₁),
    integral_div_meas_mul_meas_aux hZ]

end FiniteMeasure

section ZeroOrProbabilityMeasure

variable [IsZeroOrProbabilityMeasure μ]

-- For `Z ≥ 0` and `ℙ(0 < Z) ≤ 1`, `𝔼[Z] ≤ 𝔼[Z] / ℙ(0 < Z)`.
private theorem integral_le_integral_div_meas_aux (hZ : 0 ≤ᵐ[μ] Z) :
    ∫ ω, Z ω ∂μ ≤ (∫ ω, Z ω ∂μ) / μ.real {ω | 0 < Z ω} :=
  (integral_div_meas_mul_meas_aux hZ).symm.trans_le <|
    mul_le_of_le_one_right (div_nonneg (integral_nonneg_of_ae hZ) measureReal_nonneg)
      measureReal_le_one

/-- **Paley–Zygmund inequality**, `L^p` version: if `Z ≥ 0` is in `L^p` for some `1 ≤ p < ∞` and
`0 ≤ θ ≤ 1`, then `(1 - θ) ^ p * 𝔼[Z] ^ p / 𝔼[Z ^ p] ≤ ℙ(θ * 𝔼[Z] < Z) ^ (p - 1)`.

For `p = 2`, see `sq_mul_sq_div_integral_sq_le_meas_gt_mul_integral`; for the sharper
bound with the threshold `θ * (𝔼[Z] / ℙ(0 < Z))`, see
`rpow_div_integral_rpow_le_rpow_meas_gt_mul_integral_div_meas`. -/
theorem rpow_div_integral_rpow_le_rpow_meas_gt_mul_integral (hZ : 0 ≤ᵐ[μ] Z)
    (hZp : MemLp Z p μ) (hp : 1 ≤ p) (hp' : p ≠ ∞) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (1 - θ) ^ p.toReal * (∫ ω, Z ω ∂μ) ^ p.toReal / ∫ ω, Z ω ^ p.toReal ∂μ ≤
      μ.real {ω | θ * ∫ ω, Z ω ∂μ < Z ω} ^ (p.toReal - 1) :=
  -- `{θ * (𝔼[Z] / ℙ(0 < Z)) < Z} ⊆ {θ * 𝔼[Z] < Z}` since `𝔼[Z] ≤ 𝔼[Z] / ℙ(0 < Z)`
  (rpow_div_integral_rpow_le_rpow_meas_gt_mul_integral_div_meas hZ hZp hp hp' hθ₀
    hθ₁).trans <| Real.rpow_le_rpow measureReal_nonneg
      (measureReal_mono fun ω hω ↦
        (mul_le_mul_of_nonneg_left (integral_le_integral_div_meas_aux hZ) hθ₀).trans_lt hω)
      (sub_nonneg.2 (ENNReal.toReal_mono hp' hp))

/-- **Paley–Zygmund inequality**: if `Z ≥ 0` is in `L^2` and `0 ≤ θ ≤ 1`, then
`(1 - θ) ^ 2 * 𝔼[Z] ^ 2 / 𝔼[Z ^ 2] ≤ ℙ(θ * 𝔼[Z] < Z)`.

This is the inequality in its usual form; the other versions in this file generalize or sharpen it:
`sq_div_le_meas_gt` has an arbitrary threshold and a smaller denominator,
`sq_mul_sq_div_le_meas_gt_mul_integral_div_meas` uses the threshold
`θ * (𝔼[Z] / ℙ(0 < Z))`, and `rpow_div_integral_rpow_le_rpow_meas_gt_mul_integral` is the
`L^p` version. -/
theorem sq_mul_sq_div_integral_sq_le_meas_gt_mul_integral (hZ : 0 ≤ᵐ[μ] Z)
    (hZ2 : MemLp Z 2 μ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (1 - θ) ^ 2 * (∫ ω, Z ω ∂μ) ^ 2 / ∫ ω, Z ω ^ 2 ∂μ ≤ μ.real {ω | θ * ∫ ω, Z ω ∂μ < Z ω} := by
  simpa [show (2 : ℝ) - 1 = 1 by norm_num] using
    rpow_div_integral_rpow_le_rpow_meas_gt_mul_integral hZ hZ2 one_le_two
      ENNReal.ofNat_ne_top hθ₀ hθ₁

end ZeroOrProbabilityMeasure

end ProbabilityTheory
