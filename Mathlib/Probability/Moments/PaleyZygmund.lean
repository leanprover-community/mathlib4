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
`(1 - θ) ^ 2 * 𝔼[Z] ^ 2 ≤ 𝔼[Z ^ 2] * ℙ(θ * 𝔼[Z] < Z)`.

We prove it in the following generality. For a function `Y` with values in a normed lattice with
solid norm and nonnegative integral, Hölder's inequality on the set `{Y ≤ 0}ᶜ` gives
`‖∫ Y‖ ≤ ‖Y‖_{L^p({Y ≤ 0}ᶜ)} * μ {Y ≤ 0}ᶜ ^ (1 - 1 / p)`. For real `Y = Z - a` this yields, for
`1 ≤ p < ∞`, `0 ≤ a` and `a * ℙ(0 < Z) ≤ 𝔼[Z]`,
`(𝔼[Z] - a * ℙ(0 < Z)) ^ p ≤ 𝔼[Z ^ p] * ℙ(a < Z) ^ (p - 1)`,
from which the usual forms follow by taking `a = θ * 𝔼[Z]` or `a = θ * 𝔼[Z | 0 < Z]`.

## Main results

* `MeasureTheory.enorm_integral_le_eLpNorm_restrict_mul_rpow_measure`: the Hölder bound underlying
  the Paley–Zygmund inequality, for functions with values in a normed lattice with solid norm.
* `MeasureTheory.rpow_integral_le_setIntegral_rpow_mul_rpow_measureReal`: its real-valued version.
* `ProbabilityTheory.paley_zygmund_rpow`: the `L^p` Paley–Zygmund inequality with an arbitrary
  threshold `a`, and `ProbabilityTheory.paley_zygmund`: its `L^2` version, with the sharper
  denominator `𝔼[Z ^ 2] - 2 * a * 𝔼[Z] + a ^ 2 * ℙ(0 < Z)`.
* `ProbabilityTheory.paley_zygmund_rpow_mul_integral`,
  `ProbabilityTheory.paley_zygmund_mul_integral`: the `L^p` and `L^2` Paley–Zygmund inequalities
  for the threshold `θ * 𝔼[Z]`.
* `ProbabilityTheory.paley_zygmund_rpow_mul_integral_cond`,
  `ProbabilityTheory.paley_zygmund_mul_integral_cond`: the `L^p` and `L^2` Paley–Zygmund
  inequalities for the threshold `θ * 𝔼[Z | 0 < Z]`; the `L^2` version has the sharper denominator
  `𝔼[Z ^ 2] - θ * (2 - θ) * 𝔼[Z] ^ 2 / ℙ(0 < Z)`.

## References

* [Wikipedia, *Paley–Zygmund inequality*](https://en.wikipedia.org/wiki/Paley–Zygmund_inequality)
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {p : ℝ≥0∞}

namespace MeasureTheory

section OrderedBanach

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E] [IsOrderedAddMonoid E]
  [IsOrderedModule ℝ E] [OrderClosedTopology E] {Y : Ω → E}

/-- The integral of an integrable function is at most its integral over the set where it is not
nonpositive. -/
theorem integral_le_setIntegral_compl_setOf_le_zero (hY : Integrable Y μ) :
    ∫ ω, Y ω ∂μ ≤ ∫ ω in {ω | Y ω ≤ 0}ᶜ, Y ω ∂μ := by
  borelize E
  have hs : NullMeasurableSet {ω | Y ω ≤ 0} μ :=
    hY.aemeasurable.nullMeasurableSet_preimage isClosed_Iic.measurableSet
  refine integral_le_setIntegral hs.compl hY ?_
  rw [compl_compl]
  exact (ae_restrict_mem₀ hs).mono fun _ h ↦ h

end OrderedBanach

section SolidNorm

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E] [HasSolidNorm E]
  [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] {Y : Ω → E}

/-- The Hölder bound underlying the Paley–Zygmund inequality: if `Y` takes values in a normed
lattice with solid norm and has nonnegative integral, then the norm of its integral is controlled by
its `L^p` norm on the set `{Y ≤ 0}ᶜ` and the measure of that set. -/
theorem enorm_integral_le_eLpNorm_restrict_mul_rpow_measure (hY : Integrable Y μ)
    (h0 : 0 ≤ ∫ ω, Y ω ∂μ) (hp : 1 ≤ p) :
    ‖∫ ω, Y ω ∂μ‖ₑ ≤
      eLpNorm Y p (μ.restrict {ω | Y ω ≤ 0}ᶜ) * μ {ω | Y ω ≤ 0}ᶜ ^ (1 - 1 / p.toReal) := by
  have hle := integral_le_setIntegral_compl_setOf_le_zero hY
  calc ‖∫ ω, Y ω ∂μ‖ₑ ≤ ‖∫ ω in {ω | Y ω ≤ 0}ᶜ, Y ω ∂μ‖ₑ := by
        rw [← ofReal_norm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal
          (norm_le_norm_of_abs_le_abs (by rwa [abs_of_nonneg h0, abs_of_nonneg (h0.trans hle)]))
    _ ≤ ∫⁻ ω in {ω | Y ω ≤ 0}ᶜ, ‖Y ω‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm Y 1 (μ.restrict {ω | Y ω ≤ 0}ᶜ) :=
      (eLpNorm_one_eq_lintegral_enorm hY.1.restrict).symm
    _ ≤ _ := (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hY.1.restrict).trans_eq (by simp)

end SolidNorm

section Real

variable [IsFiniteMeasure μ] {Y : Ω → ℝ}

/-- The Hölder bound underlying the Paley–Zygmund inequality, for real functions: if `Y ∈ L^p` has
nonnegative integral, then `(∫ Y) ^ p ≤ (∫ Y ^ p over {0 < Y}) * μ {0 < Y} ^ (p - 1)`. -/
theorem rpow_integral_le_setIntegral_rpow_mul_rpow_measureReal (hY : MemLp Y p μ)
    (h0 : 0 ≤ ∫ ω, Y ω ∂μ) (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    (∫ ω, Y ω ∂μ) ^ p.toReal ≤
      (∫ ω in {ω | 0 < Y ω}, Y ω ^ p.toReal ∂μ) * μ.real {ω | 0 < Y ω} ^ (p.toReal - 1) := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp'
  have hp1 : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp' hp
  have hs : {ω | Y ω ≤ 0}ᶜ = {ω | 0 < Y ω} := by ext; simp
  have hsm : NullMeasurableSet {ω | 0 < Y ω} μ :=
    nullMeasurableSet_lt aemeasurable_const hY.aestronglyMeasurable.aemeasurable
  have hmem := ae_restrict_mem₀ hsm
  have hYp : IntegrableOn (fun ω ↦ Y ω ^ p.toReal) {ω | 0 < Y ω} μ :=
    (hY.integrable_norm_rpow hp₀ hp').integrableOn.congr
      (hmem.mono fun ω hω ↦ by simp [Real.norm_of_nonneg hω.le])
  have hl : ∫⁻ ω in {ω | 0 < Y ω}, ‖Y ω‖ₑ ^ p.toReal ∂μ =
      ENNReal.ofReal (∫ ω in {ω | 0 < Y ω}, Y ω ^ p.toReal ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hYp (hmem.mono fun ω hω ↦ Real.rpow_nonneg hω.le _)]
    exact lintegral_congr_ae (hmem.mono fun ω hω ↦ by
      simp only [Real.enorm_eq_ofReal hω.le, ENNReal.ofReal_rpow_of_nonneg hω.le hp0.le])
  have hYp0 : 0 ≤ ∫ ω in {ω | 0 < Y ω}, Y ω ^ p.toReal ∂μ :=
    setIntegral_nonneg_of_ae_restrict (hmem.mono fun ω hω ↦ Real.rpow_nonneg hω.le _)
  -- the general inequality raised to the power `p`
  have key := ENNReal.rpow_le_rpow
    (enorm_integral_le_eLpNorm_restrict_mul_rpow_measure (hY.integrable hp) h0 hp) hp0.le
  rw [hs, ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, sub_mul,
    one_div_mul_cancel hp0.ne', one_mul, eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp'
    hY.aestronglyMeasurable.restrict, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
    ENNReal.rpow_one, Real.enorm_eq_ofReal h0, ENNReal.ofReal_rpow_of_nonneg h0 hp0.le,
    ← ofReal_measureReal, ENNReal.ofReal_rpow_of_nonneg measureReal_nonneg (by linarith), hl,
    ← ENNReal.ofReal_mul hYp0] at key
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 key

end Real

end MeasureTheory

namespace ProbabilityTheory

section Cond

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set Ω} {f : Ω → E}

/-- The integral with respect to the conditional measure `μ[|s]` is the integral over `s` divided
by the measure of `s`. -/
theorem integral_cond (s : Set Ω) (f : Ω → E) :
    ∫ ω, f ω ∂μ[|s] = (μ.real s)⁻¹ • ∫ ω in s, f ω ∂μ := by
  rw [cond, integral_smul_measure, ENNReal.toReal_inv, measureReal_def]

/-- The integral over a set `s` of finite measure is the integral with respect to the conditional
measure `μ[|s]` multiplied by the measure of `s`. -/
theorem measureReal_smul_integral_cond (hs : μ s ≠ ∞) :
    μ.real s • ∫ ω, f ω ∂μ[|s] = ∫ ω in s, f ω ∂μ := by
  rw [integral_cond, smul_smul]
  obtain h | h := eq_or_ne (μ.real s) 0
  · rw [Measure.restrict_eq_zero.2 ((measureReal_eq_zero_iff hs).1 h), integral_zero_measure, h,
      smul_zero]
  · rw [mul_inv_cancel₀ h, one_smul]

end Cond

variable {Z : Ω → ℝ} {a θ : ℝ}

-- A nonnegative function vanishes off the set where it is positive.
private theorem ae_eq_zero_of_not_pos_aux (hZ : 0 ≤ᵐ[μ] Z) :
    ∀ᵐ ω ∂μ, ω ∉ {ω | 0 < Z ω} → Z ω = 0 :=
  hZ.mono fun _ hω hω' ↦ le_antisymm (not_lt.1 hω') hω

variable [IsFiniteMeasure μ]

-- For `Z ≥ 0`, `𝔼[Z | 0 < Z] * ℙ(0 < Z) = 𝔼[Z]`.
private theorem integral_cond_mul_measureReal_aux (hZ : 0 ≤ᵐ[μ] Z) :
    (∫ ω, Z ω ∂μ[|{ω | 0 < Z ω}]) * μ.real {ω | 0 < Z ω} = ∫ ω, Z ω ∂μ := by
  rw [mul_comm, ← smul_eq_mul, measureReal_smul_integral_cond (by finiteness),
    setIntegral_eq_integral_of_ae_compl_eq_zero (ae_eq_zero_of_not_pos_aux hZ)]

-- Auxiliary form of the Paley–Zygmund inequality, with the integral of `(Z - a) ^ p` over
-- `{a < Z}` on the right-hand side.
private theorem paley_zygmund_aux (hZ : 0 ≤ᵐ[μ] Z) (hZp : MemLp Z p μ) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (ha : 0 ≤ a) (haZ : a * μ.real {ω | 0 < Z ω} ≤ ∫ ω, Z ω ∂μ) :
    (∫ ω, Z ω ∂μ - a * μ.real {ω | 0 < Z ω}) ^ p.toReal ≤
      (∫ ω in {ω | a < Z ω}, (Z ω - a) ^ p.toReal ∂μ) * μ.real {ω | a < Z ω} ^ (p.toReal - 1) := by
  have hsub : {ω | a < Z ω} ⊆ {ω | 0 < Z ω} := fun ω hω ↦ ha.trans_lt hω
  have hZ0 := ae_eq_zero_of_not_pos_aux hZ
  have hint : ∫ ω in {ω | 0 < Z ω}, (Z ω - a) ∂μ = ∫ ω, Z ω ∂μ - a * μ.real {ω | 0 < Z ω} := by
    rw [integral_sub (hZp.integrable hp).integrableOn (integrableOn_const (by finiteness)),
      setIntegral_const, setIntegral_eq_integral_of_ae_compl_eq_zero hZ0, smul_eq_mul, mul_comm]
  have hT : (μ.restrict {ω | 0 < Z ω}).real {ω | a < Z ω} = μ.real {ω | a < Z ω} := by
    rw [measureReal_def, Measure.restrict_eq_self _ hsub, measureReal_def]
  have key := rpow_integral_le_setIntegral_rpow_mul_rpow_measureReal
    ((hZp.sub (memLp_const a)).restrict {ω | 0 < Z ω}) (hint ▸ sub_nonneg.2 haZ) hp hp'
  simp only [Pi.sub_apply, sub_pos] at key
  rwa [hint, Measure.restrict_restrict_of_subset hsub, hT] at key

/-- **Paley–Zygmund inequality**, `L^p` version with an arbitrary threshold: if `Z ≥ 0` is in
`L^p` for some `1 ≤ p < ∞` and `0 ≤ a` satisfies `a * ℙ(0 < Z) ≤ 𝔼[Z]`, then
`(𝔼[Z] - a * ℙ(0 < Z)) ^ p ≤ 𝔼[Z ^ p] * ℙ(a < Z) ^ (p - 1)`. -/
theorem paley_zygmund_rpow (hZ : 0 ≤ᵐ[μ] Z) (hZp : MemLp Z p μ) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (ha : 0 ≤ a) (haZ : a * μ.real {ω | 0 < Z ω} ≤ ∫ ω, Z ω ∂μ) :
    (∫ ω, Z ω ∂μ - a * μ.real {ω | 0 < Z ω}) ^ p.toReal ≤
      (∫ ω, Z ω ^ p.toReal ∂μ) * μ.real {ω | a < Z ω} ^ (p.toReal - 1) := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp'
  refine (paley_zygmund_aux hZ hZp hp hp' ha haZ).trans ?_
  gcongr ?_ * _
  have hmem : ∀ᵐ ω ∂μ.restrict {ω | a < Z ω}, ω ∈ {ω | a < Z ω} :=
    ae_restrict_mem₀ (nullMeasurableSet_lt aemeasurable_const hZp.aemeasurable)
  have hZpi : Integrable (fun ω ↦ Z ω ^ p.toReal) μ :=
    (hZp.integrable_norm_rpow hp₀ hp').congr (hZ.mono fun ω hω ↦ by simp [Real.norm_of_nonneg hω])
  calc ∫ ω in {ω | a < Z ω}, (Z ω - a) ^ p.toReal ∂μ
      ≤ ∫ ω in {ω | a < Z ω}, Z ω ^ p.toReal ∂μ :=
        setIntegral_mono_ae_restrict
          (((hZp.sub (memLp_const a)).integrable_norm_rpow hp₀ hp').integrableOn.congr
            (hmem.mono fun ω hω ↦ by simp [Real.norm_of_nonneg (sub_pos.2 hω).le]))
          hZpi.integrableOn
          (hmem.mono fun ω hω ↦ Real.rpow_le_rpow (sub_pos.2 hω).le (sub_le_self _ ha) hp0.le)
    _ ≤ ∫ ω, Z ω ^ p.toReal ∂μ :=
        setIntegral_le_integral hZpi (hZ.mono fun ω hω ↦ Real.rpow_nonneg hω _)

/-- **Paley–Zygmund inequality**, `L^p` version: if `Z ≥ 0` is in `L^p` for some `1 ≤ p < ∞` and
`0 ≤ θ ≤ 1`, then `((1 - θ) * 𝔼[Z]) ^ p ≤ 𝔼[Z ^ p] * ℙ(θ * 𝔼[Z] < Z) ^ (p - 1)`. -/
theorem paley_zygmund_rpow_mul_integral [IsProbabilityMeasure μ] (hZ : 0 ≤ᵐ[μ] Z)
    (hZp : MemLp Z p μ) (hp : 1 ≤ p) (hp' : p ≠ ∞) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    ((1 - θ) * ∫ ω, Z ω ∂μ) ^ p.toReal ≤
      (∫ ω, Z ω ^ p.toReal ∂μ) * μ.real {ω | θ * ∫ ω, Z ω ∂μ < Z ω} ^ (p.toReal - 1) := by
  have hm := integral_nonneg_of_ae hZ
  have hθm : θ * (∫ ω, Z ω ∂μ) * μ.real {ω | 0 < Z ω} ≤ θ * ∫ ω, Z ω ∂μ :=
    mul_le_of_le_one_right (mul_nonneg hθ₀ hm) measureReal_le_one
  refine (Real.rpow_le_rpow (mul_nonneg (sub_nonneg.2 hθ₁) hm) (by linarith)
    ENNReal.toReal_nonneg).trans (paley_zygmund_rpow hZ hZp hp hp' (mul_nonneg hθ₀ hm) ?_)
  exact hθm.trans (mul_le_of_le_one_left hm hθ₁)

/-- **Paley–Zygmund inequality**, `L^p` version with the conditional expectation
`𝔼[Z | 0 < Z] = 𝔼[Z] / ℙ(0 < Z)` as threshold: if `Z ≥ 0` is in `L^p` for some `1 ≤ p < ∞` and
`0 ≤ θ ≤ 1`, then `((1 - θ) * 𝔼[Z]) ^ p ≤ 𝔼[Z ^ p] * ℙ(θ * 𝔼[Z | 0 < Z] < Z) ^ (p - 1)`. -/
theorem paley_zygmund_rpow_mul_integral_cond (hZ : 0 ≤ᵐ[μ] Z) (hZp : MemLp Z p μ) (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    ((1 - θ) * ∫ ω, Z ω ∂μ) ^ p.toReal ≤
      (∫ ω, Z ω ^ p.toReal ∂μ) *
        μ.real {ω | θ * ∫ ω, Z ω ∂μ[|{ω | 0 < Z ω}] < Z ω} ^ (p.toReal - 1) := by
  have hm := integral_nonneg_of_ae hZ
  have hcond := integral_cond_mul_measureReal_aux hZ
  have hc := integral_nonneg_of_ae
    (hZ.filter_mono (cond_absolutelyContinuous (s := {ω | 0 < Z ω})).ae_le)
  have := paley_zygmund_rpow hZ hZp hp hp' (mul_nonneg hθ₀ hc)
    (by rw [mul_assoc, hcond]; exact mul_le_of_le_one_left hm hθ₁)
  rwa [mul_assoc, hcond, ← one_sub_mul] at this

/-- **Paley–Zygmund inequality**, `L^2` version with an arbitrary threshold and sharp
denominator: if `Z ≥ 0` is in `L^2` and `0 ≤ a` satisfies `a * ℙ(0 < Z) ≤ 𝔼[Z]`, then
`(𝔼[Z] - a * ℙ(0 < Z)) ^ 2 ≤ (𝔼[Z ^ 2] - 2 * a * 𝔼[Z] + a ^ 2 * ℙ(0 < Z)) * ℙ(a < Z)`. -/
theorem paley_zygmund (hZ : 0 ≤ᵐ[μ] Z) (hZ2 : MemLp Z 2 μ) (ha : 0 ≤ a)
    (haZ : a * μ.real {ω | 0 < Z ω} ≤ ∫ ω, Z ω ∂μ) :
    (∫ ω, Z ω ∂μ - a * μ.real {ω | 0 < Z ω}) ^ 2 ≤
      (∫ ω, Z ω ^ 2 ∂μ - 2 * a * ∫ ω, Z ω ∂μ + a ^ 2 * μ.real {ω | 0 < Z ω}) *
        μ.real {ω | a < Z ω} := by
  have hZi := hZ2.integrable one_le_two
  have hsq {f : Ω → ℝ} (hf : MemLp f 2 μ) : Integrable (fun ω ↦ f ω ^ 2) μ := by
    simpa [sq_abs] using hf.integrable_norm_pow' (p := 2)
  have hZ0 := ae_eq_zero_of_not_pos_aux hZ
  have key := paley_zygmund_aux hZ hZ2 one_le_two ENNReal.ofNat_ne_top ha haZ
  norm_num [Real.rpow_two] at key
  refine key.trans ?_
  gcongr ?_ * _
  calc ∫ ω in {ω | a < Z ω}, (Z ω - a) ^ 2 ∂μ
      ≤ ∫ ω in {ω | 0 < Z ω}, (Z ω - a) ^ 2 ∂μ :=
        setIntegral_mono_set (hsq (hZ2.sub (memLp_const a))).integrableOn
          (.of_forall fun ω ↦ sq_nonneg _) (.of_forall fun ω hω ↦ ha.trans_lt hω)
    _ = _ := by
        have h1 : IntegrableOn (fun ω ↦ 2 * Z ω * a) {ω | 0 < Z ω} μ :=
          ((hZi.const_mul 2).mul_const a).integrableOn
        have h2 : IntegrableOn (fun ω ↦ Z ω ^ 2 - 2 * Z ω * a) {ω | 0 < Z ω} μ :=
          (hsq hZ2).integrableOn.sub h1
        simp_rw [sub_sq]
        rw [integral_add h2 (integrableOn_const (by finiteness)),
          integral_sub (hsq hZ2).integrableOn h1,
          integral_mul_const, integral_const_mul, setIntegral_const,
          setIntegral_eq_integral_of_ae_compl_eq_zero hZ0,
          setIntegral_eq_integral_of_ae_compl_eq_zero (hZ0.mono fun ω h hω ↦ by simp [h hω]),
          smul_eq_mul]
        ring

/-- **Paley–Zygmund inequality**, `L^2` version with the conditional expectation
`𝔼[Z | 0 < Z] = 𝔼[Z] / ℙ(0 < Z)` as threshold and sharp denominator: if `Z ≥ 0` is in `L^2` and
`0 ≤ θ ≤ 1`, then
`(1 - θ) ^ 2 * 𝔼[Z] ^ 2 ≤ (𝔼[Z ^ 2] - θ * (2 - θ) * 𝔼[Z] * 𝔼[Z | 0 < Z]) * ℙ(θ * 𝔼[Z | 0 < Z] < Z)`.
Note that `𝔼[Z] * 𝔼[Z | 0 < Z] = 𝔼[Z] ^ 2 / ℙ(0 < Z)`. -/
theorem paley_zygmund_mul_integral_cond (hZ : 0 ≤ᵐ[μ] Z) (hZ2 : MemLp Z 2 μ) (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) :
    (1 - θ) ^ 2 * (∫ ω, Z ω ∂μ) ^ 2 ≤
      (∫ ω, Z ω ^ 2 ∂μ - θ * (2 - θ) * (∫ ω, Z ω ∂μ) * ∫ ω, Z ω ∂μ[|{ω | 0 < Z ω}]) *
        μ.real {ω | θ * ∫ ω, Z ω ∂μ[|{ω | 0 < Z ω}] < Z ω} := by
  have hm := integral_nonneg_of_ae hZ
  have hcond := integral_cond_mul_measureReal_aux hZ
  have hc := integral_nonneg_of_ae
    (hZ.filter_mono (cond_absolutelyContinuous (s := {ω | 0 < Z ω})).ae_le)
  have := paley_zygmund hZ hZ2 (mul_nonneg hθ₀ hc)
    (by rw [mul_assoc, hcond]; exact mul_le_of_le_one_left hm hθ₁)
  rw [mul_assoc, hcond] at this
  convert this using 2
  · ring
  · linear_combination (-θ ^ 2 * ∫ ω, Z ω ∂μ[|{ω | 0 < Z ω}]) * hcond

/-- **Paley–Zygmund inequality**: if `Z ≥ 0` is in `L^2` and `0 ≤ θ ≤ 1`, then
`(1 - θ) ^ 2 * 𝔼[Z] ^ 2 ≤ 𝔼[Z ^ 2] * ℙ(θ * 𝔼[Z] < Z)`. -/
theorem paley_zygmund_mul_integral [IsProbabilityMeasure μ] (hZ : 0 ≤ᵐ[μ] Z) (hZ2 : MemLp Z 2 μ)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (1 - θ) ^ 2 * (∫ ω, Z ω ∂μ) ^ 2 ≤
      (∫ ω, Z ω ^ 2 ∂μ) * μ.real {ω | θ * ∫ ω, Z ω ∂μ < Z ω} := by
  simpa [Real.rpow_two, mul_pow, show (2 : ℝ) - 1 = 1 by norm_num] using
    paley_zygmund_rpow_mul_integral hZ hZ2 one_le_two ENNReal.ofNat_ne_top hθ₀ hθ₁

end ProbabilityTheory
