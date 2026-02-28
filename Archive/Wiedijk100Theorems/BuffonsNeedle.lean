/-
Copyright (c) 2024 Enrico Z. Borba. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enrico Z. Borba
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Density
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Notation

/-!

# Freek № 99: Buffon's Needle

This file proves Theorem 99 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/), also
known as Buffon's Needle, which gives the probability of a needle of length `l > 0` crossing any
one of infinite vertical lines spaced out `d > 0` apart.

The two cases are proven in `buffon_short` and `buffon_long`.

## Overview of the Proof

We define a random variable `B : Ω → ℝ × ℝ` with a uniform distribution on `[-d/2, d/2] × [0, π]`.
This represents the needle's x-position and angle with respect to a vertical line. By symmetry, we
need to consider only a single vertical line positioned at `x = 0`. A needle therefore crosses the
vertical line if its projection onto the x-axis contains `0`.

We define a random variable `N : Ω → ℝ` that is `1` if the needle crosses a vertical line, and `0`
otherwise. This is defined as `fun ω => Set.indicator (needleProjX l (B ω).1 (B ω).2) 1 0`.
f
As in many references, the problem is split into two cases, `l ≤ d` (`buffon_short`), and `d ≤ l`
(`buffon_long`). For both cases, we show that
```lean
ℙ[N] = (d * π) ⁻¹ *
    ∫ θ in 0..π,
      ∫ x in Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2), 1
```
In the short case `l ≤ d`, we show that `[-l * θ.sin/2, l * θ.sin/2] ⊆ [-d/2, d/2]`
(`short_needle_inter_eq`), and therefore the inner integral simplifies to
```lean
∫ x in (-θ.sin * l / 2)..(θ.sin * l / 2), 1 = θ.sin * l
```
Which then concludes in the short case being `ℙ[N] = (2 * l) / (d * π)`.

In the long case, `l ≤ d` (`buffon_long`), we show the outer integral simplifies to
```lean
∫ θ in 0..π, min d (θ.sin * l)
```
which can be expanded to
```lean
2 * (
  ∫ θ in 0..(d / l).arcsin, min d (θ.sin * l) +
  ∫ θ in (d / l).arcsin..(π / 2), min d (θ.sin * l)
)
```
We then show the two integrals equal their respective values `l - √(l^2 - d^2)` and
`(π / 2 - (d / l).arcsin) * d`. Then with some algebra we conclude
```lean
ℙ[N] = (2 * l) / (d * π) - 2 / (d * π) * (√(l^2 - d^2) + d * (d / l).arcsin) + 1
```

## References

* https://en.wikipedia.org/wiki/Buffon%27s_needle_problem
* https://www.math.leidenuniv.nl/~hfinkeln/seminarium/stelling_van_Buffon.pdf
* https://www.isa-afp.org/entries/Buffons_Needle.html

-/

open MeasureTheory (MeasureSpace IsProbabilityMeasure Measure pdf.IsUniform)
open ProbabilityTheory Real

namespace BuffonsNeedle

variable
  /- Probability theory variables. -/
  {Ω : Type*} [MeasureSpace Ω]
  /- Buffon's needle variables. -/
  /-
    - `d > 0` is the distance between parallel lines.
    - `l > 0` is the length of the needle.
  -/
  (d l : ℝ)
  (hd : 0 < d)
  (hl : 0 < l)
  /- `B = (X, Θ)` is the joint random variable for the x-position and angle of the needle. -/
  (B : Ω → ℝ × ℝ)
  (hBₘ : Measurable B)
  /- `B` is uniformly distributed on `[-d/2, d/2] × [0, π]`. -/
  (hB : pdf.IsUniform B ((Set.Icc (-d / 2) (d / 2)) ×ˢ (Set.Icc 0 π)) ℙ)

/--
Projection of a needle onto the x-axis. The needle's center is at x-coordinate `x`, of length
`l` and angle `θ`. Note, `θ` is measured relative to the y-axis, that is, a vertical needle has
`θ = 0`.
-/
def needleProjX (x θ : ℝ) : Set ℝ := Set.Icc (x - θ.sin * l / 2) (x + θ.sin * l / 2)

/--
The indicator function of whether a needle at position `⟨x, θ⟩ : ℝ × ℝ` crosses the line `x = 0`.

In order to faithfully model the problem, we compose `needleCrossesIndicator` with a random
variable `B : Ω → ℝ × ℝ` with uniform distribution on `[-d/2, d/2] × [0, π]`. Then, by symmetry,
the probability that the needle crosses `x = 0`, is the same as the probability of a needle
crossing any of the infinitely spaced vertical lines distance `d` apart.
-/
noncomputable def needleCrossesIndicator (p : ℝ × ℝ) : ℝ :=
  Set.indicator (needleProjX l p.1 p.2) 1 0

/--
A random variable representing whether the needle crosses a line.

The line is at `x = 0`, and therefore a needle crosses the line if its projection onto the x-axis
contains `0`. This random variable is `1` if the needle crosses the line, and `0` otherwise.
-/
noncomputable def N : Ω → ℝ := needleCrossesIndicator l ∘ B

/--
The possible x-positions and angle relative to the y-axis of a needle.
-/
abbrev needleSpace : Set (ℝ × ℝ) := Set.Icc (-d / 2) (d / 2) ×ˢ Set.Icc 0 π

set_option backward.isDefEq.respectTransparency false in
include hd in
lemma volume_needleSpace : ℙ (needleSpace d) = ENNReal.ofReal (d * π) := by
  simp_rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, Real.volume_Icc,
    ENNReal.ofReal_mul hd.le]
  ring_nf

set_option backward.isDefEq.respectTransparency false in
lemma measurable_needleCrossesIndicator : Measurable (needleCrossesIndicator l) := by
  unfold needleCrossesIndicator
  refine Measurable.indicator measurable_const (IsClosed.measurableSet (IsClosed.and ?_ ?_)) <;>
    simp only [tsub_le_iff_right, zero_add, ← neg_le_iff_add_nonneg']
  · exact isClosed_le continuous_fst (by fun_prop)
  · exact isClosed_le continuous_fst.neg (by fun_prop)

lemma stronglyMeasurable_needleCrossesIndicator :
    MeasureTheory.StronglyMeasurable (needleCrossesIndicator l) := by
  refine stronglyMeasurable_iff_measurable_separable.mpr
    ⟨measurable_needleCrossesIndicator l, {0, 1}, ?separable⟩
  have range_finite : Set.Finite ({0, 1} : Set ℝ) := by
    simp only [Set.finite_singleton, Set.Finite.insert]
  refine ⟨range_finite.countable, ?subset_closure⟩
  rw [IsClosed.closure_eq range_finite.isClosed, Set.subset_def, Set.range]
  intro x ⟨p, hxp⟩
  by_cases hp : 0 ∈ needleProjX l p.1 p.2
  · simp_rw [needleCrossesIndicator, Set.indicator_of_mem hp, Pi.one_apply] at hxp
    apply Or.inr hxp.symm
  · simp_rw [needleCrossesIndicator, Set.indicator_of_notMem hp] at hxp
    apply Or.inl hxp.symm

include hd in
lemma integrable_needleCrossesIndicator :
    MeasureTheory.Integrable (needleCrossesIndicator l)
      (Measure.prod
        (Measure.restrict ℙ (Set.Icc (-d / 2) (d / 2)))
        (Measure.restrict ℙ (Set.Icc 0 π))) := by
  have needleCrossesIndicator_nonneg p : 0 ≤ needleCrossesIndicator l p := by
    apply Set.indicator_apply_nonneg
    simp only [Pi.one_apply, zero_le_one, implies_true]
  have needleCrossesIndicator_le_one p : needleCrossesIndicator l p ≤ 1 := by
    unfold needleCrossesIndicator
    by_cases hp : 0 ∈ needleProjX l p.1 p.2
    · simp_rw [Set.indicator_of_mem hp, Pi.one_apply, le_refl]
    · simp_rw [Set.indicator_of_notMem hp, zero_le_one]
  refine And.intro
    (stronglyMeasurable_needleCrossesIndicator l).aestronglyMeasurable
    ((MeasureTheory.hasFiniteIntegral_iff_norm (needleCrossesIndicator l)).mpr ?_)
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono (g := 1) ?le_const) ?lt_top
  case le_const =>
    intro p
    simp only [Real.norm_eq_abs, abs_of_nonneg (needleCrossesIndicator_nonneg _),
      ENNReal.ofReal_le_one, Pi.one_apply]
    exact needleCrossesIndicator_le_one p
  case lt_top =>
    simp_rw [Pi.one_apply, MeasureTheory.lintegral_const, one_mul, Measure.prod_restrict,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Measure.prod_prod, Real.volume_Icc,
      neg_div, sub_neg_eq_add, add_halves, sub_zero, ← ENNReal.ofReal_mul hd.le,
      ENNReal.ofReal_lt_top]

set_option linter.style.whitespace false in
include hd hB hBₘ in
/--
This is a common step in both the short and the long case to simplify the expectation of the
needle crossing a line to a double integral.
```lean
∫ (θ : ℝ) in Set.Icc 0 π,
  ∫ (x : ℝ) in Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2), 1
```
The domain of the inner integral is simpler in the short case, where the intersection is
equal to `Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2)` by `short_needle_inter_eq`.
-/
lemma buffon_integral :
    𝔼[N l B] = (d * π)⁻¹ *
      ∫ (θ : ℝ) in Set.Icc 0 π,
      ∫ (_ : ℝ) in Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2), 1 := by
  simp_rw [N, Function.comp_apply]
  rw [
    ← MeasureTheory.integral_map hBₘ.aemeasurable
      (stronglyMeasurable_needleCrossesIndicator l).aestronglyMeasurable,
    hB, ProbabilityTheory.cond, MeasureTheory.integral_smul_measure, volume_needleSpace d hd,
    ← ENNReal.ofReal_inv_of_pos (mul_pos hd Real.pi_pos),
    ENNReal.toReal_ofReal (inv_nonneg.mpr (mul_nonneg hd.le Real.pi_pos.le)), smul_eq_mul,
  ]
  refine mul_eq_mul_left_iff.mpr (Or.inl ?_)
  have : MeasureTheory.IntegrableOn (needleCrossesIndicator l)
      (Set.Icc (-d / 2) (d / 2) ×ˢ Set.Icc 0 π) := by
    simp_rw [MeasureTheory.IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict,
      integrable_needleCrossesIndicator d l hd]
  rw [Measure.volume_eq_prod, MeasureTheory.setIntegral_prod _ this,
    MeasureTheory.integral_integral_swap ?integrable]
  case integrable => simp_rw [Function.uncurry_def, Prod.mk.eta,
    integrable_needleCrossesIndicator d l hd]
  simp only [needleCrossesIndicator, needleProjX]
  have indicator_eq (x θ : ℝ) :
      Set.indicator (Set.Icc (x - θ.sin * l / 2) (x + θ.sin * l / 2)) 1 0 =
      Set.indicator (Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2)) (1 : ℝ → ℝ) x := by
    simp_rw [Set.indicator, Pi.one_apply, Set.mem_Icc, tsub_le_iff_right, zero_add, neg_mul]
    have :
        x ≤ Real.sin θ * l / 2 ∧ 0 ≤ x + Real.sin θ * l / 2 ↔
        -(Real.sin θ * l) / 2 ≤ x ∧ x ≤ Real.sin θ * l / 2 := by
      rw [neg_div, and_comm, ← tsub_le_iff_right, zero_sub]
    by_cases h : x ≤ Real.sin θ * l / 2 ∧ 0 ≤ x + Real.sin θ * l / 2
    · rw [if_pos h, if_pos (this.mp h)]
    · rw [if_neg h, if_neg (this.not.mp h)]
  simp_rw [indicator_eq, MeasureTheory.setIntegral_indicator measurableSet_Icc, Pi.one_apply]

include hl in
/--
From `buffon_integral`, in both the short and the long case, we have
```lean
𝔼[N l B] = (d * π)⁻¹ *
  ∫ (θ : ℝ) in Set.Icc 0 π,
    ∫ (x : ℝ) in Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2), 1
```
With this lemma, in the short case, the inner integral's domain simplifies to
`Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2)`.
-/
lemma short_needle_inter_eq (h : l ≤ d) (θ : ℝ) :
    Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2) =
    Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2) := by
  rw [Set.Icc_inter_Icc, max_div_div_right zero_le_two,
    min_div_div_right zero_le_two, neg_mul, max_neg_neg, mul_comm,
    min_eq_right ((mul_le_of_le_one_right hl.le θ.sin_le_one).trans h)]

set_option backward.isDefEq.respectTransparency false in
include hd hBₘ hB hl in
/--
Buffon's Needle, the short case (`l ≤ d`). The probability of the needle crossing a line
equals `(2 * l) / (d * π)`.
-/
theorem buffon_short (h : l ≤ d) : ℙ[N l B] = (2 * l) * (d * π)⁻¹ := by
  simp_rw [buffon_integral d l hd B hBₘ hB, short_needle_inter_eq d l hl h _,
    MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
    Real.volume_Icc, smul_eq_mul, mul_one, mul_comm (d * π)⁻¹ _,
    mul_eq_mul_right_iff]
  apply Or.inl
  ring_nf
  have : ∀ᵐ θ, θ ∈ Set.Icc 0 π → ENNReal.toReal (ENNReal.ofReal (θ.sin * l)) = θ.sin * l := by
    have (θ : ℝ) (hθ : θ ∈ Set.Icc 0 π) : 0 ≤ θ.sin * l :=
      mul_nonneg (Real.sin_nonneg_of_mem_Icc hθ) hl.le
    simp_rw [ENNReal.toReal_ofReal_eq_iff, MeasureTheory.ae_of_all _ this]
  simp_rw [MeasureTheory.setIntegral_congr_ae measurableSet_Icc this,
    ← smul_eq_mul, integral_smul_const, smul_eq_mul, mul_comm, mul_eq_mul_left_iff,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_sin, Real.cos_zero, Real.cos_pi, sub_neg_eq_add, one_add_one_eq_two, true_or]

/--
The integrand in the long case is `min d (θ.sin * l)` and its integrability is necessary for
the integral lemmas below.
-/
lemma intervalIntegrable_min_const_sin_mul (a b : ℝ) :
    IntervalIntegrable (fun (θ : ℝ) => min d (θ.sin * l)) ℙ a b := by
  apply Continuous.intervalIntegrable (by fun_prop)

/--
This equality is useful since `θ.sin` is increasing in `0..π / 2` (but not in `0..π`).
Then, `∫ θ in 0..π / 2, min d (θ.sin * l)` can be split into two adjacent integrals, at the
point where `d = θ.sin * l`, which is `θ = (d / l).arcsin`.
-/
lemma integral_min_eq_two_mul :
    ∫ θ in 0..π, min d (θ.sin * l) = 2 * ∫ θ in 0..π / 2, min d (θ.sin * l) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2) (c := π)]
  conv => lhs; arg 2; arg 1; intro θ; rw [← neg_neg θ, Real.sin_neg]
  · simp_rw [intervalIntegral.integral_comp_neg fun θ => min d (-θ.sin * l), ← Real.sin_add_pi,
      intervalIntegral.integral_comp_add_right (fun θ => min d (θ.sin * l)), neg_add_cancel,
      (by ring : -(π / 2) + π = π / 2), two_mul]
  all_goals exact intervalIntegrable_min_const_sin_mul d l _ _

set_option backward.isDefEq.respectTransparency false in
include hd hl in
/--
The first of two adjacent integrals in the long case. In the range `0..(d / l).arcsin`, we
have that `θ.sin * l ≤ d`, and thus the integral is `∫ θ in 0..(d / l).arcsin, θ.sin * l`.
-/
lemma integral_zero_to_arcsin_min :
    ∫ θ in 0..(d / l).arcsin, min d (θ.sin * l) = (1 - √(1 - (d / l) ^ 2)) * l := by
  have : Set.EqOn (fun θ => min d (θ.sin * l)) (Real.sin · * l) (Set.uIcc 0 (d / l).arcsin) := by
    intro θ ⟨hθ₁, hθ₂⟩
    have : 0 ≤ (d / l).arcsin := Real.arcsin_nonneg.mpr (div_nonneg hd.le hl.le)
    simp only [min_eq_left this, max_eq_right this] at hθ₁ hθ₂
    have hθ_mem : θ ∈ Set.Ioc (-(π / 2)) (π / 2) := by
      exact ⟨lt_of_lt_of_le (neg_lt_zero.mpr (div_pos Real.pi_pos two_pos)) hθ₁,
        le_trans hθ₂ (d / l).arcsin_mem_Icc.right⟩
    simp_rw [min_eq_right ((le_div_iff₀ hl).mp ((Real.le_arcsin_iff_sin_le' hθ_mem).mp hθ₂))]
  rw [intervalIntegral.integral_congr this, intervalIntegral.integral_mul_const, integral_sin,
    Real.cos_zero, Real.cos_arcsin]

include hl in
/--
The second of two adjacent integrals in the long case. In the range `(d / l).arcsin..(π / 2)`, we
have that `d ≤ θ.sin * l`, and thus the integral is `∫ θ in (d / l).arcsin..(π / 2), d`.
-/
lemma integral_arcsin_to_pi_div_two_min (h : d ≤ l) :
    ∫ θ in (d / l).arcsin..(π / 2), min d (θ.sin * l) = (π / 2 - (d / l).arcsin) * d := by
  have : Set.EqOn (fun θ => min d (θ.sin * l)) (fun _ => d) (Set.uIcc (d / l).arcsin (π / 2)) := by
    intro θ ⟨hθ₁, hθ₂⟩
    wlog hθ_ne_pi_div_two : θ ≠ π / 2
    · simp only [ne_eq, not_not] at hθ_ne_pi_div_two
      simp only [hθ_ne_pi_div_two, Real.sin_pi_div_two, one_mul, min_eq_left h]
    simp only [min_eq_left (d / l).arcsin_le_pi_div_two,
      max_eq_right (d / l).arcsin_le_pi_div_two] at hθ₁ hθ₂
    have hθ_mem : θ ∈ Set.Ico (-(π / 2)) (π / 2) := by
      exact ⟨le_trans (Real.arcsin_mem_Icc (d / l)).left hθ₁, lt_of_le_of_ne hθ₂ hθ_ne_pi_div_two⟩
    simp_rw [min_eq_left ((div_le_iff₀ hl).mp ((Real.arcsin_le_iff_le_sin' hθ_mem).mp hθ₁))]
  rw [intervalIntegral.integral_congr this, intervalIntegral.integral_const, smul_eq_mul]

set_option linter.style.whitespace false in
include hd hBₘ hB hl in
/-- Buffon's Needle, the long case (`d ≤ l`) -/
theorem buffon_long (h : d ≤ l) :
    ℙ[N l B] = (2 * l) / (d * π) - 2 / (d * π) * (√(l ^ 2 - d ^ 2) + d * (d / l).arcsin) + 1 := by
  simp only [
    buffon_integral d l hd B hBₘ hB, MeasureTheory.integral_const, smul_eq_mul, mul_one,
    MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, Set.Icc_inter_Icc, Real.volume_Icc,
    min_div_div_right zero_le_two d, max_div_div_right zero_le_two (-d),
    div_sub_div_same, neg_mul, max_neg_neg, sub_neg_eq_add, ← mul_two,
    mul_div_cancel_right₀ (min d (Real.sin _ * l)) two_ne_zero, MeasureTheory.measureReal_def
  ]
  have : ∀ᵐ θ, θ ∈ Set.Icc 0 π →
      ENNReal.toReal (ENNReal.ofReal (min d (θ.sin * l))) = min d (θ.sin * l) := by
    have (θ : ℝ) (hθ : θ ∈ Set.Icc 0 π) : 0 ≤ min d (θ.sin * l) := by
      by_cases! h : d ≤ θ.sin * l
      · rw [min_eq_left h]; exact hd.le
      · rw [min_eq_right h.le]; exact mul_nonneg (Real.sin_nonneg_of_mem_Icc hθ) hl.le
    simp_rw [ENNReal.toReal_ofReal_eq_iff, MeasureTheory.ae_of_all _ this]
  rw [MeasureTheory.setIntegral_congr_ae measurableSet_Icc this,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le Real.pi_pos.le, integral_min_eq_two_mul,
    ← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_min_const_sin_mul d l _ _) (intervalIntegrable_min_const_sin_mul d l _ _),
    integral_zero_to_arcsin_min d l hd hl, integral_arcsin_to_pi_div_two_min d l hl h]
  field_simp
  simp (disch := positivity)
  field

end BuffonsNeedle
