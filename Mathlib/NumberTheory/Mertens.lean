/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Pietro Monticone, Robby Sneiderman, Guiseppe Sorge, Terence Tao,
Yan Yablonovskiy, Yi Yuan
-/
module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Log.InvLog
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.GammaDeriv
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.Tactic.NormNum.Prime

/-!
# Mertens theorems

This file establishes the first and second Mertens theorems that estimate sums and products
involving primes or the von Mangoldt function.

## Main definitions

- `Mertens.Weight` a class of weights that obey Mertens' first and second theorems with explicit
constants.
- `Mertens.Weight.vonMangoldt`: The function `f n = Λ n / n` bundled as a Mertens weight.
- `Mertens.Weight.prime`: The function `f p = if p.Prime then log p / p else 0` bundled as a
Mertens weight.

## Main results

- Mertens' first theorem: if `f` is a Mertens weight, then `∑ n ∈ Ioc 0 ⌊x⌋₊, f n - log x` is
bounded for `x ≥ 1`.
- Mertens' second theorem: if `f` is a Mertens weight, then
`∑ n ∈ Ioc 0 ⌊x⌋₊, f n / log n - log (log x) - M` decays like `1 / log x`, where `M` is the
Meissel--Mertens constant associated to `f`.
- In the case of the von Mangoldt weight, the Meissel--Mertens constant is equal to the
Euler--Mascheroni constant `γ`.
- Mertens' third theorem: `∏ p ∈ primesLE ⌊x⌋₊, (1 - 1 / p) ~ exp(-γ) / log x` as `x → ∞`.

Explicit constants are available in all cases.

## References

Parts of this file were upstreamed from the PrimeNumberTheoremAnd project by Kontorovich et al,
https://github.com/alexKontorovich/PrimeNumberTheoremAnd.

-/

@[expose] public section

namespace Mertens

open Nat hiding log log_pos
open Finset Filter Real Chebyshev intervalIntegral Asymptotics MeasureTheory Topology
open ArithmeticFunction hiding log
open scoped Nat.Prime

/-!
## Bounds on the partial sum of the logarithm

The partial sum of the logarithm can also be expressed as the logarithm of the factorial, as well
as a sum involving the von Mangoldt function.  Here we state these identities and also provide
some upper and lower bounds on the partial sum of `log n`.  These estimates will be used to
construct the von Mangoldt and prime Mertens weights.

TODO: add sharper bounds arising from the Euler-Maclaurin formula.

-/

/-- The partial sum of the logarithm is equal to the log of the factorial. -/
theorem sum_log_eq_log_factorial (N : ℕ) : ∑ n ∈ Ioc 0 N, log n = log N.factorial := by
  rw [← prod_Ico_id_eq_factorial, ← log_prod (by intros; simp; grind), prod_natCast]
  rfl

/-- The partial sum of the logarithm is equal to a weighted sum of the von Mangoldt function. -/
theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have (n : ℕ) : log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← floor_div_natCast]

/-- A crude upper bound on the partial sum of the logarithm. -/
theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x - x + log x + 1
    := by
  have h1 := floor_le (by linarith : 0 ≤ x)
  have h2 : 1 ≤ ⌊x⌋₊ := by simpa
  calc
    _ = ∑ n ∈ Icc 1 ⌊x⌋₊, log n := by rfl
    _ ≤ (∫ t in (1:ℕ)..⌊x⌋₊, log t) + log x := by
      rw [← sum_Ico_add_eq_sum_Icc (by simpa)]
      gcongr
      exact (strictMonoOn_log.monotoneOn.mono (by grind)).sum_le_integral_Ico h2
    _ ≤ (∫ t in 1..x, log t) + log x := by
      norm_cast; gcongr
      apply integral_mono_interval (by rfl) (mod_cast h2) h1 _ intervalIntegrable_log'
      exact ae_restrict_of_forall_mem (by measurability) (fun _ _ ↦ (log_pos (by grind)).le)
    _ = _ := by simp; ring

/-- An even cruder upper bound on the partial sum of the logarithm. -/
theorem sum_log_le' {x : ℝ} (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x := by
  linarith [sum_log_le hx, log_le_sub_one_of_pos (by linarith)]

/-- A crude lower bound on the partial sum of the logarithm. -/
theorem le_sum_log {x : ℝ} (hx : 1 ≤ x) :
    x * log x - x - log x + 1 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
  have : 1 ≤ ⌊x⌋₊ := by simpa
  calc
    _ = ∑ n ∈ Icc 1 ⌊x⌋₊, log n := by rfl
    _ = ∑ n ∈ Ico (1 + 1) (⌊x⌋₊ + 1), log n := by simp [← add_sum_Ioc_eq_sum_Icc this]; rfl
    _ = ∑ n ∈ Ico 1 ⌊x⌋₊, log (n + 1 : ℕ) := by rw [← sum_Ico_add']
    _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
      convert ((strictMonoOn_log.mono (by grind)).monotoneOn.integral_le_sum_Ico this).ge
      norm_cast
    _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
      nth_rw 3 [integral_symm]
      rw [sub_neg_eq_add, integral_add_adjacent_intervals] <;> simp
    _ ≥ (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log x := by
      gcongr
      apply integral_mono_on (floor_le (by linarith)) (by simp) (by simp)
      intro _ _; rify at this; gcongr <;> grind
    _ ≥ _ := by
      have : 0 ≤ log x := log_nonneg hx
      have : x - ⌊x⌋₊ ≤ 1 := by linarith [lt_floor_add_one x]
      grw [integral_log, log_one, intervalIntegral.integral_const, smul_eq_mul, this]
      linarith

/-- An even cruder lower bound on the partial sum of the logarithm. -/
theorem le_sum_log' {x : ℝ} (hx : 1 ≤ x) : x * log x - 2 * x ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
  linarith [le_sum_log hx, log_le_self (by linarith)]

/-- A sharper bound on the partial sum of the logarithm in the natural number case. -/
theorem le_sum_log_nat {N : ℕ} : N * log N - N ≤ ∑ n ∈ Ioc 0 N, log n := by
  by_cases! hN : N = 0
  · simp [hN]
  have : 0 ≤ log N := by positivity
  have : 0 ≤ log (2 * Real.pi) := log_nonneg (by linarith [two_le_pi])
  grw [sum_log_eq_log_factorial, ← Stirling.le_log_factorial_stirling hN]
  linarith

/-!
## An abstract theory of Mertens weights

We introduce the notion of a _Mertens weight_, which is a function `f : ℕ → ℝ` vanishing at
`0` and `1` that obeys upper and lower bounds on the quantity `∑ n ∈ Icc 0 ⌊x⌋₊, f n - log x`.

The main results are:

- **Abstract Mertens first theorem**: One has `∑ n ∈ Icc 0 ⌊x⌋₊, f n = log x + O(1)` for `1 ≤ x`.
(This is essentially tautological from the weight axioms.)
- **Abstract Mertens second theorem**: One has
`∑ n ∈ Icc 0 ⌊x⌋₊, f n / log n = log log x + M + O(1 / log x)` for `2 ≤ x` and some explicit
constant `M`.  (This follows from the first theorem by an Abel summation argument.)

Multiple versions of the first and second theorems are given here, with various levels of precision
in the error term, and with `x` required to be either `Real` or `Nat`.

In this file we will construct two specific Mertens weights, which we call the von Mangoldt weight
and the prime weight, which give the classical Mertens first and second theorems.  In future work
one could also construct Mertens weights associated to number fields or in arithmetic progressions
to create further variants of Mertens' theorems.  (In doing so, it may be worthwhile to generalize
the Mertens weight to allow for constant multiples in front of the logarithmic factor.)
-/

private lemma inv_div_log_sq_nonneg {x t : ℝ} (ht : t ∈ Set.Ioi x) (hx : 1 < x)
    : 0 ≤ t⁻¹ / (log t)^2 := by
  have : 0 < t := by grind
  positivity

private lemma integrable_const_div_mul_log_sq {x : ℝ} (C : ℝ) (hx : 2 ≤ x) :
    IntegrableOn (fun t ↦ (t⁻¹ / (log t)^2) * C) (.Ioi x) volume :=
  (integrableOn_Ioi_inv_div_log_sq (by linarith)).mul_const _

private lemma integ_div_mul_log_sq {x : ℝ} (C : ℝ) (hx : 2 ≤ x) :
    ∫ (t : ℝ) in .Ioi x, (t⁻¹ / (log t)^2) * C = C / log x := by
  rw [MeasureTheory.integral_mul_const, integral_Ioi_inv_divlog_sq (by linarith)]
  field

/-- A weight `f` is a bundled function `f : ℕ → ℝ` for which the quantity
`∑ n ∈ Icc 0 ⌊x⌋₊, f n - log x` is bounded above and below for `x ≥ 1`, which vanishes
at `0` and `1`, and does not grow faster than `log n / n`.

Created as a `class` rather than a `structure` in order to allow the components and methods of
`Weight` to be accessed via instance synthesis.
-/
class Weight where
  /-- The underlying function -/
  toFun : ℕ → ℝ
  map_zero' : toFun 0 = 0
  map_one' : toFun 1 = 0
  /-- The lower bound for the first Mertens error. -/
  lowerBound : ℝ
  /-- The upper bound for the first Mertens error. -/
  upperBound : ℝ
  le_first' : ∀ x ≥ 1, lowerBound ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, toFun n - log x
  first_le' : ∀ x ≥ 1, ∑ n ∈ Ioc 0 ⌊x⌋₊, toFun n - log x ≤ upperBound
  /-- A constant for the pointwise bound on the function -/
  C₀ : ℝ
  toFun_bound (n : ℕ) : |toFun n| ≤ C₀ * log n / n

namespace Weight

noncomputable instance instCoefn : CoeFun Weight (fun _ ↦ ℕ → ℝ) where
  coe f := f.toFun

open intervalIntegral

variable [f : Weight] (x : ℝ) (N : ℕ)

@[simp]
lemma map_zero : f 0 = 0 := f.map_zero'

@[simp]
theorem map_one : f 1 = 0 := f.map_one'

/-- The first Mertens error for a weight `f` is defined as
`f.E₁ x = ∑ n ∈ Ioc 0 ⌊x⌋₊, f n - log x`. -/
noncomputable def E₁ := ∑ n ∈ Ioc 0 ⌊x⌋₊, f n - log x

lemma sum_eq : ∑ n ∈ Ioc 0 ⌊x⌋₊, f n = log x + E₁ x := by grind [E₁]

lemma sum_eq' : ∑ n ∈ Icc 0 ⌊x⌋₊, f n = log x + E₁ x := by
  simpa [← add_sum_Ioc_eq_sum_Icc] using sum_eq x

lemma sum_eq_nat : ∑ n ∈ Ioc 0 N, f n = log N + E₁ N := by simpa using sum_eq N

lemma le_first {t : ℝ} (ht : t ≥ 1) : lowerBound ≤ E₁ t := le_first' t ht

lemma first_le {t : ℝ} (ht : t ≥ 1) : E₁ t ≤ upperBound := first_le' t ht

lemma apply_bound (n : ℕ) : |f n| ≤ C₀ * log n / n := f.toFun_bound n

lemma hi_nonneg : 0 ≤ upperBound := by
  simpa [(by rfl : Icc 0 1 = {0, 1})] using first_le' 1 (by rfl)

lemma lo_nonpos : lowerBound ≤ 0 := by
  simpa [(by rfl : Icc 0 1 = {0, 1})] using le_first' 1 (by rfl)

lemma C₀_nonneg : 0 ≤ C₀ := by
  refine le_of_mul_le_mul_of_pos_right ?_ (by positivity : 0 < log (2 : ℕ) / (2 : ℕ))
  grw [← mul_div_assoc C₀, ← apply_bound 2]
  simp

/-- An absolute value bound for the first Mertens error. -/
noncomputable def C₁ := max (-lowerBound) upperBound

/-- An absolute value bound (after dividing by `log x`) for the second Mertens error. -/
noncomputable def C₂ := upperBound - lowerBound

lemma C₁_nonneg : 0 ≤ C₁ := by simp [C₁, hi_nonneg, lo_nonpos]

lemma C₂_nonneg : 0 ≤ C₂ := by grind [C₂, hi_nonneg, lo_nonpos]

/-- The abstract Mertens first theorem. -/
theorem E₁_bound {x : ℝ} (hx : 1 ≤ x) : |E₁ x| ≤ C₁ := by
  grw [abs_le, ← le_first hx, first_le hx]; grind [C₁]

theorem sum_sub_log_bound {x : ℝ} (hx : 1 ≤ x) : |∑ n ∈ Ioc 0 ⌊x⌋₊, f n - log x| ≤ C₁ := by
  simpa [sum_eq x] using E₁_bound hx

theorem sum_sub_log_bound_nat : |∑ n ∈ Ioc 0 N, f n - log N| ≤ C₁ := by
  by_cases! hN : N = 0
  · simp [hN, C₁_nonneg]
  simpa using sum_sub_log_bound (mod_cast (by omega) : 1 ≤ (N : ℝ))

theorem sum_sub_log_bounded : (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, f n - log x)
    =O[atTop] fun _ ↦ (1 : ℝ) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one, eventually_atTop]
  exact ⟨C₁, 1, fun _ ↦ sum_sub_log_bound⟩

theorem sum_sub_log_bounded_nat : (fun N ↦ ∑ n ∈ Ioc 0 N, f n - log N)
    =O[atTop] fun _ ↦ (1 : ℝ) := by
  convert! sum_sub_log_bounded.comp_tendsto tendsto_natCast_atTop_atTop
  simp

theorem sum_asymp : (∑ n ∈ Ioc 0 ⌊·⌋₊, f n) ~[atTop] log :=
  sum_sub_log_bounded.trans_isLittleO (isLittleO_const_log_atTop)|>.isEquivalent

theorem sum_asymp_nat : (∑ n ∈ Ioc 0 ·, f n) ~[atTop] (log ↑·) := by
  convert! sum_asymp.comp_tendsto tendsto_natCast_atTop_atTop
  simp

/-- The Meissel--Mertens constant associated to a weight `f` is defined as
`M = (∫ t in .Ioi 2, (t⁻¹ / (log t)^2) * E₁ t) + 1 - log (log 2)`.
-/
noncomputable def M := (∫ t in .Ioi 2, (t⁻¹ / (log t)^2) * E₁ t) + 1 - log (log 2)

/-- The second Mertens error for a weight `f` is defined as
`E₂ x = ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - M`. -/
noncomputable def E₂ := ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - M

lemma sum_div_log_eq' : ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * f n = log (log x) + M + E₂ x := by
  grind [E₂]

lemma sum_div_log_eq : ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n = log (log x) + M + E₂ x := by
  simpa [← add_sum_Ioc_eq_sum_Icc, map_zero] using sum_div_log_eq' x

lemma integrable_mul_E₁ {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn (fun t ↦ (t⁻¹ / (log t)^2) * E₁ t) (.Ioi x) volume := by
  apply Integrable.mono (integrable_const_div_mul_log_sq C₁ hx)
  · exact Measurable.aestronglyMeasurable (by unfold E₁; fun_prop)
  filter_upwards [ae_restrict_mem (by measurability)] with t ht
  simp only [Set.mem_Ioi, norm_mul, norm_eq_abs] at ht ⊢
  have : 0 < log t := log_pos (by linarith)
  grw [f.E₁_bound (by linarith), le_abs_self f.C₁]

/-- General upper and lower bounds for the Meissel--Mertens constant. -/
theorem M_bounds :
    M ≤ upperBound / log 2 + 1 - log (log 2) ∧ lowerBound / log 2 + 1 - log (log 2) ≤ M := by
  unfold M
  rw [← integ_div_mul_log_sq _ (by rfl), ← integ_div_mul_log_sq _ (by rfl)]
  have := integrable_mul_E₁ (by rfl)
  have : NullMeasurableSet (.Ioi (2 : ℝ)) volume := by measurability
  constructor <;> gcongr with t ht
  exacts [integrable_const_div_mul_log_sq _ (by rfl),
          inv_div_log_sq_nonneg ht (by norm_num), first_le (by grind),
          integrable_const_div_mul_log_sq _ (by rfl),
          inv_div_log_sq_nonneg ht (by norm_num), le_first (by grind)]

theorem E₂_eq {x : ℝ} (hx : 2 ≤ x) :
    E₂ x = (log x)⁻¹ * E₁ x - ∫ t in .Ioi x, (t⁻¹ / (log t)^2) * E₁ t := by
  -- a weird bug - if I move `hcont` too far into the proof, the `grind` discharger breaks.
  have hcont : ContinuousOn (fun t ↦  -t⁻¹ / log t ^ 2) (.Icc 2 x) := by
    fun_prop (disch := grind [log_ne_zero])
  have : 0 < log x := log_pos (by linarith)
  suffices ∫ t in 2..x, (t⁻¹ / (log t)^2) * E₁ t = ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * f n -
    (log x)⁻¹ * (∑ n ∈ Icc 0 ⌊x⌋₊, f n) - log (log x) + log (log 2) by
    have := integral_interval_add_Ioi (integrable_mul_E₁ (by rfl)) (integrable_mul_E₁ hx)
    have : (log x)⁻¹ * E₁ x = (log x)⁻¹ * (∑ n ∈ Icc 0 ⌊x⌋₊, f n) - 1 := by
      rw [sum_eq']; field_simp; abel
    unfold E₂ M; linarith
  have : ∫ (t : ℝ) in 2..x, (t⁻¹ / (log t)^2) * ∑ n ∈ Icc 0 ⌊t⌋₊, f n =
      (∫ (t : ℝ) in 2..x, (t⁻¹ / (log t)^2) * log t)
      + ∫ (t : ℝ) in 2..x, (t⁻¹ / (log t)^2) * E₁ t := by
    simp only [sum_eq', mul_add]
    apply intervalIntegral.integral_add
    <;> rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    · apply (ContinuousOn.integrableOn_Icc _).mono_set Set.Ioc_subset_Icc_self
      fun_prop (disch := grind [log_ne_zero])
    · apply Integrable.mono (g := fun t ↦ t⁻¹ / (log 2 ^ 2) * C₁)
      · apply (ContinuousOn.integrableOn_Icc _).mono_set Set.Ioc_subset_Icc_self
        fun_prop (disch := grind)
      · exact Measurable.aestronglyMeasurable (by unfold E₁; fun_prop)
      · filter_upwards [ae_restrict_mem (by measurability)] with t ht
        simp only [norm_mul, norm_eq_abs, Set.mem_Ioc] at ht ⊢
        grw [f.E₁_bound (by linarith), le_abs_self f.C₁]
        have : 0 < t := by linarith
        gcongr; order
  have : ∫ (t : ℝ) in 2..x, (t⁻¹ / (log t)^2) * log t = log (log x) - log (log 2) := by
    rw [← integral_inv_div_log (by norm_num) (by linarith)]
    exact intervalIntegral.integral_congr fun _ _ ↦ by grind [Set.uIcc_of_le, log_pos]
  rw [sum_mul_eq_sub_integral_mul₁ _ map_zero map_one x (f := fun t ↦ (log t)⁻¹)]
  · suffices ∫ t in .Ioc 2 x, deriv (fun t ↦ (log t)⁻¹) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k =
        - ∫ t in 2..x, (t⁻¹ / (log t)^2) * ∑ n ∈ Icc 0 ⌊t⌋₊, f n by linarith
    rw [← intervalIntegral.integral_neg, integral_of_le hx]
    exact setIntegral_congr_fun (by measurability) (fun _ _ ↦ by simp [field])
  · intro t _
    have : log t ≠ 0 := log_ne_zero.mpr (by grind)
    fun_prop (disch := grind)
  · exact ContinuousOn.integrableOn_Icc (by simpa using hcont)

/-- The abstract Mertens second theorem. -/
theorem E₂_bound {x : ℝ} (hx : 2 ≤ x) : |f.E₂ x| ≤ C₂ / log x := by
  have hx' : 1 < x := by linarith
  have := log_pos hx'
  have := f.integrable_mul_E₁ hx
  have : NullMeasurableSet (.Ioi x) volume := by measurability
  rw [f.E₂_eq hx, abs_le, C₂]
  constructor
  · calc
      _ ≥ (log x)⁻¹ * lowerBound - ∫ t in .Ioi x, (t⁻¹ / (log t)^2) * upperBound := by
        gcongr with t ht
        exacts [le_first hx'.le, integrable_const_div_mul_log_sq _ hx,
          inv_div_log_sq_nonneg ht hx', first_le (by grind)]
      _ = _ := by rw [integ_div_mul_log_sq _ hx]; simp [field]
  · calc
      _ ≤ (log x)⁻¹ * upperBound - ∫ t in .Ioi x, (t⁻¹ / (log t)^2) * lowerBound := by
        gcongr with t ht
        exacts [first_le hx'.le, integrable_const_div_mul_log_sq _ hx,
          inv_div_log_sq_nonneg ht hx', le_first (by grind)]
      _ = _ := by rw [integ_div_mul_log_sq _ hx]; simp [field]

private theorem E₂_bound_weak {x : ℝ} (hx : 1 ≤ x) :
   |f.E₂ x| ≤ |log (log x)| + |M| + C₂ / log 2 := by
  have := C₂_nonneg
  rcases le_or_gt 2 x with hx' | hx'
  · grw [E₂_bound hx', hx', le_add_iff_nonneg_left]
    positivity
  unfold E₂
  grw [abs_sub, abs_sub, sum_eq_zero, abs_zero, zero_add, le_add_iff_nonneg_right]
  · exact div_nonneg C₂_nonneg (log_nonneg (by grind))
  intro n hn
  grw [mem_Icc, le_floor_iff (by linarith), hx'] at hn
  have : n = 0 ∨ n = 1 := by norm_cast at hn; omega
  rcases this with rfl | rfl <;> simp

theorem sum_div_log_sub_sub_bound {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - M| ≤ C₂ / log x := by
  grw [← E₂_bound hx, sum_div_log_eq x]; ring_nf; rfl

theorem sum_div_log_sub_sub_bound_nat (hN : 2 ≤ N) :
    |∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n - log (log N) - M| ≤ C₂ / log N := by
  simpa using sum_div_log_sub_sub_bound (mod_cast (by omega) : 2 ≤ (N : ℝ))

theorem sum_div_log_sub_sub_isBigO :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - M)
    =O[atTop] fun x ↦ (log x)⁻¹ := by
  simp only [isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
  refine ⟨C₂, 2, fun x hx ↦ ?_⟩
  convert sum_div_log_sub_sub_bound hx using 1
  grind [abs_of_pos (log_pos (by linarith : 1 < x))]

theorem sum_div_log_sub_sub_isBigO_nat :
    (fun (N : ℕ) ↦ ∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n - log (log N) - M)
    =O[atTop] fun N ↦ (log N)⁻¹ := by
  convert! f.sum_div_log_sub_sub_isBigO.comp_tendsto tendsto_natCast_atTop_atTop
  simp

theorem sum_div_log_sub_sub_isLittleO :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - M) =o[atTop] fun _ ↦ (1 : ℝ) :=
  f.sum_div_log_sub_sub_isBigO.trans_isLittleO inv_log_isLittleO_one

theorem sum_div_log_sub_sub_isLittleO_nat :
    (fun (N : ℕ) ↦ ∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n - log (log N) - M)
    =o[atTop] fun _ ↦ (1 : ℝ) := by
  convert! f.sum_div_log_sub_sub_isLittleO.comp_tendsto tendsto_natCast_atTop_atTop
  simp

theorem sum_div_log_sub_bounded : ∃ C, ∀ x ≥ 2,
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x)| ≤ C := by
  refine ⟨ |M| + C₂ / log 2, fun x hx ↦ ?_ ⟩
  have := C₂_nonneg
  grw [← hx, ← f.sum_div_log_sub_sub_bound hx, ← abs_add_le]
  ring_nf; rfl

theorem sum_div_log_sub_bounded_nat : ∃ C, ∀ N : ℕ, N ≥ 2 →
    |∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n - log (log N)| ≤ C := by
  obtain ⟨ C, hC ⟩ := f.sum_div_log_sub_bounded
  exact ⟨ C, fun N hN ↦ by simpa using hC N (mod_cast hN) ⟩

theorem sum_div_log_sub_isBigO :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x)) =O[atTop] fun _ ↦ (1 : ℝ) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one, eventually_atTop]
  obtain ⟨ C, _ ⟩ := f.sum_div_log_sub_bounded
  use C, 2

theorem sum_div_log_sub_isBigO_nat :
    (fun N : ℕ ↦ ∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n - log (log N)) =O[atTop] fun _ ↦ (1 : ℝ) := by
  convert! f.sum_div_log_sub_isBigO.comp_tendsto tendsto_natCast_atTop_atTop
  simp

theorem sum_div_log_asymp :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n) ~[atTop] fun x ↦ log (log x) :=
  (f.sum_div_log_sub_isBigO.trans_isLittleO one_isLittleO_log_log).isEquivalent

theorem sum_div_log_asymp_nat :
    (fun N : ℕ ↦ ∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n) ~[atTop] fun N ↦ log (log N) := by
  convert! f.sum_div_log_asymp.comp_tendsto tendsto_natCast_atTop_atTop
  simp

open ENNReal

/-- A formula for the Dirichlet series associated to Mertens' second theorem, with exact
error term. -/
theorem sum_div_log_mul_pow_eq {s : ℝ} (hs : 1 < s) :
    ∑' n : ℕ, (log n)⁻¹ * f n * n ^ (1 - s) = - log (s - 1) - eulerMascheroniConstant + M
    + ∫ x in .Ioi 1, (E₂ (x ^ (s - 1)⁻¹)) * x ^ (-2 : ℝ) := calc
  _ = ∑' n : ℕ, ∫ x in .Ioi 1, (log n)⁻¹ * f n * (Set.Ioi (n : ℝ)).indicator
      (fun x ↦ ((s - 1) * x ^ (-s))) x := by
    congr! with n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have : max 1  (n : ℝ) = n := mod_cast (by omega)
    simp only [MeasureTheory.integral_const_mul, measurableSet_Ioi, setIntegral_indicator,
      Set.Ioi_inter_Ioi, this, mul_eq_mul_left_iff, _root_.mul_eq_zero, inv_eq_zero, log_eq_zero,
      cast_eq_zero, cast_eq_one]
    rw [integral_Ioi_rpow_of_lt] <;> grind
  _ = ∫ x in .Ioi 1, ∑' n : ℕ, (log n)⁻¹ * f n * (Set.Ioi (n : ℝ)).indicator
      (fun x ↦ ((s - 1) * x ^ (-s))) x := by
    rw [integral_tsum]
    · exact fun _ ↦ Measurable.aestronglyMeasurable (by fun_prop (disch := measurability))
    · simp_rw [enorm_mul, ne_eq, ←lt_top_iff_ne_top, enorm_indicator_eq_indicator_enorm]
      calc
        _ = ∑' (i : ℕ), .ofReal (|(log i)⁻¹| * |toFun i| * (i : ℝ)^(1 - s)) := by
          congr! with n
          rcases eq_or_ne n 0 with rfl | hn
          · simp
          have : max (n : ℝ) 1 = n := mod_cast (by omega)
          rw [lintegral_const_mul' _ _ (by finiteness), setLIntegral_indicator measurableSet_Ioi,
            Set.Ioi_inter_Ioi, this, ← ofReal_integral_norm_eq_lintegral_enorm]
          · simp only [enorm_eq_ofReal_abs, abs_inv, norm_mul, norm_eq_abs,
            MeasureTheory.integral_const_mul]
            rw [setIntegral_congr_fun (g := fun x ↦ x ^ (- s)) (by measurability),
              integral_Ioi_rpow_of_lt (by linarith) (by positivity)]
            · rw [← ofReal_mul (by positivity), ← ofReal_mul (by positivity),
                abs_of_nonneg (by linarith : 0 ≤ s - 1)]
              grind
            · intro x hx
              have : 0 ≤ x := by grind
              exact abs_of_nonneg (by positivity)
          · apply Integrable.const_mul (integrableOn_Ioi_rpow_of_lt ..) <;> grind
        _ ≤ ∑' (i : ℕ), ENNReal.ofReal (C₀ * (i:ℝ)^(-s)) := by
          refine ENNReal.tsum_le_tsum fun n ↦ ofReal_le_ofReal ?_
          rcases eq_or_ne n 0 with rfl | _
          · simp [zero_rpow (by grind : -s ≠ 0)]
          rcases eq_or_ne n 1 with rfl | _
          · simp [C₀_nonneg]
          have : 0 < log n := log_pos (mod_cast (by omega))
          grw [apply_bound n, abs_of_nonneg (by positivity)]
          field_simp
          rw [mul_assoc, ← rpow_one_add' (by positivity) (by linarith)]
          grind
        _ < ⊤ := by
          simp_rw [ofReal_mul C₀_nonneg, ENNReal.tsum_mul_left]
          suffices ∑' (i : ℕ), ENNReal.ofReal (i ^ (-s)) < ⊤ by finiteness
          exact (summable_nat_rpow.mpr (by linarith)).tsum_ofReal_lt_top
  _ = ∫ x in .Ioi 1, (∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * f n) * ((s - 1) * x ^ (-s)) := by
    apply setIntegral_congr_ae (by measurability)
    have : ∀ᵐ (x : ℝ), ∀ n : ℕ, x ≠ n :=
      eventually_countable_forall.mpr fun n ↦ Measure.ae_ne volume (n : ℝ)
    filter_upwards [this] with x hx
    intro hx'
    calc
      _ = ∑' (n : ℕ), Set.indicator (Icc 0 ⌊x⌋₊)
          (fun (n : ℕ) ↦ (log n)⁻¹ * toFun n * (s - 1) * x ^ (-s)) n := by
        congr! with n
        have : 0 ≤ x := by grind
        specialize hx n
        simp only [Set.indicator, coe_Icc, Set.mem_Icc, Nat.le_floor_iff this]
        split_ifs <;> grind
      _ = _ := by
        rw [← sum_eq_tsum_indicator, ← sum_mul, ← sum_mul]
        ring
  _ = (s - 1) * ∫ x in .Ioi 1, log (log x) * x ^ (-s) + M * x ^ (-s) + E₂ x * x ^ (-s) := by
    simp_rw [sum_div_log_eq', add_mul, ← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun (by measurability) (by intro; grind)
  _ = _ := by
    have h1 := integrableOn_log_log_mul_rpow hs
    have h2 (C : ℝ) : IntegrableOn (C * · ^ (-s)) (.Ioi 1) :=
      Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)) C
    have h3 : IntegrableOn (fun x ↦ E₂ x * x ^ (-s)) (.Ioi 1) := by
      refine Integrable.mono'
        (g := fun x ↦ |log (log x) * x ^ (-s)| + (|M| + C₂ / log 2) * x ^ (-s))
        (h1.abs.add (h2 _)) (Measurable.aestronglyMeasurable (by unfold E₂; fun_prop))
        (ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx ↦ ?_))
      have : 0 < x := by grind
      have : 0 ≤ x ^ (-s) := by positivity
      grw [norm_mul, abs_mul, norm_eq_abs, norm_eq_abs, abs_of_nonneg this, E₂_bound_weak]
      <;> grind
    rw [MeasureTheory.integral_add, MeasureTheory.integral_add, mul_add, mul_add,
        eulerMascheroniConstant_eq_neg_integral_log_log hs, MeasureTheory.integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith) (by norm_num)]
    · nth_rw 4 [← integral_comp_rpow_Ioi_of_pos' (by linarith : 0 < s - 1) (by norm_num)]
      simp only [Real.one_rpow, neg_add_rev, sub_add_cancel_left, neg_neg, smul_eq_mul]
      congr
      · grind
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun (by measurability) (fun x hx ↦ ?_)
      have : 0 < x := by grind
      rw [← rpow_mul this.le, ← rpow_mul this.le, mul_inv_cancel₀ (by linarith), Real.rpow_one]
      calc
        _ = (s - 1) * (E₂ x * (x ^ (s - 1 - 1) * x ^ ((s - 1) * -2))) := by
          rw [← rpow_add this]; ring_nf
        _ = _ := by ring
    exacts [h1, h2 M, h1.add (h2 M), h3]

/-- An asymptotic for the Dirichlet series associated to Mertens' second theorem. -/
theorem sum_div_log_mul_pow_add_tendsto :
    Tendsto (fun s ↦ ∑' n : ℕ, (log n)⁻¹ * f n * n ^ (1 - s) + log (s - 1)) (𝓝[>] 1)
    (𝓝 (M - eulerMascheroniConstant)) := by
  have := C₂_nonneg
  suffices Tendsto (fun (s : ℝ) ↦ ∫ x in .Ioi 1, (E₂ (x ^ (s - 1)⁻¹)) * x ^ (-2 : ℝ)) (𝓝[>] 1)
      (𝓝 0) by
    rw [← tendsto_sub_nhds_zero_iff]
    apply this.congr'
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    rw [sum_div_log_mul_pow_eq hs]
    ring
  refine squeeze_zero_norm (fun _ ↦ norm_integral_le_lintegral_norm _) ?_
  apply (tendsto_toReal zero_ne_top).comp
  convert tendsto_lintegral_filter_of_dominated_convergence (l := 𝓝[>] (1 : ℝ)) (f := 0)
    (fun x ↦ ENNReal.ofReal ((|log (log x)| + |M| + C₂ / log 2) * x ^ (-2 : ℝ)))
    ?_ ?_ ?_ ?_
  · simp
  · unfold E₂; filter_upwards with _; fun_prop
  · filter_upwards [eventually_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds] with s hs hs'
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    gcongr
    rw [Set.mem_Ioi] at hs hx
    have : 0 < s - 1 := by linarith
    grw [norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ x ^ (-2 : ℝ))]
    gcongr
    rcases le_or_gt 2 (x ^ (s - 1)⁻¹) with h | h
    · grw [E₂_bound h, ← h, le_add_iff_nonneg_left]
      positivity
    · have hx' : x ≤ x ^ (s - 1)⁻¹ := self_le_rpow_of_one_le hx.le (by field_simp; linarith)
      have : 1 ≤ x ^ (s - 1)⁻¹ := by linarith
      grw [E₂_bound_weak this]
      gcongr 2
      grw [← neg_le_abs, abs_of_nonpos, neg_le_neg_iff]
      · exact log_le_log (log_pos hx) (log_le_log (by linarith) hx')
      apply log_nonpos (log_nonneg this)
      grw [h, log_two_lt_d9]
      norm_num
  · rw [lintegral_ofReal_ne_top_iff_integrable (Measurable.aestronglyMeasurable (by fun_prop))
        (Eventually.of_forall fun _ ↦ by simp only [Pi.zero_apply, rpow_neg_ofNat]; positivity)]
    simp_rw [add_assoc, add_mul _ (|M| + C₂ / log 2)]
    apply Integrable.add
    exacts [IntegrableOn.congr_fun (integrableOn_log_log_mul_rpow (by norm_num : 1 < (2 : ℝ))).abs
      (fun _ _ ↦ by simp [zpow_ofNat]) measurableSet_Ioi,
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul _]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    suffices Tendsto (fun s : ℝ ↦ E₂ (x ^ (s - 1)⁻¹) * x ^ (-2 : ℝ)) (𝓝[>] 1)
        (𝓝 (0 * x ^ (-2 : ℝ))) by simpa using ENNReal.tendsto_ofReal this.norm
    have h1 : Tendsto E₂ atTop (𝓝 0) := by
      apply squeeze_zero_norm' (a := (C₂ / log ·)) _ (tendsto_log_atTop.const_div_atTop _)
      filter_upwards [eventually_ge_atTop 2] with x hx
      simpa using E₂_bound hx
    have h2 : Tendsto (· - (1 : ℝ)) (𝓝[>] 1) (𝓝[>] 0) := by convert tendsto_map; simp
    exact (h1.comp ((tendsto_rpow_atTop_of_base_gt_one _ hx).comp
           (tendsto_inv_nhdsGT_zero.comp h2))).mul_const _

end Weight

section ConstructWeights

/-!
## Constructing the two Mertens weights

In this section we construct the two standard Mertens weights:

* The von Mangoldt weight `Weight.vonMangoldt n = Λ n / n`, where `Λ` is the von Mangoldt function.
* The prime weight `Weight.prime n = log n / n` if `n` is prime and `0` otherwise.

In the former case we obtain lower and upper bounds of `-2` and `log 4 + 1` for the first Mertens
theorem error term, with an improvement of the lower bound to `-1` for natural numbers.

In the latter case we obtain lower and upper bounds of `-3` and `log 4`, with an improvement of
the lower bound to `-2` in the natural number case.

The two sums `∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n` and `∑ n ∈ PrimesLE ⌊x⌋₊, log p / p` arising in the
first Mertens theorem differ asymptotically by a constant `E₁ = 0.755366...`.  Here we bound
this constant between `0` and `1`.
-/

variable (x : ℝ) (N : ℕ)

/-- The bare form of the von Mangoldt weight.  Should not be directly needed in applications. -/
noncomputable def vonMangoldtFun : ℕ → ℝ := fun n ↦ Λ n / n

/-- The bare form of the prime weight.  Should not be directly needed in applications. -/
noncomputable def primeFun : ℕ → ℝ := fun n ↦ if n.Prime then log n / n else 0

private lemma sum_prime_eq : ∑ n ∈ Ioc 0 N, primeFun n = ∑ p ∈ primesLE N, log p / p := by
  simp [primeFun, primesLE_eq_filter_Ioc_zero, sum_filter]

private lemma le_mul_sum_vonMangoldt {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * ∑ n ∈ Ioc 0 ⌊x⌋₊, vonMangoldtFun n := calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by simp [mul_sum, vonMangoldtFun]; ring_nf
  _ ≥ _ := by
    rw [sum_log_eq_sum_mangoldt]
    gcongr
    exact floor_le <| div_nonneg (by linarith) (by linarith)

private lemma mul_sum_prime_le :
    x * ∑ n ∈ Ioc 0 ⌊x⌋₊, primeFun n ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n + θ x := calc
  _ = ∑ p ∈ primesLE ⌊x⌋₊, log p * (x / p) := by rw [sum_prime_eq, mul_sum]; ring_nf
  _ ≤ ∑ p ∈ primesLE ⌊x⌋₊, log p * (⌊x / p⌋₊ + 1) := by gcongr; exact lt_floor_add_one _|>.le
  _ = ∑ p ∈ primesLE ⌊x⌋₊, log p * ⌊x / p⌋₊ + θ x := by
    simp [mul_add, sum_add_distrib, theta, primesLE_eq_filter_Ioc_zero]
  _ ≤ _ := by
    rw [sum_log_eq_sum_mangoldt, primesLE_eq_filter_Ioc_zero, sum_filter]
    gcongr
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    positivity

private lemma sum_prime_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, primeFun n ≤ log x + log 4 := by
  apply le_of_mul_le_mul_left _ (by linarith : 0 < x)
  grw [mul_sum_prime_le, theta_le_log4_mul_x (by linarith), sum_log_le' hx]
  ring_nf; rfl

/-- The summand defining the constant `E₁` below, with `e₁ p` defined to equal
`log p / (p * (p - 1))` if `p` is prime and `0` otherwise. -/
noncomputable def e₁ : ℕ → ℝ := fun p ↦ if p.Prime then log p / (p * (p - 1)) else 0

/-- The constant `E₁ = 0.755366...` (https://oeis.org/A138312) is defined as the sum of
`log p / (p * (p-1))` over primes `p`. -/
noncomputable def E₁ : ℝ := ∑' p : ℕ, e₁ p

theorem e₁_nonneg (p : ℕ) : 0 ≤ e₁ p := by
  unfold e₁
  split_ifs with h
  · have : 1 ≤ (p : ℝ) := mod_cast h.one_le
    positivity
  rfl

theorem e₁_summable : Summable e₁ := by
  refine (summable_one_div_nat_rpow.mpr (by norm_num : 1 < (3 : ℝ) / 2) |>.const_div
    4).of_nonneg_of_le e₁_nonneg fun p ↦ ?_
  unfold e₁
  split_ifs with h
  · have : 2 ≤ (p : ℝ) := mod_cast h.two_le
    have denom : p * ((p : ℝ) - 1) ≥ p ^ 2 / 2 := by nlinarith
    grw [log_le_rpow_div (cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2), denom]
    · field_simp
      rw [mul_assoc, ← rpow_add (by positivity)]
      ring_nf; norm_cast
    grind
  · positivity

theorem E₁_nonneg : 0 ≤ E₁ := tsum_nonneg e₁_nonneg

/-- An upper bound for `E₁`. -/
theorem E₁_le : E₁ ≤ 1 := by
  refine e₁_summable.tsum_le_of_sum_range_le (fun N ↦ ?_)
  have : ∑ n ∈ range N, _ ≤ ∑ n ∈ range (2 * N + 5), _ :=
    sum_le_sum_of_subset_of_nonneg (by grind) (fun n _ _ ↦ e₁_nonneg n)
  have : ∑ n ∈ range (2 * N + 5), e₁ n = log 2 / 2 + log 3 / 6 + ∑ n ∈ .Ico 5 (2 * N + 5), e₁ n
      := by
    convert sum_union (s₁ := {0,1,2,3,4}) (s₂ := .Ico 5 (2 * N + 5)) (by grind [disjoint_left])
    · ext; simp; omega
    norm_num [e₁]
  have : ∑ n ∈ .Ico 5 (2 * N + 5), e₁ n = ∑ n ∈ .range N, e₁ (2 * n + 5) := by
    apply (sum_of_injOn (2 * · + 5) (by intro; grind) (by intro; grind) _ (by simp)).symm
    simp only [mem_Ico, coe_range, Set.mem_image, Set.mem_Iio, not_exists, not_and, e₁,
      ite_eq_right_iff, div_eq_zero_iff, log_eq_zero, cast_eq_zero, cast_eq_one,
      _root_.mul_eq_zero, and_imp]
    intro p _ _ h hp
    obtain ⟨ m, rfl ⟩ := hp.odd_of_ne_two (by omega)
    specialize h (m - 2)
    omega
  let g : ℝ → ℝ := fun t ↦ log (2 * t + 3) / (2 * t + 3) ^ 2
  have : ∑ n ∈ .range N, e₁ (2 * n + 5) ≤ (5 / 4) * ∑ n ∈ .range N, g (n + 1) := by
    simp only [e₁, g, cast_add, cast_mul, cast_ofNat, mul_sum]
    gcongr with i _
    ring_nf
    have : 0 ≤ log (5 + (i : ℝ) * 2) := log_nonneg (by norm_cast; omega)
    split_ifs
    · field_simp; ring_nf; gcongr <;> norm_num
    positivity
  have : ∑ n ∈ .range N, g (n + 1) ≤ ∫ x in 0..N, g x := by
    convert (antitoneOn_of_deriv_nonpos (convex_Icc 0 _) ..).sum_le_integral (a := N) (f := g)
        using 1
    · simp
    · simp
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      simp only [Set.mem_Icc, g] at ht ⊢
      have : (2 * t + 3) ≠ 0 := by linarith
      fun_prop (disch := grind)
    · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
      rw [interior_Icc, Set.mem_Ioo] at ht
      have : (2 * t + 3) ^ 2 ≠ 0 := by simp; linarith
      fun_prop (disch := grind)
    · intro t ht
      simp at ht
      rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind),
        deriv_comp_mul_left 2 (fun t ↦ log (t + 3)), deriv_comp_add_const, deriv_log,
        deriv_comp_mul_left 2 (fun t ↦ (t + 3) ^ 2)]
      simp
      field_simp
      have : 0 ≤ 2 * t + 3 := by linarith
      have : 2 * log (2 * t + 3) ≥ 1 := by grw [← ht.1]; simp; linarith [log_three_gt_d9]
      grw [this]; simp
  have : ∫ x in 0..N, g x ≤ (log 3 + 1) / 6 := by
    let f : ℝ → ℝ := fun t ↦ (-log (2 * t + 3) - 1) / (2 * (2 * t + 3))
    have {x : ℝ} (hx : 0 ≤ x) : HasDerivAt f (g x) x := by
      have : HasDerivAt (2 * · + 3) 2 x := HasDerivAt.add_const _ (hasDerivAt_const_mul 2)
      convert! HasDerivAt.comp x ?_ this (h₂ := fun t ↦ (-log t - 1) / (2 * t))
        (h₂' := log (2 * x + 3) / (2 * (2 * x + 3)^2)) using 1
      · grind
      convert! HasDerivAt.fun_div (c' := -1 / (2 * x + 3)) _ (hasDerivAt_const_mul 2) _ using 1
      · field
      · convert! hasDerivAt_log (by linarith : 2 * x + 3 ≠ 0)|>.neg.sub_const _ using 1
        grind
      linarith
    have hN : 0 ≤ (N : ℝ) := cast_nonneg' N
    rw [integral_eq_sub_of_hasDerivAt (f := f)]
    · simp [f]; field_simp; grind [log_nonneg]
    · simp; grind
    · exact ContinuousOn.log (f := (2 * · + 3)) (by fun_prop) (by simp; grind)|>.div₀
        (by fun_prop) (by simp; grind)|>.intervalIntegrable
  linarith [log_two_lt_d9, log_three_lt_d9]

theorem sum_vonMangoldt_le_sum_prime_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ primesLE ⌊x⌋₊, log p / p + E₁ := by
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, sum_PrimePow_eq_sum_sum _
    (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ primesLE ⌊x ^ (1 / (k : ℝ))⌋₊, log p / (p ^ k : ℕ) := by
    simp only [primesLE_eq_filter_Ioc_zero]
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Prime.pow_minFac (by simp_all) (by grind)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ primesLE ⌊x⌋₊, log p / (p ^ k : ℕ) := by
    simp only [primesLE_eq_filter_Ioc_zero]
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    rw [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ primesLE ⌊x⌋₊, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg _ fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
    grw [← le_max_right]
  _ = ∑ p ∈ primesLE ⌊x⌋₊, log p / p +
      ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ primesLE ⌊x⌋₊, log p / (p ^ k : ℕ) := by
    simp [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
  _ ≤ _ := by
    gcongr
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊, e₁ p := by
      unfold e₁
      rw [← sum_filter, ← primesLE_eq_filter_Ioc_zero, sum_comm]
      gcongr with p hp
      simp_rw [← mul_one_div (log p), cast_pow, ← one_div_pow, ← mul_sum]
      rw [primesLE_eq_filter_Ioc_zero, mem_filter, mem_Ioc] at hp
      gcongr
      grw [← Ico_add_one_add_one_eq_Ioc, geom_sum_Ico_le_of_lt_one (by simp)]
      · have : 0 < (p : ℝ) := mod_cast hp.1.1.pos
        norm_num; field_simp; simp
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := e₁_summable.sum_le_tsum _ fun p _ ↦ e₁_nonneg p

/-- The von Mangoldt weight `f : ℕ → ℝ := fun n ↦ Λ n / n`. -/
@[reducible]
noncomputable def Weight.vonMangoldt : Weight := {
  toFun := vonMangoldtFun
  map_zero' := by simp [vonMangoldtFun]
  map_one' := by simp [vonMangoldtFun]
  lowerBound := -2
  upperBound := log 4 + 1
  le_first' x hx := by
    suffices x * (log x - 2) ≤ x * ∑ n ∈ Ioc 0 ⌊x⌋₊, vonMangoldtFun n by
      linarith [le_of_mul_le_mul_left this (by linarith)]
    grw [← le_mul_sum_vonMangoldt (by linarith), ← le_sum_log' hx]
    linarith [log_le_self (by linarith : 0 ≤ x)]
  first_le' x hx := by
    unfold vonMangoldtFun
    linarith [sum_prime_le hx, E₁_le, sum_vonMangoldt_le_sum_prime_add_E₁ hx, sum_prime_eq ⌊x⌋₊]
  C₀ := 1
  toFun_bound n := by
    unfold vonMangoldtFun
    grw [abs_of_nonneg (by positivity), one_mul, vonMangoldt_le_log]
}

@[simp]
lemma Weight.vonMangoldt_apply : vonMangoldt N = Λ N / N := rfl

@[simp]
lemma Weight.vonMangoldt_lowerBound_eq : vonMangoldt.lowerBound = -2 := rfl

@[simp]
lemma Weight.vonMangoldt_upperBound_eq : vonMangoldt.upperBound = log 4 + 1 := rfl

@[simp]
lemma Weight.vonMangoldt_C₁_eq : vonMangoldt.C₁ = log 4 + 1 := by
  simp [C₁]; linarith [log_four_eq, log_two_gt_d9]

@[simp]
lemma Weight.vonMangoldt_C₂_eq : vonMangoldt.C₂ = log 4 + 3 := by simp [C₂]; linarith

/-- The Meissel--Mertens constant for the von Mangoldt weight simplifies to the
Euler--Mascheroni constant. -/
@[simp]
lemma Weight.vonMangoldt_M_eq : vonMangoldt.M = eulerMascheroniConstant := by
  rw [← sub_eq_zero]
  apply tendsto_nhds_unique vonMangoldt.sum_div_log_mul_pow_add_tendsto
  have := log_riemannZeta_add_log_sub_isLittleO_ofReal
  rw [isLittleO_one_iff] at this
  refine tendsto_nhdsWithin_congr (fun s hs ↦ ?_) this
  rw [log_riemannZeta_eq hs]
  congr! 3 with n
  rcases eq_or_ne 0 n with rfl | h <;> simp
  field_simp
  rw [mul_assoc, ← rpow_add (mod_cast (by omega))]
  ring_nf
  grind [rpow_one]

/-- The prime weight `f : ℕ → ℝ := fun n ↦ 1 / n` if `n` is prime and `0` otherwise. -/
@[reducible]
noncomputable def Weight.prime : Weight := {
  toFun := primeFun
  map_zero' := by simp [primeFun]
  map_one' := by simp [primeFun]
  lowerBound := -3
  upperBound := log 4
  le_first' x hx := by
    have : -2 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x := Weight.vonMangoldt.le_first' x hx
    linarith [E₁_le, sum_vonMangoldt_le_sum_prime_add_E₁ hx, sum_prime_eq ⌊x⌋₊]
  first_le' x hx := by linarith [sum_prime_le hx]
  C₀ := 1
  toFun_bound n := by
    unfold primeFun
    split_ifs
    · rw [abs_of_nonneg, one_mul]; positivity
    · rw [abs_zero]; positivity
}

@[simp]
lemma Weight.prime_apply : prime N = if N.Prime then log N / N else 0 := rfl

@[simp]
lemma Weight.prime_lowerBound_eq : prime.lowerBound = -3 := rfl

@[simp]
lemma Weight.prime_upperBound_eq : prime.upperBound = log 4 := rfl

@[simp]
lemma Weight.prime_C₁_eq : prime.C₁ = 3 := by simp [C₁]; linarith [log_four_eq, log_two_lt_d9]

@[simp]
lemma Weight.prime_C₂_eq : prime.C₂ = log 4 + 3 := by simp [C₂]

private lemma neg_inv_sub_log_sub_inv_eq (p : Primes) : - (1 / p + log (1 - 1 / p))
    = ∑' (k : ℕ), 1 / ((↑k + 2) * (p : ℝ) ^ ((k + 2))) := by
  symm; apply HasSum.tsum_eq
  let c : ℕ → ℝ := fun k ↦ 1 / ((k + 1 : ℝ) * (p : ℝ) ^ ((k + 1)))
  suffices HasSum (fun k ↦ c (k + 1)) (- (1 / p + log (1 - 1 / p))) by
    convert this using 2 with n; unfold c; norm_cast
  rw [hasSum_nat_add_iff 1]
  have : 1 < (p : ℝ) := mod_cast p.prop.one_lt
  convert! (1 / (p : ℝ)).hasSum_pow_div_log_of_abs_lt_one
      (by grw [abs_of_pos (by positivity), ← this]; simp) using 1
  <;> simp +contextual [c, division_def]

private lemma tsum_inv_mul_pow_le {s : ℝ} (hs : 1 ≤ s) (p : Primes) :
    ∑' (k : ℕ), 1 / ((↑k + 2) * (p : ℝ) ^ ((↑k + 2) * s)) ≤ 1 / p ^ 2 := by
  have h0 : 0 < (p : ℝ) := mod_cast p.prop.pos
  have h2 : 2 ≤ (p : ℝ) := mod_cast p.prop.two_le
  refine tsum_le_of_sum_range_le (by intro; positivity) fun N ↦ ?_
  grw [← hs]
  · simp_rw [mul_one, rpow_add h0, rpow_ofNat, one_div, mul_inv_rev, mul_assoc, ← mul_sum]
    apply mul_le_of_le_one_right (by positivity)
    calc
      _ ≤ ∑ n ∈ range N, (1 - (2 : ℝ)⁻¹) * ((2 : ℝ)⁻¹) ^ n := by
        apply sum_le_sum; intros
        grw [← h2, inv_pow, rpow_natCast]
        field_simp; grind
      _ ≤ _ := by rw [← mul_sum, mul_neg_geom_sum, sub_le_self_iff]; positivity
  · linarith

/-- The standard formula for the Meissel-Mertens constant. -/
theorem Weight.prime_M_eq : prime.M = eulerMascheroniConstant
  + ∑' p : Primes, (log (1 - 1 / p) + 1 / p) := by
  rw [← sub_eq_iff_eq_add']
  apply tendsto_nhds_unique prime.sum_div_log_mul_pow_add_tendsto
  have h := log_riemannZeta_add_log_sub_isLittleO_ofReal
  rw [isLittleO_one_iff] at h
  suffices Tendsto (fun s : ℝ ↦ ∑' (p : Primes) (k : ℕ), 1 / ((k + 2) * (p : ℝ) ^ ((k + 2) * s)))
    (𝓝[>] 1) (𝓝 (∑' (p : Primes), (- (1 / p + log (1 - 1 / p))))) by
    convert tendsto_nhdsWithin_congr (fun s hs ↦ ?_) (h.sub this)
    · grind [tsum_neg]
    rw [log_riemannZeta_eq hs]
    nth_rw 1 [tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers]
    · have : ∑' (p : Primes), Λ p / (p ^ s * log p)
          = ∑' (n : ℕ), (log n)⁻¹ * prime n * (n : ℝ) ^ (1 - s) := by
        rw [Primes.tsum_eq_tsum_ite (fun p ↦ Λ p / (p ^ s * log p))]
        congr! 2 with n
        split_ifs with h <;> simp [vonMangoldt_apply_prime, h]
        have := h.pos
        have := h.log_pos
        field_simp (disch := positivity); rw [← rpow_add (by positivity)]; simp
      have :  ∑' (p : Primes) (k : ℕ),
          Λ (p ^ (k + 2)) / ((p ^ (k + 2) : ℕ) ^ s * log (p ^ (k + 2) : ℕ))
          = ∑' (p : Primes) (k : ℕ), 1 / ((k + 2) * (p : ℝ) ^ ((k + 2 : ℝ) * s)) := by
        congr! 4 with p k
        simp [ArithmeticFunction.vonMangoldt, p.prop.isPrimePow.pow, p.prop.pow_minFac]
        field_simp (disch := positivity)
        rw [rpow_mul (by positivity)]
        norm_cast
      linarith
    · apply (summable_one_div_nat_rpow.mpr hs).of_norm_bounded
      intro n
      rcases (by omega : n = 0 ∨ n = 1 ∨ 1 < n) with rfl | rfl | h
      · simp [zero_rpow_nonneg]
      · simp
      · have : 0 < log n := log_pos (mod_cast h)
        grw [norm_eq_abs, abs_div, abs_mul, vonMangoldt_le_log]
        field_simp
        apply le_abs_self
    · intro; simp +contextual [vonMangoldt_ne_zero_iff]
  apply tendsto_tsum_of_dominated_convergence ((summable_one_div_nat_pow.mpr one_lt_two).subtype _)
  · intro p
    rw [neg_inv_sub_log_sub_inv_eq p]
    have : 1 ≤ (p : ℝ) := mod_cast p.prop.one_le
    have : 2 ≤ (p : ℝ) := mod_cast p.prop.two_le
    apply tendsto_tsum_of_dominated_convergence summable_geometric_two
    · intro k
      convert! tendsto_const_nhds.div (b := (k + 2) * (p : ℝ) ^ (k + 2))
        (Tendsto.mono_left _ nhdsWithin_le_nhds) (by positivity) using 1
      have : Continuous (fun s : ℝ ↦ (k + 2) * (p : ℝ) ^ ((k + 2) * s)) := by
        fun_prop (disch := positivity)
      convert this.tendsto 1
      norm_cast; simp
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      rw [Set.mem_Ioi] at hs
      intro
      rw [norm_eq_abs, abs_of_nonneg (by positivity)]
      grw [← hs, ← this, one_div_pow]
      norm_cast; gcongr; grind
  · filter_upwards [eventually_mem_nhdsWithin] with s hs
    rw [Set.mem_Ioi] at hs
    intro p
    rw [norm_eq_abs, abs_of_nonneg (by positivity)]
    exact tsum_inv_mul_pow_le hs.le p

end ConstructWeights

section FirstTheorem

/-
## The first Mertens theorem

-/

variable {x : ℝ} (N : ℕ)

theorem le_sum_vonMangoldt_div_sub (hx : 1 ≤ x) : - 2 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x :=
 Weight.vonMangoldt.le_first' x hx

/-- A sharper lower bound in the case of natural numbers. -/
theorem le_sum_vonMangoldt_div_sub_nat : - 1 ≤ ∑ n ∈ Ioc 0 N, Λ n / n - log N := by
  by_cases! hN : N = 0
  · simp [hN]
  suffices N * (log N - 1) ≤ N * ∑ n ∈ Ioc 0 ⌊(N : ℝ)⌋₊, Weight.vonMangoldt n by
    simp at this
    linarith [le_of_mul_le_mul_left this (by norm_cast; omega)]
  have := le_mul_sum_vonMangoldt (x := N) (by positivity)
  simp only [floor_natCast, Weight.vonMangoldt_apply, vonMangoldtFun] at this ⊢
  grw [← this, ←le_sum_log_nat]
  ring_nf; rfl

theorem le_sum_log_prime_div_sub (hx : 1 ≤ x) : - 3 ≤ ∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x
    := (sum_prime_eq _).symm ▸ Weight.prime.le_first' x hx

/-- A sharper lower bound in the case of natural numbers. -/
theorem le_sum_log_prime_div_sub_nat : - 2 ≤ ∑ p ∈ primesLE N, log p / p - log N := by
  by_cases! hN : N = 0
  · simp [hN]
  have := sum_vonMangoldt_le_sum_prime_add_E₁ (mod_cast (by omega) : 1 ≤ (N : ℝ))
  simp at this
  linarith [le_sum_vonMangoldt_div_sub_nat N, E₁_le]

theorem sum_vonMangoldt_div_sub_le (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x ≤ log 4 + 1
    := Weight.vonMangoldt.first_le' x hx

theorem sum_log_prime_div_sub_le (hx : 1 ≤ x) : ∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x ≤ log 4
    := (sum_prime_eq _).symm ▸ Weight.prime.first_le' x hx

theorem abs_sum_vonMangoldt_div_sub_le (hx : 1 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x| ≤ log 4 + 1 :=
  Weight.vonMangoldt.sum_sub_log_bound hx|>.trans_eq Weight.vonMangoldt_C₁_eq

theorem abs_sum_vonMangoldt_div_sub_le_nat :
    |∑ n ∈ Ioc 0 N, Λ n / n - log N| ≤ log 4 + 1 :=
  Weight.vonMangoldt.sum_sub_log_bound_nat N|>.trans_eq Weight.vonMangoldt_C₁_eq

theorem abs_sum_log_prime_div_sub_le (hx : 1 ≤ x) :
    |∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x| ≤ 3 :=
  (sum_prime_eq _).symm ▸ Weight.prime.sum_sub_log_bound hx|>.trans_eq Weight.prime_C₁_eq

/-- A sharper bound in the case of natural numbers. -/
theorem abs_sum_log_prime_div_sub_le_nat : |∑ p ∈ primesLE N, log p / p - log N| ≤ 2 := by
  by_cases! hN : N = 0
  · simp [hN]
  have : 1 ≤ (N:ℝ) := mod_cast (by omega)
  rw [abs_le']; constructor
  · trans log 4
    · simpa using sum_log_prime_div_sub_le this
    linarith [log_four_eq, log_two_lt_d9]
  linarith [le_sum_log_prime_div_sub_nat N]

theorem sum_vonMangoldt_div_sub_bounded : (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x)
    =O[atTop] fun _ ↦ (1 : ℝ) := Weight.vonMangoldt.sum_sub_log_bounded

theorem sum_vonMangoldt_div_sub_bounded_nat : (fun N ↦ ∑ n ∈ Ioc 0 N, Λ n / n - log N)
    =O[atTop] fun _ ↦ (1 : ℝ) := Weight.vonMangoldt.sum_sub_log_bounded_nat

theorem sum_log_prime_div_sub_bounded : (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x)
    =O[atTop] fun _ ↦ (1 : ℝ) := by
  convert Weight.prime.sum_sub_log_bounded using 3; rw [← sum_prime_eq]; rfl

theorem sum_log_prime_div_sub_bounded_nat : (fun N ↦ ∑ p ∈ primesLE N, log p / p - log N)
    =O[atTop] fun _ ↦ (1 : ℝ) := by
  convert Weight.prime.sum_sub_log_bounded_nat using 3; rw [← sum_prime_eq]; rfl

theorem sum_vonMangoldt_div_asymp : (∑ n ∈ Ioc 0 ⌊·⌋₊, Λ n / n) ~[atTop] log :=
  Weight.vonMangoldt.sum_asymp

theorem sum_vonMangoldt_div_asymp_nat : (∑ n ∈ Ioc 0 ·, Λ n / n) ~[atTop] (log ↑·) :=
  Weight.vonMangoldt.sum_asymp_nat

theorem sum_log_prime_div_asymp : (∑ p ∈ primesLE ⌊·⌋₊, log p / p) ~[atTop] log := by
  convert Weight.prime.sum_asymp using 2; rw [← sum_prime_eq]; rfl

theorem sum_log_prime_div_asymp_nat : (∑ p ∈ primesLE ·, log p / p) ~[atTop] (log ↑·) := by
  convert Weight.prime.sum_asymp_nat using 2; rw [← sum_prime_eq]; rfl

end FirstTheorem

section SecondTheorem

/-
## The second Mertens theorem
-/

variable {x : ℝ} {N : ℕ}

private lemma Weight.vonMangoldt_sum_inv_log_mul_eq :
    ∑ n ∈ Ioc 0 N, (log n)⁻¹ * Weight.vonMangoldt n = ∑ n ∈ Ioc 0 N, Λ n / (n * log n) := by
  congr! 1; simp; field

private lemma Weight.prime_sum_inv_log_mul_eq :
    ∑ n ∈ Ioc 0 N, (log n)⁻¹ * Weight.prime n = ∑ p ∈ primesLE N, 1 / (p : ℝ) := by
  simp only [Weight.prime_apply, mul_ite, mul_zero, primesLE_eq_filter_Ioc_zero, sum_filter]
  congr! 2 with p _ hp
  have := hp.log_pos
  field_simp (disch := positivity)

theorem sum_vonMangoldt_div_mul_log_sub_sub_bound (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - log (log x) - eulerMascheroniConstant| ≤
      (log 4 + 3) / log x := by
  rw [← Weight.vonMangoldt_M_eq]
  convert! Weight.vonMangoldt.sum_div_log_sub_sub_bound hx using 2
  · rw [Weight.vonMangoldt_sum_inv_log_mul_eq]
  simp

theorem sum_vonMangoldt_div_mul_log_sub_sub_bound_nat (hN : 2 ≤ N) :
    |∑ n ∈ Ioc 0 N, Λ n / (n * log n) - log (log N) - eulerMascheroniConstant| ≤
      (log 4 + 3) / log N := by
  convert sum_vonMangoldt_div_mul_log_sub_sub_bound (x := N) (mod_cast hN)
  simp

theorem sum_prime_inv_sub_sub_bound (hx : 2 ≤ x) :
    |∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ) - log (log x) - Weight.prime.M| ≤ (log 4 + 3) / log x := by
  convert! Weight.prime.sum_div_log_sub_sub_bound hx using 2
  · rw [Weight.prime_sum_inv_log_mul_eq]
  simp

theorem sum_prime_inv_sub_sub_bound_nat (hN : 2 ≤ N) :
    |∑ p ∈ primesLE N, 1 / (p : ℝ) - log (log N) - Weight.prime.M| ≤ (log 4 + 3) / log N := by
  convert sum_prime_inv_sub_sub_bound (x := N) (mod_cast hN)
  simp

theorem sum_vonMangoldt_div_mul_log_sub_sub_isBigO :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - log (log x) - eulerMascheroniConstant)
    =O[atTop] fun x ↦ (log x)⁻¹ := by
  rw [← Weight.vonMangoldt_M_eq]
  convert Weight.vonMangoldt.sum_div_log_sub_sub_isBigO using 4
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

theorem sum_vonMangoldt_div_mul_log_sub_sub_isBigO_nat :
    (fun N : ℕ ↦ ∑ n ∈ Ioc 0 N, Λ n / (n * log n) - log (log N) - eulerMascheroniConstant)
    =O[atTop] fun N ↦ (log N)⁻¹ := by
  rw [← Weight.vonMangoldt_M_eq]
  convert Weight.vonMangoldt.sum_div_log_sub_sub_isBigO_nat using 4
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

theorem sum_prime_div_mul_log_sub_sub_isBigO :
    (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ) - log (log x) - Weight.prime.M)
    =O[atTop] fun x ↦ (log x)⁻¹ := by
  convert Weight.prime.sum_div_log_sub_sub_isBigO using 4
  rw [Weight.prime_sum_inv_log_mul_eq]

theorem sum_prime_div_mul_log_sub_sub_isBigO_nat :
    (fun (N : ℕ) ↦ ∑ p ∈ primesLE N, 1 / (p : ℝ) - log (log N) - Weight.prime.M)
    =O[atTop] fun N ↦ (log N)⁻¹ := by
  convert Weight.prime.sum_div_log_sub_sub_isBigO_nat using 4
  rw [Weight.prime_sum_inv_log_mul_eq]

theorem sum_vonMangoldt_div_mul_log_sub_sub_isLittleO :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - log (log x) - eulerMascheroniConstant)
    =o[atTop] fun _ ↦ (1 : ℝ) := by
  rw [← Weight.vonMangoldt_M_eq]
  convert Weight.vonMangoldt.sum_div_log_sub_sub_isLittleO using 4
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

theorem sum_vonMangoldt_div_mul_log_sub_sub_isLittleO_nat :
    (fun (N : ℕ) ↦ ∑ n ∈ Ioc 0 N, Λ n / (n * log n) - log (log N) - eulerMascheroniConstant)
    =o[atTop] fun _ ↦ (1 : ℝ) := by
  rw [← Weight.vonMangoldt_M_eq]
  convert Weight.vonMangoldt.sum_div_log_sub_sub_isLittleO_nat using 4
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

theorem sum_prime_inv_sub_sub_isLittleO :
    (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ) - log (log x) - Weight.prime.M)
    =o[atTop] fun _ ↦ (1 : ℝ) := by
  convert Weight.prime.sum_div_log_sub_sub_isLittleO using 4
  rw [Weight.prime_sum_inv_log_mul_eq]

theorem sum_prime_inv_sub_sub_isLittleO_nat :
    (fun (N : ℕ) ↦ ∑ p ∈ primesLE N, 1 / (p : ℝ) - log (log N) - Weight.prime.M)
    =o[atTop] fun _ ↦ (1 : ℝ) := by
  convert Weight.prime.sum_div_log_sub_sub_isLittleO_nat using 4
  rw [Weight.prime_sum_inv_log_mul_eq]

theorem sum_vonMangoldt_div_mul_log_sub_isBigO :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - log (log x)) =O[atTop] fun _ ↦ (1 : ℝ) := by
  convert Weight.vonMangoldt.sum_div_log_sub_isBigO using 3
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

theorem sum_vonMangoldt_div_mul_log_sub_isBigO_nat
    : (fun (N : ℕ) ↦ ∑ n ∈ Ioc 0 N, Λ n / (n * log n) - log (log N)) =O[atTop] fun _ ↦ (1 : ℝ)
    := by
  convert Weight.vonMangoldt.sum_div_log_sub_isBigO_nat using 3
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

theorem sum_prime_inv_sub_isBigO :
    (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ) - log (log x)) =O[atTop] fun _ ↦ (1 : ℝ) := by
  convert Weight.prime.sum_div_log_sub_isBigO using 3
  rw [Weight.prime_sum_inv_log_mul_eq]

theorem sum_prime_inv_sub_isBigO_nat
    : (fun (N : ℕ) ↦ ∑ p ∈ primesLE N, 1 / (p : ℝ) - log (log N)) =O[atTop] fun _ ↦ (1 : ℝ) := by
  convert Weight.prime.sum_div_log_sub_isBigO_nat using 3
  rw [Weight.prime_sum_inv_log_mul_eq]

theorem sum_vonMangoldt_div_mul_log_asymp :
    (∑ n ∈ Ioc 0 ⌊·⌋₊, Λ n / (n * log n)) ~[atTop] fun x ↦ log (log x) := by
  convert Weight.vonMangoldt.sum_div_log_asymp using 2
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

theorem sum_vonMangoldt_div_mul_log_asymp_nat :
    (∑ n ∈ Ioc 0 ·, Λ n / (n * log n)) ~[atTop] fun N ↦ log (log N) := by
  convert Weight.vonMangoldt.sum_div_log_asymp_nat using 2
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

theorem sum_prime_inv_asymp :
    (∑ p ∈ primesLE ⌊·⌋₊, 1 / (p : ℝ)) ~[atTop] fun x ↦ log (log x) := by
  convert Weight.prime.sum_div_log_asymp using 2
  rw [Weight.prime_sum_inv_log_mul_eq]

theorem sum_prime_inv_asymp_nat :
    (∑ p ∈ primesLE ·, 1 / (p : ℝ)) ~[atTop] fun N ↦ log (log N) := by
  convert Weight.prime.sum_div_log_asymp_nat using 2
  rw [Weight.prime_sum_inv_log_mul_eq]

end SecondTheorem

section ThirdTheorem

/-
## The third Mertens theorem

It will be convenient to express the third Mertens theorem in terms of an error term
`E₃ x = ∑ p ∈ primesLE ⌊x⌋₊, log (1 - 1 / (p : ℝ)) + log (log x) + eulerMascheroniConstant`.
-/

private lemma neg_inv_sub_log_sub_inv_nonneg (p : Primes) : 0 ≤ - (1 / p + log (1 - 1 / p)) := by
  have : 1 < (p : ℝ) := mod_cast p.prop.one_lt
  grw [log_le_sub_one_of_pos] <;> field_simp <;> grind

private lemma neg_inv_sub_log_sub_inv_le (p : Primes) : - (1 / p + log (1 - 1 / p))
    ≤ 1 / p ^ 2 := by
  rw [neg_inv_sub_log_sub_inv_eq p]
  have := tsum_inv_mul_pow_le (le_refl _) p
  norm_cast at this
  simpa using this

/-- The error term in Mertens' third theorem. -/
noncomputable def E₃ (x : ℝ) :=
  ∑ p ∈ primesLE ⌊x⌋₊, log (1 - 1 / (p : ℝ)) + log (log x) + eulerMascheroniConstant

theorem sum_prime_log_sub_inv_eq (x : ℝ) : ∑ p ∈ primesLE ⌊x⌋₊, log (1 - 1 / (p : ℝ))
    = - log (log x) - eulerMascheroniConstant + E₃ x := by grind [E₃]

theorem sum_prime_log_sub_inv_eq_nat (N : ℕ) : ∑ p ∈ primesLE N, log (1 - 1 / (p : ℝ))
    = - log (log N) - eulerMascheroniConstant + E₃ N := by
  simpa using sum_prime_log_sub_inv_eq N

theorem prod_prime_one_minus_inv_eq {x : ℝ} (hx : 1 < x) : ∏ p ∈ primesLE ⌊x⌋₊, (1 - (1 : ℝ) / p) =
    exp (-eulerMascheroniConstant) * exp (E₃ x) / log x := by
  have hlog : 0 < log x := log_pos hx
  have hpos {p : ℕ} (hp : p.Prime) : (0 : ℝ) < 1 - 1 / p := by
    grind [one_div_le_one_div_of_le two_pos (mod_cast hp.two_le : (2 : ℝ) ≤ p)]
  simp_rw [E₃, exp_add, exp_sum, exp_log hlog, exp_neg]
  field_simp
  exact prod_congr rfl fun p hp ↦ (exp_log (hpos (mem_filter.mp hp).2)).symm

/-- A completely explicit upper bound on the error term. -/
theorem E₃_bound {x : ℝ} (hx : 2 ≤ x) : |E₃ x| ≤ (log 4 + 3) / log x + 1 / ⌊x⌋₊ := by
  have hx' := floor_mono hx
  simp only [floor_ofNat] at hx'
  have := sum_prime_inv_sub_sub_bound hx
  rw [Weight.prime_M_eq, Nat.Primes.tsum_eq_tsum_ite fun p ↦ log (1 - 1 / p) + 1 / p,
      ← Summable.sum_add_tsum_nat_add (⌊x⌋₊ + 1)] at this
  · have h {a b c d : ℝ} (ha : |a| ≤ b) (hac : |a + c| ≤ d) : |c| ≤ b + d := by
      grw [abs_add' c a, ha, hac]
    apply h this
    rw [← sum_filter, ← primesLE_eq_filter_range, sum_add_distrib, E₃]
    ring_nf
    have (i : ℕ) : 0 ≤ - if (1 + i + ⌊x⌋₊).Prime then ((1 + i + ⌊x⌋₊ : ℕ) : ℝ)⁻¹
        + log (1 - ((1 + i + ⌊x⌋₊ : ℕ) : ℝ)⁻¹) else 0 := by
      split_ifs with hp
      · grind [neg_inv_sub_log_sub_inv_nonneg ⟨ _, hp ⟩]
      · simp
    grw [← tsum_neg, abs_of_nonneg (tsum_nonneg this)]
    apply tsum_le_of_sum_range_le this; intro N
    calc
      _ ≤ ∑ i ∈ range N, (((⌊x⌋₊ + i : ℕ): ℝ)⁻¹ - ((⌊x⌋₊ + (i + 1) : ℕ): ℝ)⁻¹) := by
        apply sum_le_sum; intro i _
        split_ifs with h
        · calc
            _ ≤ 1 / ((1 + i + ⌊x⌋₊ : ℕ) : ℝ) ^ 2 := by
              convert neg_inv_sub_log_sub_inv_le ⟨ _, h ⟩ <;> grind
            _ ≤ _ := by
              rw [inv_sub_inv (by positivity) (by positivity)]
              push_cast; ring_nf; gcongr <;> grind
        · simp only [neg_zero, cast_add, cast_one, sub_nonneg]; gcongr; linarith
      _ ≤ _ := by
        rw [sum_range_sub', add_zero, cast_add, tsub_le_iff_right, le_add_iff_nonneg_right]
        positivity
  · rw [← Nat.Primes.summable_iff_summable_ite]
    apply ((summable_one_div_nat_rpow.mpr (by norm_num : 1 < (2 : ℝ))).subtype _).of_norm_bounded
    intro p
    have h1 := neg_inv_sub_log_sub_inv_nonneg p
    have h2 := neg_inv_sub_log_sub_inv_le p
    simp at h1 h2 ⊢
    grind

theorem E₃_isBigO : E₃ =O[atTop] fun x ↦ (log x)⁻¹ := by
  trans fun x ↦ (log 4 + 3) / log x + 1 / ⌊x⌋₊
  · apply Eventually.isBigO
    filter_upwards [eventually_ge_atTop 2] with x hx
    simpa using E₃_bound hx
  · simp_rw [division_def]
    refine (isBigO_const_mul_self ..).add (.of_bound 2 ?_)
    filter_upwards [eventually_gt_atTop 2] with x hx
    have := log_pos (by linarith : 1 < x)
    simp [abs_of_pos this]
    have := lt_floor_add_one x
    have : 0 < (⌊x⌋₊ : ℝ) := by linarith
    field_simp
    grw [Real.log_le_self] <;> linarith

theorem E₃_isLittleO : E₃ =o[atTop] fun _ ↦ (1 : ℝ) :=
  E₃_isBigO.trans_isLittleO inv_log_isLittleO_one

theorem E₃_tendsto : Tendsto E₃ atTop (𝓝 0) := by simpa [isLittleO_one_iff] using E₃_isLittleO

theorem exp_E₃_sub_isBigO : (fun x ↦ exp (E₃ x) - 1) =O[atTop] fun x ↦ (log x)⁻¹ := by
  suffices (exp · - 1) =O[𝓝 0] (·) from this.comp_tendsto E₃_tendsto|>.trans E₃_isBigO
  simpa using differentiable_exp.differentiableAt.isBigO_sub (x₀ := 0)

theorem exp_E₃_sub_isLittleO : (fun x ↦ exp (E₃ x) - 1) =o[atTop] fun _ ↦ (1 : ℝ) :=
  exp_E₃_sub_isBigO.trans_isLittleO inv_log_isLittleO_one

theorem exp_E₃_tendsto : Tendsto (fun x ↦ exp (E₃ x)) atTop (𝓝 1) := by
  rw [← tendsto_sub_nhds_zero_iff, ← isLittleO_one_iff (F := ℝ)]
  exact exp_E₃_sub_isLittleO

theorem sum_primes_log_sub_add_isBigO :
    (fun x : ℝ ↦ ∑ p ∈ primesLE ⌊x⌋₊, log (1 - 1 / (p : ℝ)) + log (log x))
    =O[atTop] fun _ ↦ (1 : ℝ) := by
  suffices (fun x : ℝ ↦ E₃ x - eulerMascheroniConstant) =O[atTop] fun _ ↦ (1 : ℝ) from
    this.congr (by grind [sum_prime_log_sub_inv_eq]) (by simp)
  exact E₃_isLittleO.isBigO.sub (isBigO_const_one ..)

theorem sum_primes_log_sub_add_isBigO_nat :
    (fun N : ℕ ↦ ∑ p ∈ primesLE N, log (1 - 1 / (p : ℝ)) + log (log N))
    =O[atTop] fun _ ↦ (1 : ℝ) := by
  convert sum_primes_log_sub_add_isBigO.comp_tendsto tendsto_natCast_atTop_atTop
  <;> simp

theorem log_mul_prod_prime_one_minus_inv_tendsto :
    Tendsto (fun x ↦ log x * ∏ p ∈ primesLE ⌊x⌋₊, (1 - (1 : ℝ) / p)) atTop
    (𝓝 (exp (-eulerMascheroniConstant))) := by
  have := exp_E₃_tendsto.const_mul (exp (-eulerMascheroniConstant))
  rw [mul_one] at this
  apply this.congr'
  filter_upwards [eventually_gt_atTop 1]
  grind [prod_prime_one_minus_inv_eq, log_pos]

theorem log_mul_prod_prime_one_minus_inv_tendsto_nat :
    Tendsto (fun (N : ℕ) ↦ log N * ∏ p ∈ primesLE N, (1 - (1 : ℝ) / p)) atTop
    (𝓝 (exp (-eulerMascheroniConstant))) := by
  convert log_mul_prod_prime_one_minus_inv_tendsto.comp tendsto_natCast_atTop_atTop
  simp

theorem prod_prime_one_minus_inv_asymp :
    (∏ p ∈ primesLE ⌊·⌋₊, (1 - (1 : ℝ) / p)) ~[atTop] (exp (-eulerMascheroniConstant) / log ·) := by
  have := log_mul_prod_prime_one_minus_inv_tendsto.const_mul (exp eulerMascheroniConstant)
  simp [← exp_add] at this
  refine isEquivalent_of_tendsto_one (this.congr' ?_)
  filter_upwards [eventually_gt_atTop 1]
  simp
  grind [log_pos, exp_neg]

theorem prod_prime_one_minus_inv_asymp_nat :
    (∏ p ∈ primesLE ·, (1 - (1 : ℝ) / p)) ~[atTop] (exp (-eulerMascheroniConstant) / log ·) := by
  convert! prod_prime_one_minus_inv_asymp.comp_tendsto tendsto_natCast_atTop_atTop
  simp

end ThirdTheorem

end Mertens
