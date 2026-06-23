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
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.NumberTheory.Chebyshev

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

Explicit constants are available in all cases.

## TODO

- Establish that the Meissel--Mertens constant for the von Mangoldt function is equal to the
Euler--Mascheroni constant.
- Establish Mertens' third theorem.

## References

Parts of this file were upstreamed from the PrimeNumberTheoremAnd project by Kontorovich et al,
https://github.com/alexKontorovich/PrimeNumberTheoremAnd.

-/

@[expose] public section

namespace Mertens

open Nat hiding log log_pos
open Finset Filter Real Chebyshev intervalIntegral Asymptotics MeasureTheory
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
      exact (strictMonoOn_log.monotoneOn.mono (by grind)).sum_le_integral_Ico (f := log) h2
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
    rw [sub_neg_eq_add, integral_add_adjacent_intervals] <;> exact intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log x := by
    gcongr
    apply integral_mono_on (floor_le (by linarith)) intervalIntegrable_log'
      intervalIntegrable_const
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
  grw [sum_log_eq_log_factorial, ←Stirling.le_log_factorial_stirling hN]
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

In this file we will construct two specific Mertens weight, which we call the von Mangoldt weight
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
`∑ n ∈ Icc 0 ⌊x⌋₊, f n - log x` is bounded above and below for `x ≥ 1`, and which vanishes
at `0` and `1`.
-/
class Weight where
  to_fun : ℕ → ℝ
  map_zero' : to_fun 0 = 0
  map_one' : to_fun 1 = 0
  lowerBound : ℝ
  upperBound : ℝ
  le_first' : ∀ x ≥ 1, lowerBound ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, to_fun n - log x
  first_le' : ∀ x ≥ 1, ∑ n ∈ Ioc 0 ⌊x⌋₊, to_fun n - log x ≤ upperBound

namespace Weight

noncomputable instance inst_coefn : CoeFun Weight (fun _ ↦ ℕ → ℝ) where
  coe f := f.to_fun

open intervalIntegral

/- This is needed to ensure measurability of various error terms -/
attribute [fun_prop] measurable_from_top

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

lemma sum_eq_nat : ∑ n ∈ Ioc 0 N, f n = log N + E₁ N := by
  simpa using sum_eq N

lemma le_first {t : ℝ} (ht : t ≥ 1) : lowerBound ≤ E₁ t := le_first' t ht

lemma first_le {t : ℝ} (ht : t ≥ 1) : E₁ t ≤ upperBound := first_le' t ht

lemma hi_nonneg : 0 ≤ upperBound := by
  simpa [(by rfl : Icc 0 1 = {0, 1})] using first_le' 1 (by rfl)

lemma lo_nonpos : lowerBound ≤ 0 := by
  simpa [(by rfl : Icc 0 1 = {0, 1})] using le_first' 1 (by rfl)

/-- An absolute value bound for the first Mertens error. -/
noncomputable def C₁ := max (-lowerBound) upperBound

/-- An absolute value bound (after dividing by `log x`) for the second Mertens error. -/
noncomputable def C₂ := upperBound - lowerBound

lemma C₁_nonneg : 0 ≤ C₁ := by simp [C₁, hi_nonneg, lo_nonpos]

lemma C₂_nonneg : 0 ≤ C₂ := by grind [C₂, hi_nonneg, lo_nonpos]

/-- The abstract Mertens first theorem. -/
theorem first_theorem' {x : ℝ} (hx : 1 ≤ x) : |E₁ x| ≤ C₁ := by
  grw [abs_le, ← le_first hx, first_le hx]; grind [C₁]

theorem first_theorem {x : ℝ} (hx : 1 ≤ x) : |∑ n ∈ Ioc 0 ⌊x⌋₊, f n - log x| ≤ C₁ := by
  simpa [sum_eq x] using first_theorem' hx

theorem first_theorem_nat : |∑ n ∈ Ioc 0 N, f n - log N| ≤ C₁ := by
  by_cases! hN : N = 0
  · simp [hN, C₁_nonneg]
  simpa using first_theorem (mod_cast (by lia) : 1 ≤ (N : ℝ))

theorem first_theorem_error_bounded : (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, f n - log x)
    =O[atTop] fun _ ↦ (1 : ℝ) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one, eventually_atTop]
  exact ⟨C₁, 1, fun _ ↦ first_theorem⟩

theorem first_theorem_error_bounded_nat : (fun N ↦ ∑ n ∈ Ioc 0 N, f n - log N)
    =O[atTop] fun _ ↦ (1 : ℝ) := by
  convert! first_theorem_error_bounded.comp_tendsto tendsto_natCast_atTop_atTop
  simp

theorem first_theorem_asymp : (∑ n ∈ Ioc 0 ⌊·⌋₊, f n) ~[atTop] log :=
  (first_theorem_error_bounded.trans_isLittleO (isLittleO_const_log_atTop)).isEquivalent

theorem first_theorem_asymp_nat : (∑ n ∈ Ioc 0 ·, f n) ~[atTop] (log ↑·) := by
  convert! first_theorem_asymp.comp_tendsto tendsto_natCast_atTop_atTop
  simp

/-- The Meissel--Mertens constant associated to a weight `f` is defined as
`M = (∫ t in .Ioi 2, (t⁻¹ / (log t)^2) * E₁ t) + 1 - log (log 2)`.
-/
noncomputable def M := (∫ t in .Ioi 2, (t⁻¹ / (log t)^2) * E₁ t) + 1 - log (log 2)

/- The second Mertens error for a weight `f` is defined as
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
  grw [f.first_theorem' (by linarith), le_abs_self f.C₁]

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
  -- a weird bug - if I move `hcont` too far into the proof, the proof breaks.  Have not
  -- identified the cause yet.
  have hcont : ContinuousOn (fun t ↦  -t⁻¹ / log t ^ 2) (.Icc 2 x) := by
    fun_prop (disch := grind [log_ne_zero])
  have : 0 < log x := log_pos (by linarith)
  suffices ∫ t in 2..x, (t⁻¹ / (log t)^2) * E₁ t = ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * f n -
    (log x)⁻¹ * (∑ n ∈ Icc 0 ⌊x⌋₊, f n) - log (log x) + log (log 2) by
    have : (∫ t in 2..x, _) + ∫ t in .Ioi x, _ = ∫ t in .Ioi 2, (t⁻¹ / (log t)^2) * E₁ t :=
      integral_interval_add_Ioi (integrable_mul_E₁ (by rfl)) (integrable_mul_E₁ hx)
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
    apply Integrable.mono (g := fun t ↦ t⁻¹ / (log 2 ^ 2) * C₁)
    · apply (ContinuousOn.integrableOn_Icc _).mono_set Set.Ioc_subset_Icc_self
      fun_prop (disch := grind)
    · exact Measurable.aestronglyMeasurable (by unfold E₁; fun_prop)
    filter_upwards [ae_restrict_mem (by measurability)] with t ht
    simp only [norm_mul, norm_eq_abs, Set.mem_Ioc] at ht ⊢
    grw [f.first_theorem' (by linarith), le_abs_self f.C₁]
    have : 0 < t := by linarith
    gcongr; order
  have : ∫ (t : ℝ) in 2..x, (t⁻¹ / (log t)^2) * log t = log (log x) - log (log 2) := by
    rw [← integral_inv_div_log (by norm_num) (by linarith)]
    exact intervalIntegral.integral_congr fun _ _ ↦ by grind [Set.uIcc_of_le, log_pos]
  rw [sum_mul_eq_sub_integral_mul₁ _ f.map_zero f.map_one x (f := fun t ↦ (log t)⁻¹)]
  · suffices ∫ t in .Ioc 2 x, deriv (fun t ↦ (log t)⁻¹) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k =
        - ∫ t in 2..x, (t⁻¹ / (log t)^2) * ∑ n ∈ Icc 0 ⌊t⌋₊, f n by linarith
    rw [← intervalIntegral.integral_neg, intervalIntegral.integral_of_le hx]
    exact setIntegral_congr_fun (by measurability) (fun _ _ ↦ by simp [field])
  · intro t _
    have : log t ≠ 0 := log_ne_zero.mpr (by grind)
    fun_prop (disch := grind)
  · apply ContinuousOn.integrableOn_Icc
    simpa using hcont

/-- The abstract Mertens second theorem. -/
theorem second_theorem' {x : ℝ} (hx : 2 ≤ x) :
    |f.E₂ x| ≤ C₂ / log x := by
  have hx' : 1 < x := by linarith
  have : 0 < log x := log_pos hx'
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

theorem second_theorem {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - M| ≤ C₂ / log x := by
  grw [← second_theorem' hx, sum_div_log_eq x]; ring_nf; rfl

theorem second_theorem_nat (hN : 2 ≤ N) :
  |∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n - log (log N) - M| ≤ C₂ / log N := by
  simpa using second_theorem (mod_cast (by lia) : 2 ≤ (N : ℝ))

theorem second_theorem_error_bigO_inv_log :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - M)
    =O[atTop] (fun x ↦ (log x)⁻¹) := by
  simp only [isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
  refine ⟨C₂, 2, fun x hx ↦ ?_⟩
  convert second_theorem hx using 1
  grind [abs_of_pos (log_pos (by linarith) : 0 < log x)]

theorem second_theorem_error_bigO_inv_log_nat :
    (fun (N : ℕ) ↦ ∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n - log (log N) - M)
    =O[atTop] (fun N ↦ (log N)⁻¹) := by
  convert! f.second_theorem_error_bigO_inv_log.comp_tendsto tendsto_natCast_atTop_atTop
  simp

theorem second_theorem_error_littleO_one :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - M) =o[atTop] fun _ ↦ (1:ℝ) :=
  f.second_theorem_error_bigO_inv_log.trans_isLittleO inv_log_eq_o_one

theorem second_theorem_error_littleO_one_nat :
    (fun (N : ℕ) ↦ ∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n - log (log N) - M)
    =o[atTop] fun _ ↦ (1 : ℝ) := by
  convert! f.second_theorem_error_littleO_one.comp_tendsto tendsto_natCast_atTop_atTop
  simp

theorem second_theorem_error_bounded : ∃ C, ∀ x ≥ 2,
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x)| ≤ C := by
  refine ⟨ |M| + C₂ / log 2, fun x hx ↦ ?_ ⟩
  have := C₂_nonneg
  grw [← hx, ← f.second_theorem hx, ← abs_add_le]
  ring_nf; rfl

theorem second_theorem_error_bounded_nat : ∃ C, ∀ N : ℕ, N ≥ 2 →
    |∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n - log (log N)| ≤ C := by
  obtain ⟨ C, hC ⟩ := f.second_theorem_error_bounded
  exact ⟨ C, fun N hN ↦ by simpa using hC N (mod_cast hN) ⟩

theorem second_theorem_error_bigO_one :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x)) =O[atTop] fun _ ↦ (1:ℝ) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one, eventually_atTop]
  obtain ⟨ C, _ ⟩ := f.second_theorem_error_bounded
  use C, 2

theorem second_theorem_error_bigO_one_nat :
    (fun N : ℕ ↦ ∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n - log (log N)) =O[atTop] fun _ ↦ (1 : ℝ) := by
  convert! f.second_theorem_error_bigO_one.comp_tendsto tendsto_natCast_atTop_atTop
  simp

theorem second_theorem_asymp :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n) ~[atTop] fun x ↦ log (log x) :=
  (f.second_theorem_error_bigO_one.trans_isLittleO one_eq_o_log_log).isEquivalent

theorem second_theorem_asymp_nat :
    (fun N : ℕ ↦ ∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n) ~[atTop] fun N ↦ log (log N) := by
  convert! f.second_theorem_asymp.comp_tendsto tendsto_natCast_atTop_atTop
  simp

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
noncomputable def vonMangoldt_fun : ℕ → ℝ := fun n ↦ Λ n / n

/-- The bare form of the prime weight.  Should not be directly needed in applications. -/
noncomputable def prime_fun : ℕ → ℝ := fun n ↦ if n.Prime then log n / n else 0

private lemma sum_vonMangoldt_eq : ∑ n ∈ Ioc 0 N, vonMangoldt_fun n = ∑ n ∈ Ioc 0 N, Λ n / n :=
  rfl

private lemma sum_prime_eq : ∑ n ∈ Ioc 0 N, prime_fun n = ∑ p ∈ primesLE N, log p / p := by
  simp [prime_fun, primesLE_eq_filter_Ioc_zero, sum_filter]

private lemma le_mul_sum_vonMangoldt {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * ∑ n ∈ Ioc 0 ⌊x⌋₊, vonMangoldt_fun n := calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by simp [mul_sum, vonMangoldt_fun]; ring_nf
  _ ≥ _ := by
    rw [sum_log_eq_sum_mangoldt]
    gcongr; exacts [vonMangoldt_nonneg, floor_le <| div_nonneg (by linarith) (by linarith)]

private lemma mul_sum_prime_le :
    x * ∑ n ∈ Ioc 0 ⌊x⌋₊, prime_fun n ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n + θ x := calc
  _ = ∑ p ∈ primesLE ⌊x⌋₊, log p * (x / p) := by
    rw [sum_prime_eq, mul_sum]; ring_nf
  _ ≤ ∑ p ∈ primesLE ⌊x⌋₊, log p * (⌊x / p⌋₊ + 1) := by gcongr; exact lt_floor_add_one _|>.le
  _ = ∑ p ∈ primesLE ⌊x⌋₊, log p * ⌊x / p⌋₊ + θ x := by
    simp [mul_add, sum_add_distrib, theta, primesLE_eq_filter_Ioc_zero]
  _ ≤ _ := by
    rw [sum_log_eq_sum_mangoldt, primesLE_eq_filter_Ioc_zero, sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

private lemma sum_prime_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, prime_fun n ≤ log x + log 4 := by
  apply le_of_mul_le_mul_left _ (by linarith : 0 < x)
  grw [mul_sum_prime_le, theta_le_log4_mul_x (by linarith), sum_log_le' hx]
  ring_nf; rfl

/-- The summand defining the constant `E₁` below. -/
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
  have : ∑ n ∈ range N, e₁ n ≤ ∑ n ∈ range (2 * N + 5), e₁ n :=
    sum_le_sum_of_subset_of_nonneg (by grind) (fun n _ _ ↦ e₁_nonneg n)
  have : ∑ n ∈ range (2 * N + 5), e₁ n = log 2 / 2 + log 3 / 6 + ∑ n ∈ .Ico 5 (2 * N + 5), e₁ n
      := by
    convert sum_union (s₁ := {0,1,2,3,4}) (s₂ := .Ico 5 (2 * N + 5)) (by grind [disjoint_left])
    · ext; simp; lia
    simp [e₁, prime_two, prime_three, not_prime_four]
    ring_nf
  have : ∑ n ∈ .Ico 5 (2 * N + 5), e₁ n = ∑ n ∈ .range N, e₁ (2 * n + 5) := by
    apply (sum_of_injOn (2 * · + 5) (by intro; grind) (by intro; grind) _ (by simp)).symm
    simp only [mem_Ico, coe_range, Set.mem_image, Set.mem_Iio, not_exists, not_and, e₁,
      ite_eq_right_iff, div_eq_zero_iff, log_eq_zero, cast_eq_zero, cast_eq_one,
      _root_.mul_eq_zero, and_imp]
    intro p _ _ h hp
    obtain ⟨ m, rfl ⟩ := hp.odd_of_ne_two (by lia)
    specialize h (m - 2)
    lia
  let g : ℝ → ℝ := fun t ↦ log (2 * t + 3) / (2 * t + 3)^2
  have : ∑ n ∈ .range N, e₁ (2 * n + 5) ≤ (5/4) * ∑ n ∈ .range N, g (n + 1) := by
    simp only [e₁, g, cast_add, cast_mul, cast_ofNat, mul_sum]
    gcongr with i hi
    ring_nf
    have : 0 ≤ log (5 + (i : ℝ) * 2) := log_nonneg (by norm_cast; lia)
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
      have : 3 ≤ 2 * t + 3 := by linarith
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
      · convert! ((hasDerivAt_log (by linarith : 2 * x + 3 ≠ 0)).neg).sub_const _ using 1
        grind
      linarith
    have hN : 0 ≤ (N : ℝ) := cast_nonneg' N
    rw [integral_eq_sub_of_hasDerivAt (f := f)]
    · have : 0 ≤ log (3 + N * 2) := log_nonneg (by norm_cast; linarith)
      simp [f]; field_simp; grind
    · simp; grind
    apply ((ContinuousOn.log (f := (2 * · + 3)) (by fun_prop) (by simp; grind)).div₀
      (by fun_prop) _).intervalIntegrable
    simp; grind
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
    apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity))
    gcongr
    apply le_max_right
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
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := e₁_summable.sum_le_tsum _ fun p _ ↦ e₁_nonneg p

/-- The von Mangoldt weight `f : ℕ → ℝ := fun n ↦ Λ n / n`. -/
@[reducible]
noncomputable def Weight.vonMangoldt : Weight := {
  to_fun := vonMangoldt_fun
  map_zero' := by simp [vonMangoldt_fun]
  map_one' := by simp [vonMangoldt_fun]
  lowerBound := -2
  upperBound := log 4 + 1
  le_first' x hx := by
    suffices x * (log x - 2) ≤ x * ∑ n ∈ Ioc 0 ⌊x⌋₊, vonMangoldt_fun n by
      linarith [le_of_mul_le_mul_left this (by linarith)]
    grw [← le_mul_sum_vonMangoldt (by linarith), ← le_sum_log' hx]
    linarith [log_le_self (by linarith : 0 ≤ x)]
  first_le' x hx := by
    unfold vonMangoldt_fun
    linarith [sum_prime_le hx, E₁_le, sum_vonMangoldt_le_sum_prime_add_E₁ hx,
      sum_prime_eq ⌊x⌋₊]
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

/-- The prime weight `f : ℕ → ℝ := fun n ↦ 1 / n` if `n` is prime and `0` otherwise. -/
@[reducible]
noncomputable def Weight.prime : Weight := {
  to_fun := prime_fun
  map_zero' := by simp [prime_fun]
  map_one' := by simp [prime_fun]
  lowerBound := -3
  upperBound := log 4
  le_first' x hx := by
    have : -2 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x := Weight.vonMangoldt.le_first' x hx
    linarith [E₁_le, sum_vonMangoldt_le_sum_prime_add_E₁ hx, sum_prime_eq ⌊x⌋₊]
  first_le' x hx := by linarith [sum_prime_le hx]
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
    linarith [le_of_mul_le_mul_left this (by norm_cast; lia)]
  have := le_mul_sum_vonMangoldt (mod_cast (by lia) : 0 ≤ (N : ℝ))
  simp only [floor_natCast, Weight.vonMangoldt_apply, vonMangoldt_fun] at this ⊢
  grw [← this, ←le_sum_log_nat]
  ring_nf; rfl

theorem le_sum_log_prime_div_sub (hx : 1 ≤ x) : - 3 ≤ ∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x
    := (sum_prime_eq _).symm ▸ Weight.prime.le_first' x hx

/-- A sharper lower bound in the case of natural numbers. -/
theorem le_sum_log_prime_div_sub_nat : - 2 ≤ ∑ p ∈ primesLE N, log p / p - log N := by
  by_cases! hN : N = 0
  · simp [hN]
  have := sum_vonMangoldt_le_sum_prime_add_E₁ (mod_cast (by lia) : 1 ≤ (N : ℝ))
  simp at this
  linarith [le_sum_vonMangoldt_div_sub_nat N, E₁_le]

theorem sum_vonMangoldt_div_sub_le (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x ≤ log 4 + 1
    := Weight.vonMangoldt.first_le' x hx

theorem sum_log_prime_div_sub_le (hx : 1 ≤ x) : ∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x ≤ log 4
    := (sum_prime_eq _).symm ▸ Weight.prime.first_le' x hx

theorem abs_sum_vonMangoldt_div_sub_le (hx : 1 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x| ≤ log 4 + 1 := by
    convert! Weight.vonMangoldt.first_theorem hx
    rw [Weight.vonMangoldt_C₁_eq]

theorem abs_sum_vonMangoldt_div_sub_le_nat :
    |∑ n ∈ Ioc 0 N, Λ n / n - log N| ≤ log 4 + 1 := by
    convert! Weight.vonMangoldt.first_theorem_nat N
    rw [Weight.vonMangoldt_C₁_eq]

theorem abs_sum_log_prime_div_sub_le (hx : 1 ≤ x) :
    |∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x| ≤ 3 := by
    convert! (sum_prime_eq _).symm ▸ Weight.prime.first_theorem hx
    rw [Weight.prime_C₁_eq]

/-- A sharper bound in the case of natural numbers. -/
theorem abs_sum_log_prime_div_sub_le_nat : |∑ p ∈ primesLE N, log p / p - log N| ≤ 2 := by
  by_cases! hN : N = 0
  · simp [hN]
  have : 1 ≤ (N:ℝ) := mod_cast (by lia)
  rw [abs_le']; constructor
  · trans log 4
    · simpa using sum_log_prime_div_sub_le this
    linarith [log_four_eq, log_two_lt_d9]
  linarith [le_sum_log_prime_div_sub_nat N]

theorem sum_vonMangoldt_div_sub_bounded : (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x)
    =O[atTop] (fun _ ↦ (1 : ℝ)) := Weight.vonMangoldt.first_theorem_error_bounded

theorem sum_vonMangoldt_div_sub_bounded_nat : (fun N ↦ ∑ n ∈ Ioc 0 N, Λ n / n - log N)
    =O[atTop] fun _ ↦ (1 : ℝ) := Weight.vonMangoldt.first_theorem_error_bounded_nat

theorem sum_log_prime_div_sub_bounded : (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x)
    =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  convert Weight.prime.first_theorem_error_bounded using 3; rw [← sum_prime_eq]; rfl

theorem sum_log_prime_div_sub_bounded_nat : (fun N ↦ ∑ p ∈ primesLE N, log p / p - log N)
    =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  convert Weight.prime.first_theorem_error_bounded_nat using 3; rw [← sum_prime_eq]; rfl

theorem sum_vonMangoldt_div_asymp : (∑ n ∈ Ioc 0 ⌊·⌋₊, Λ n / n) ~[atTop] log :=
  Weight.vonMangoldt.first_theorem_asymp

theorem sum_vonMangoldt_div_asymp_nat : (∑ n ∈ Ioc 0 ·, Λ n / n) ~[atTop] (log ↑·) :=
  Weight.vonMangoldt.first_theorem_asymp_nat

theorem sum_log_prime_div_asymp : (∑ p ∈ primesLE ⌊·⌋₊, log p / p) ~[atTop] log := by
  convert Weight.prime.first_theorem_asymp using 2; rw [← sum_prime_eq]; rfl

theorem sum_log_prime_div_asymp_nat : (∑ p ∈ primesLE ·, log p / p) ~[atTop] (log ↑·) := by
  convert Weight.prime.first_theorem_asymp_nat using 2; rw [← sum_prime_eq]; rfl

end FirstTheorem

section SecondTheorem

/-
## The second Mertens theorem

We give most of the second Mertens theorem here, except that the proof that
`Weight.vonMangoldt.M = eulerMascheroni` is currently missing.  Once that theorem is
added, the relevant versions of the second Mertens theorem will be migrated to after
that theorem.
-/

variable {x : ℝ} (N : ℕ)

private lemma Weight.vonMangoldt_sum_inv_log_mul_eq {N : ℕ} :
    ∑ n ∈ Ioc 0 N, (log n)⁻¹ * Weight.vonMangoldt n = ∑ n ∈ Ioc 0 N, Λ n / (n * log n) := by
  congr! 1 with n hn
  simp; field

private lemma Weight.prime_sum_inv_log_mul_eq {N : ℕ} :
    ∑ n ∈ Ioc 0 N, (log n)⁻¹ * Weight.prime n = ∑ p ∈ primesLE N, 1 / (p : ℝ) := by
  simp only [Weight.prime_apply, mul_ite, mul_zero, primesLE_eq_filter_Ioc_zero, one_div,
    sum_filter]
  congr! 2 with p h hp
  have : 0 < log p := log_pos (mod_cast hp.one_lt)
  field_simp

/-- Preliminary version - will be migrated once `Weight.vonMangoldt.M` is proven to
equal `eulerMascheroni` -/
theorem sum_vonMangoldt_div_mul_log_bound (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - log (log x) - Weight.vonMangoldt.M| ≤
      (log 4 + 3) / log x := by
    convert! Weight.vonMangoldt.second_theorem hx using 2
    · rw [Weight.vonMangoldt_sum_inv_log_mul_eq]
    simp

/-- Preliminary version - will be migrated once `Weight.vonMangoldt.M` is proven to
equal `eulerMascheroni` -/
theorem sum_vonMangoldt_div_mul_log_bound_nat (hN : 2 ≤ N) :
    |∑ n ∈ Ioc 0 N, Λ n / (n * log n) - log (log N) - Weight.vonMangoldt.M| ≤
      (log 4 + 3) / log N := by
    convert sum_vonMangoldt_div_mul_log_bound (x := ↑N) (mod_cast hN)
    simp

theorem sum_prime_div_mul_log_bound (hx : 2 ≤ x) :
    |∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ) - log (log x) - Weight.prime.M| ≤
      (log 4 + 3) / log x := by
    convert! Weight.prime.second_theorem hx using 2
    · rw [Weight.prime_sum_inv_log_mul_eq]
    simp

theorem sum_prime_div_mul_log_bound_nat (hN : 2 ≤ N) :
    |∑ p ∈ primesLE N, 1 / (p : ℝ) - log (log N) - Weight.prime.M| ≤
      (log 4 + 3) / log N := by
    convert sum_prime_div_mul_log_bound (x := ↑N) (mod_cast hN)
    simp

/-- Preliminary version - will be migrated once `Weight.vonMangoldt.M` is proven to
equal `eulerMascheroni` -/
theorem sum_vonMangoldt_div_mul_log_bound_bigO_inv_log :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - log (log x) - Weight.vonMangoldt.M)
    =O[atTop] fun x ↦ (log x)⁻¹ := by
  convert Weight.vonMangoldt.second_theorem_error_bigO_inv_log using 4
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

/-- Preliminary version - will be migrated once `Weight.vonMangoldt.M` is proven to
equal `eulerMascheroni` -/
theorem sum_vonMangoldt_div_mul_log_bound_bigO_inv_log_nat :
    (fun (N : ℕ) ↦ ∑ n ∈ Ioc 0 N, Λ n / (n * log n) - log (log N) - Weight.vonMangoldt.M)
    =O[atTop] (fun N ↦ (log N)⁻¹) := by
  convert Weight.vonMangoldt.second_theorem_error_bigO_inv_log_nat using 4
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

theorem sum_prime_div_mul_log_bound_bigO_inv_log :
    (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ) - log (log x) - Weight.prime.M)
    =O[atTop] fun x ↦ (log x)⁻¹ := by
  convert Weight.prime.second_theorem_error_bigO_inv_log using 4
  rw [Weight.prime_sum_inv_log_mul_eq]

theorem sum_prime_div_mul_log_bound_bigO_inv_log_nat :
    (fun (N : ℕ) ↦ ∑ p ∈ primesLE N, 1 / (p : ℝ) - log (log N) - Weight.prime.M)
    =O[atTop] (fun N ↦ (log N)⁻¹) := by
  convert Weight.prime.second_theorem_error_bigO_inv_log_nat using 4
  rw [Weight.prime_sum_inv_log_mul_eq]

/-- Preliminary version - will be migrated once `Weight.vonMangoldt.M` is proven to
equal `eulerMascheroni` -/
theorem sum_vonMangoldt_div_mul_log_bound_littleO_one :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - log (log x) - Weight.vonMangoldt.M)
    =o[atTop] (fun _ ↦ (1:ℝ)) := by
  convert Weight.vonMangoldt.second_theorem_error_littleO_one using 4
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

/-- Preliminary version - will be migrated once `Weight.vonMangoldt.M` is proven to
equal `eulerMascheroni` -/
theorem sum_vonMangoldt_div_mul_log_bound_littleO_one_nat :
    (fun (N : ℕ) ↦ ∑ n ∈ Ioc 0 N, Λ n / (n * log n) - log (log N) - Weight.vonMangoldt.M)
    =o[atTop] (fun _ ↦ (1:ℝ)) := by
  convert Weight.vonMangoldt.second_theorem_error_littleO_one_nat using 4
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

theorem sum_prime_div_mul_log_bound_littleO_one :
    (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ) - log (log x) - Weight.prime.M)
    =o[atTop] (fun _ ↦ (1:ℝ)) := by
  convert Weight.prime.second_theorem_error_littleO_one using 4
  rw [Weight.prime_sum_inv_log_mul_eq]

theorem sum_prime_div_mul_log_bound_littleO_one_nat :
    (fun (N : ℕ) ↦ ∑ p ∈ primesLE N, 1 / (p : ℝ) - log (log N) - Weight.prime.M)
    =o[atTop] (fun _ ↦ (1:ℝ)) := by
  convert Weight.prime.second_theorem_error_littleO_one_nat using 4
  rw [Weight.prime_sum_inv_log_mul_eq]

theorem sum_vonMangoldt_div_mul_log_bound_bigO_one :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
  convert Weight.vonMangoldt.second_theorem_error_bigO_one using 3
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

theorem sum_vonMangoldt_div_mul_log_bound_bigO_one_nat
    : (fun (N : ℕ) ↦ ∑ n ∈ Ioc 0 N, Λ n / (n * log n) - log (log N)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
  convert Weight.vonMangoldt.second_theorem_error_bigO_one_nat using 3
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

theorem sum_prime_div_mul_log_bound_bigO_one :
    (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ) - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
  convert Weight.prime.second_theorem_error_bigO_one using 3
  rw [Weight.prime_sum_inv_log_mul_eq]

theorem sum_prime_div_mul_log_bound_bigO_one_nat
    : (fun (N : ℕ) ↦ ∑ p ∈ primesLE N, 1 / (p : ℝ) - log (log N)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
  convert Weight.prime.second_theorem_error_bigO_one_nat using 3
  rw [Weight.prime_sum_inv_log_mul_eq]

theorem sum_vonMangoldt_div_mul_log_bound_asymp :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n)) ~[atTop] (fun x ↦ log (log x)) := by
  convert Weight.vonMangoldt.second_theorem_asymp using 2
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

theorem sum_vonMangoldt_div_mul_log_bound_asymp_nat :
    (fun (N : ℕ) ↦ ∑ n ∈ Ioc 0 N, Λ n / (n * log n)) ~[atTop] (fun N ↦ log (log N)) := by
  convert Weight.vonMangoldt.second_theorem_asymp_nat using 2
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

theorem sum_prime_div_mul_log_bound_asymp :
    (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ)) ~[atTop] (fun x ↦ log (log x)) := by
  convert Weight.prime.second_theorem_asymp using 2
  rw [Weight.prime_sum_inv_log_mul_eq]

theorem sum_prime_div_mul_log_bound_asymp_nat :
    (fun (N : ℕ) ↦ ∑ p ∈ primesLE N, 1 / (p : ℝ)) ~[atTop] (fun N ↦ log (log N)) := by
  convert Weight.prime.second_theorem_asymp_nat using 2
  rw [Weight.prime_sum_inv_log_mul_eq]

end SecondTheorem

end Mertens
