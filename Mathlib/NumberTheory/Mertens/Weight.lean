/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Pietro Monticone, Robby Sneiderman, Guiseppe Sorge, Terence Tao,
Yan Yablonovskiy, Yi Yuan
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.PrimesInAP

import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic.NormNum.Prime

/-!
# Mertens weights: abstract theory

We introduce the notion of a *Mertens weight*: a function `f : ℕ → ℝ` vanishing at `0` and `1`
that obeys upper and lower bounds on `∑ n ∈ Icc 0 ⌊x⌋₊, f n - log x`, and develop the abstract
theory (the error terms `E₁`, `E₂` and the associated asymptotics).

The main results are:

- **Abstract Mertens first theorem**: `∑ n ∈ Icc 0 ⌊x⌋₊, f n = log x + O(1)` for `1 ≤ x`
  (essentially tautological from the weight axioms).
- **Abstract Mertens second theorem**:
  `∑ n ∈ Icc 0 ⌊x⌋₊, f n / log n = log log x + M + O(1 / log x)` for `2 ≤ x` and some explicit
  constant `M` (via an Abel summation argument).

Multiple versions are given, with various error-term precision and with `x` either `Real` or `Nat`.

The two specific Mertens weights (von Mangoldt and prime) are constructed in
`Mathlib.NumberTheory.Mertens.Construction`, and the classical theorems are derived in
`Mathlib.NumberTheory.Mertens.Theorems`.
-/

@[expose] public section

namespace Mertens

open Nat hiding log log_pos
open Finset Filter Real Chebyshev intervalIntegral Asymptotics MeasureTheory Topology
  Measurable ContinuousOn
open ArithmeticFunction hiding log
open scoped Nat.Prime

variable {x t : ℝ}

private lemma inv_div_log_sq_nonneg (ht : t ∈ Set.Ioi x) (hx : 1 < x) : 0 ≤ t⁻¹ / (log t)^2 := by
  positivity [(by grind : 0 < t)]

private lemma integrable_const_div_mul_log_sq (C : ℝ) (hx : 2 ≤ x) :
    IntegrableOn (fun t ↦ (t⁻¹ / (log t)^2) * C) (.Ioi x) volume :=
  (integrableOn_inv_div_log_sq_Ioi (by linarith)).mul_const _

private lemma integ_div_mul_log_sq (C : ℝ) (hx : 2 ≤ x) :
    ∫ t in .Ioi x, (t⁻¹ / (log t)^2) * C = C / log x := by
  rw [MeasureTheory.integral_mul_const, integral_inv_div_log_sq_Ioi (by linarith)]
  field

/-- A weight `f` is a bundled function `f : ℕ → ℝ` for which the quantity
`∑ n ∈ Icc 0 ⌊x⌋₊, f n - log x` is bounded above and below for `x ≥ 1`, which vanishes
at `0` and `1`, and does not grow faster than `log n / n`.
-/
structure Weight where
  /-- The underlying function -/
  f : ℕ → ℝ
  map_zero' : f 0 = 0
  map_one' : f 1 = 0
  /-- The lower bound for the first Mertens error. -/
  lowerBound : ℝ
  /-- The upper bound for the first Mertens error. -/
  upperBound : ℝ
  le_first' : ∀ x ≥ 1, lowerBound ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, f n - log x
  first_le' : ∀ x ≥ 1, ∑ n ∈ Ioc 0 ⌊x⌋₊, f n - log x ≤ upperBound
  /-- A constant for the pointwise bound on the function -/
  C₀ : ℝ
  f_bound (n : ℕ) : |f n| ≤ C₀ * log n / n

noncomputable instance instCoefn : CoeFun Weight (fun _ ↦ ℕ → ℝ) where coe (w: Weight) := w.f

namespace Weight

open intervalIntegral

variable (f : Weight) (x : ℝ) (n N : ℕ) {t : ℝ}

@[simp] lemma map_zero : f 0 = 0 := f.map_zero'
@[simp] lemma map_one : f 1 = 0 := f.map_one'

/-- The first Mertens error for a weight `f` is defined as
`f.E₁ x = ∑ n ∈ Ioc 0 ⌊x⌋₊, f n - log x`. -/
noncomputable def E₁ := ∑ n ∈ Ioc 0 ⌊x⌋₊, f n - log x

lemma sum_eq : ∑ n ∈ Ioc 0 ⌊x⌋₊, f n = log x + f.E₁ x := by grind [E₁]

lemma sum_eq' : ∑ n ∈ Icc 0 ⌊x⌋₊, f n = log x + f.E₁ x := by
  simpa [← add_sum_Ioc_eq_sum_Icc] using f.sum_eq x

lemma sum_eq_nat : ∑ n ∈ Ioc 0 N, f n = log N + f.E₁ N := by simpa using f.sum_eq N

lemma le_first (ht : t ≥ 1) : f.lowerBound ≤ f.E₁ t := f.le_first' t ht

lemma first_le (ht : t ≥ 1) : f.E₁ t ≤ f.upperBound := f.first_le' t ht

lemma apply_bound : |f n| ≤ f.C₀ * log n / n := f.f_bound n

lemma hi_nonneg : 0 ≤ f.upperBound := by
  simpa [(by rfl : Icc 0 1 = {0, 1})] using f.first_le' 1 (by rfl)

lemma lo_nonpos : f.lowerBound ≤ 0 := by
  simpa [(by rfl : Icc 0 1 = {0, 1})] using f.le_first' 1 (by rfl)

lemma C₀_nonneg : 0 ≤ f.C₀ := by
  refine le_of_mul_le_mul_of_pos_right ?_ (by positivity : 0 < log (2 : ℕ) / (2 : ℕ))
  grw [← mul_div_assoc f.C₀, ← apply_bound f 2]
  simp

/-- An absolute value bound for the first Mertens error. -/
noncomputable def C₁ := max (-f.lowerBound) f.upperBound

/-- An absolute value bound (after dividing by `log x`) for the second Mertens error. -/
noncomputable def C₂ := f.upperBound - f.lowerBound

lemma C₁_nonneg : 0 ≤ f.C₁ := by simp [C₁, hi_nonneg, lo_nonpos]

lemma C₂_nonneg : 0 ≤ f.C₂ := by grind [C₂, hi_nonneg, lo_nonpos]

/-- The abstract Mertens first theorem. -/
theorem E₁_bound {x : ℝ} (hx : 1 ≤ x) : |f.E₁ x| ≤ f.C₁ := by
  grw [abs_le, ← f.le_first hx, f.first_le hx]; grind [C₁]

theorem sum_sub_log_bound {x : ℝ} (hx : 1 ≤ x) : |∑ n ∈ Ioc 0 ⌊x⌋₊, f n - log x| ≤ f.C₁ := by
  simpa [f.sum_eq x] using f.E₁_bound hx

theorem sum_sub_log_bound_nat : |∑ n ∈ Ioc 0 N, f n - log N| ≤ f.C₁ := by
  by_cases! N = 0
  · simp [*, C₁_nonneg]
  simpa using f.sum_sub_log_bound (mod_cast (by omega) : 1 ≤ (N : ℝ))

theorem sum_sub_log_bounded : (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, f n - log x)
    =O[atTop] fun _ ↦ (1 : ℝ) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one, eventually_atTop]
  exact ⟨f.C₁, 1, fun _ ↦ f.sum_sub_log_bound⟩

theorem sum_sub_log_bounded_nat : (fun N ↦ ∑ n ∈ Ioc 0 N, f n - log N)
    =O[atTop] fun _ ↦ (1 : ℝ) := by
  convert! f.sum_sub_log_bounded.comp_tendsto tendsto_natCast_atTop_atTop; simp

theorem sum_asymp : (∑ n ∈ Ioc 0 ⌊·⌋₊, f n) ~[atTop] log :=
  f.sum_sub_log_bounded.trans_isLittleO (isLittleO_const_log_atTop)|>.isEquivalent

theorem sum_asymp_nat : (∑ n ∈ Ioc 0 ·, f n) ~[atTop] (log ↑·) := by
  convert! f.sum_asymp.comp_tendsto tendsto_natCast_atTop_atTop; simp

/-- The Meissel--Mertens constant associated to a weight `f` is defined as
`M = (∫ t in .Ioi 2, (t⁻¹ / (log t)^2) * E₁ t) + 1 - log (log 2)`.
-/
noncomputable def M := (∫ t in .Ioi 2, (t⁻¹ / (log t)^2) * f.E₁ t) + 1 - log (log 2)

/-- The second Mertens error for a weight `f` is defined as
`E₂ x = ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - M`. -/
noncomputable def E₂ := ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - f.M

lemma sum_div_log_eq' : ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * f n = log (log x) + f.M + f.E₂ x := by
  grind [E₂]

lemma sum_div_log_eq : ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n = log (log x) + f.M + f.E₂ x := by
  simpa [← add_sum_Ioc_eq_sum_Icc, map_zero] using f.sum_div_log_eq' x

lemma integrable_mul_E₁ {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn (fun t ↦ (t⁻¹ / (log t)^2) * f.E₁ t) (.Ioi x) volume := by
  apply Integrable.mono (integrable_const_div_mul_log_sq f.C₁ hx)
    (aestronglyMeasurable (by unfold E₁; fun_prop))
  filter_upwards [ae_restrict_mem (by measurability)] with t ht
  simp only [Set.mem_Ioi, norm_mul, norm_eq_abs] at ht ⊢
  have : 0 < log t := log_pos (by linarith)
  grw [f.E₁_bound (by linarith), le_abs_self f.C₁]

/-- General upper and lower bounds for the Meissel--Mertens constant. -/
theorem M_bounds : f.M ≤ f.upperBound / log 2 + 1 - log (log 2) ∧
    f.lowerBound / log 2 + 1 - log (log 2) ≤ f.M := by
  unfold M
  rw [← integ_div_mul_log_sq, ← integ_div_mul_log_sq] <;> try rfl
  have := f.integrable_mul_E₁ (by rfl)
  have : NullMeasurableSet (.Ioi (2 : ℝ)) volume := by measurability
  constructor <;> gcongr with t ht
  exacts [integrable_const_div_mul_log_sq _ (by rfl), inv_div_log_sq_nonneg ht (by norm_num),
    f.first_le (by grind), integrable_const_div_mul_log_sq _ (by rfl),
    inv_div_log_sq_nonneg ht (by norm_num), f.le_first (by grind)]

/-- Expresses the error term `E₂` in terms of `E₁`. -/
theorem E₂_eq {x : ℝ} (hx : 2 ≤ x) :
    f.E₂ x = (log x)⁻¹ * f.E₁ x - ∫ t in .Ioi x, (t⁻¹ / (log t)^2) * f.E₁ t := by
  -- a weird bug - if I move `hcont` too far into the proof, the `grind` discharger breaks.
  -- discussion https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Strange.20.60fun_prop.60.20behavior
  have hcont : ContinuousOn (fun t ↦  -t⁻¹ / log t ^ 2) (.Icc 2 x) := by
    fun_prop (disch := grind [log_ne_zero])
  have : 0 < log x := log_pos (by linarith)
  suffices ∫ t in 2..x, (t⁻¹ / (log t)^2) * f.E₁ t = ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * f n -
      (log x)⁻¹ * (∑ n ∈ Icc 0 ⌊x⌋₊, f n) - log (log x) + log (log 2) by
    grind [E₂, M, integral_interval_add_Ioi (f.integrable_mul_E₁ le_rfl) (f.integrable_mul_E₁ hx),
      f.sum_eq']
  have : ∫ t in 2..x, (t⁻¹ / (log t)^2) * ∑ n ∈ Icc 0 ⌊t⌋₊, f n =
      (∫ t in 2..x, (t⁻¹ / (log t)^2) * log t) + ∫ t in 2..x, (t⁻¹ / (log t)^2) * f.E₁ t := by
    simp only [sum_eq', mul_add]
    apply intervalIntegral.integral_add <;> rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    · apply (integrableOn_Icc _).mono_set Set.Ioc_subset_Icc_self
      fun_prop (disch := grind [log_ne_zero])
    · apply Integrable.mono (g := fun t ↦ t⁻¹ / (log 2 ^ 2) * f.C₁)
      · apply (integrableOn_Icc _).mono_set Set.Ioc_subset_Icc_self
        fun_prop (disch := grind)
      · exact aestronglyMeasurable (by unfold E₁; fun_prop)
      · filter_upwards [ae_restrict_mem (by measurability)] with t ht
        simp only [norm_mul, norm_eq_abs, Set.mem_Ioc] at ht ⊢
        grw [f.E₁_bound (by linarith), le_abs_self f.C₁]
        have : 0 < t := by linarith
        gcongr; order
  have : ∫ t in 2..x, (t⁻¹ / (log t)^2) * log t = log (log x) - log (log 2) := by
    rw [← integral_inv_div_log (by norm_num) (by linarith)]
    exact integral_congr fun _ _ ↦ by grind [Set.uIcc_of_le, log_pos]
  -- the main step: apply Abel summation
  rw [sum_mul_eq_sub_integral_mul₁ _ f.map_zero f.map_one x (f := fun t ↦ (log t)⁻¹)]
  · suffices ∫ t in .Ioc 2 x, deriv (fun t ↦ (log t)⁻¹) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k =
        - ∫ t in 2..x, (t⁻¹ / (log t)^2) * ∑ n ∈ Icc 0 ⌊t⌋₊, f n by linarith
    rw [← intervalIntegral.integral_neg, integral_of_le hx]
    exact setIntegral_congr_fun (by measurability) (fun _ _ ↦ by simp [field])
  · intro t _
    have : log t ≠ 0 := log_ne_zero.mpr (by grind)
    fun_prop (disch := grind)
  · exact integrableOn_Icc (by simpa using hcont)

/-- The abstract Mertens second theorem. -/
theorem E₂_bound {x : ℝ} (hx : 2 ≤ x) : |f.E₂ x| ≤ f.C₂ / log x := by
  have hx' : 1 < x := by linarith
  have := log_pos hx'
  have := f.integrable_mul_E₁ hx
  have : NullMeasurableSet (.Ioi x) volume := by measurability
  rw [f.E₂_eq hx, abs_le, C₂]
  constructor
  · calc
      _ ≥ (log x)⁻¹ * f.lowerBound - ∫ t in .Ioi x, (t⁻¹ / (log t)^2) * f.upperBound := by
        gcongr with t ht
        exacts [f.le_first hx'.le, integrable_const_div_mul_log_sq _ hx,
          inv_div_log_sq_nonneg ht hx', f.first_le (by grind)]
      _ = _ := by simp [integ_div_mul_log_sq _ hx, field]
  · calc
      _ ≤ (log x)⁻¹ * f.upperBound - ∫ t in .Ioi x, (t⁻¹ / (log t)^2) * f.lowerBound := by
        gcongr with t ht
        exacts [f.first_le hx'.le, integrable_const_div_mul_log_sq _ hx,
          inv_div_log_sq_nonneg ht hx', f.le_first (by grind)]
      _ = _ := by simp [integ_div_mul_log_sq _ hx, field]

/-- This bound is needed to establish some integrability properties of `f.E₂`. -/
private theorem E₂_bound_weak {x : ℝ} (hx : 1 ≤ x) :
   |f.E₂ x| ≤ |log (log x)| + |f.M| + f.C₂ / log 2 := by
  have := f.C₂_nonneg
  rcases le_or_gt 2 x with hx' | hx'
  · grw [f.E₂_bound hx', hx', le_add_iff_nonneg_left]
    positivity
  unfold E₂
  grw [abs_sub, abs_sub, sum_eq_zero, abs_zero, zero_add, le_add_iff_nonneg_right]
  · exact div_nonneg f.C₂_nonneg (log_nonneg one_le_two)
  intro n hn
  grw [mem_Icc, le_floor_iff (by linarith), hx'] at hn
  rcases (by simp_all; omega : n = 0 ∨ n = 1) with rfl | rfl <;> simp

theorem sum_div_log_sub_sub_bound {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - f.M| ≤ f.C₂ / log x := by
  grw [← f.E₂_bound hx, f.sum_div_log_eq x]; grind

theorem sum_div_log_sub_sub_bound_nat (hN : 2 ≤ N) :
    |∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n - log (log N) - f.M| ≤ f.C₂ / log N := by
  simpa using f.sum_div_log_sub_sub_bound (mod_cast (by omega) : 2 ≤ (N : ℝ))

theorem sum_div_log_sub_sub_isBigO : (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - f.M)
    =O[atTop] fun x ↦ (log x)⁻¹ := by
  simp only [isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
  refine ⟨f.C₂, 2, fun x hx ↦ ?_⟩
  convert f.sum_div_log_sub_sub_bound hx using 1
  grind [abs_of_pos (log_pos (by linarith : 1 < x))]

theorem sum_div_log_sub_sub_isBigO_nat : (fun (N : ℕ) ↦ ∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n
    - log (log N) - f.M) =O[atTop] fun N ↦ (log N)⁻¹ := by
  simpa [Function.comp_def] using
    f.sum_div_log_sub_sub_isBigO.comp_tendsto tendsto_natCast_atTop_atTop

theorem sum_div_log_sub_sub_isLittleO : (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n
    - log (log x) - f.M) =o[atTop] fun _ ↦ (1 : ℝ) :=
  f.sum_div_log_sub_sub_isBigO.trans_isLittleO inv_log_isLittleO_one

theorem sum_div_log_sub_sub_isLittleO_nat : (fun (N : ℕ) ↦ ∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n
    - log (log N) - f.M) =o[atTop] fun _ ↦ (1 : ℝ) := by
  simpa [Function.comp_def] using
    f.sum_div_log_sub_sub_isLittleO.comp_tendsto tendsto_natCast_atTop_atTop

theorem sum_div_log_sub_bounded : ∃ C, ∀ x ≥ 2,
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x)| ≤ C := by
  refine ⟨ |f.M| + f.C₂ / log 2, fun x hx ↦ ?_ ⟩
  have := f.C₂_nonneg
  grw [← hx, ← f.sum_div_log_sub_sub_bound hx, ← abs_add_le]
  simp [field]

theorem sum_div_log_sub_bounded_nat : ∃ C, ∀ N : ℕ, N ≥ 2 →
    |∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n - log (log N)| ≤ C := by
  obtain ⟨ C, hC ⟩ := f.sum_div_log_sub_bounded
  exact ⟨ C, fun N hN ↦ by simpa using hC N (mod_cast hN) ⟩

theorem sum_div_log_sub_isBigO : (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n
    - log (log x)) =O[atTop] fun _ ↦ (1 : ℝ) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one, eventually_atTop]
  obtain ⟨ C, _ ⟩ := f.sum_div_log_sub_bounded
  use C, 2

theorem sum_div_log_sub_isBigO_nat : (fun N : ℕ ↦ ∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n
    - log (log N)) =O[atTop] fun _ ↦ (1 : ℝ) := by
  simpa [Function.comp_def] using f.sum_div_log_sub_isBigO.comp_tendsto tendsto_natCast_atTop_atTop

theorem sum_div_log_asymp : (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n) ~[atTop]
    fun x ↦ log (log x) :=
  (f.sum_div_log_sub_isBigO.trans_isLittleO one_isLittleO_log_log).isEquivalent

theorem sum_div_log_asymp_nat : (fun N : ℕ ↦ ∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n) ~[atTop]
    fun N ↦ log (log N) := by
  simpa [Function.comp_def] using f.sum_div_log_asymp.comp_tendsto tendsto_natCast_atTop_atTop

open ENNReal

/-- A formula for the Dirichlet series associated to Mertens' second theorem, with exact
error term. -/
theorem sum_div_log_mul_pow_eq {s : ℝ} (hs : 1 < s) :
    ∑' n : ℕ, (log n)⁻¹ * f n * n ^ (1 - s) = - log (s - 1) - eulerMascheroniConstant + f.M
    + ∫ x in .Ioi 1, (f.E₂ (x ^ (s - 1)⁻¹)) * x ^ (-2 : ℝ) := calc
  _ = ∑' n : ℕ, ∫ x in .Ioi 1, (log n)⁻¹ * f n * (Set.Ioi ↑n).indicator
      (fun x ↦ ((s - 1) * x ^ (-s))) x := by
    congr! with n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have : max 1 (n : ℝ) = n := mod_cast (by omega)
    simp only [MeasureTheory.integral_const_mul, measurableSet_Ioi, setIntegral_indicator,
      Set.Ioi_inter_Ioi, this, mul_eq_mul_left_iff, _root_.mul_eq_zero, inv_eq_zero, log_eq_zero,
      cast_eq_zero, cast_eq_one]
    rw [integral_Ioi_rpow_of_lt] <;> grind
  _ = ∫ x in .Ioi 1, ∑' n : ℕ, (log n)⁻¹ * f n * (Set.Ioi ↑n).indicator
      (fun x ↦ ((s - 1) * x ^ (-s))) x := by
    rw [integral_tsum]
    · exact fun _ ↦ aestronglyMeasurable (by fun_prop (disch := measurability))
    · simp_rw [enorm_mul, ne_eq, ←lt_top_iff_ne_top, enorm_indicator_eq_indicator_enorm]
      calc
        _ = ∑' (i : ℕ), .ofReal (|(log i)⁻¹| * |f i| * (↑i)^(1 - s)) := by
          congr! with n
          rcases eq_or_ne n 0 with rfl | hn
          · simp
          have : max (n : ℝ) 1 = n := mod_cast (by omega)
          rw [lintegral_const_mul' _ _ (by finiteness), setLIntegral_indicator measurableSet_Ioi,
            Set.Ioi_inter_Ioi, this, ← ofReal_integral_norm_eq_lintegral_enorm]
          · simp only [enorm_eq_ofReal_abs, abs_inv, norm_mul, norm_eq_abs,
            MeasureTheory.integral_const_mul]
            rw [setIntegral_congr_fun (g := (· ^ (- s))) (by measurability),
              integral_Ioi_rpow_of_lt (by linarith) (by positivity)]
            · rw [← ofReal_mul, ← ofReal_mul, abs_of_nonneg (a := s - 1)]
              <;> first | positivity | grind
            · intro x _
              have : 0 ≤ x := by grind
              exact abs_of_nonneg (by positivity)
          · apply Integrable.const_mul (integrableOn_Ioi_rpow_of_lt ..) <;> grind
        _ ≤ ∑' (i : ℕ), ENNReal.ofReal (f.C₀ * (i : ℝ)^(-s)) := by
          refine ENNReal.tsum_le_tsum fun n ↦ ofReal_le_ofReal ?_
          rcases eq_or_ne n 0 with rfl | _
          · simp [zero_rpow (by grind : -s ≠ 0)]
          rcases eq_or_ne n 1 with rfl | _
          · simp [f.C₀_nonneg]
          have : 0 < log n := log_pos (mod_cast (by omega))
          grw [f.apply_bound n, abs_of_nonneg (by positivity)]
          field_simp
          rw [mul_assoc, ← rpow_one_add'] <;> grind
        _ < ⊤ := by
          simp_rw [ofReal_mul f.C₀_nonneg, ENNReal.tsum_mul_left]
          suffices ∑' (i : ℕ), ENNReal.ofReal (i ^ (-s)) < ⊤ by finiteness
          exact (summable_nat_rpow.mpr (by linarith)).tsum_ofReal_lt_top
  _ = ∫ x in .Ioi 1, (∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * f n) * ((s - 1) * x ^ (-s)) := by
    apply setIntegral_congr_ae (by measurability)
    have : ∀ᵐ (x : ℝ), ∀ n : ℕ, x ≠ n :=
      eventually_countable_forall.mpr fun n ↦ Measure.ae_ne volume (n : ℝ)
    filter_upwards [this] with x hx
    intro hx'
    calc
      _ = ∑' n, Set.indicator (Icc 0 ⌊x⌋₊)
          (fun (n : ℕ) ↦ (log n)⁻¹ * f n * (s - 1) * x ^ (-s)) n := by
        grind [Set.indicator, coe_Icc, le_floor_iff (by grind : 0 ≤ x)]
      _ = _ := by simp_rw [← sum_eq_tsum_indicator, ← sum_mul]; ring
  _ = (s - 1) * ∫ x in .Ioi 1, log (log x) * x ^ (-s) + f.M * x ^ (-s) + f.E₂ x * x ^ (-s) := by
    simp_rw [sum_div_log_eq', add_mul, ← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun (by measurability) (by intro; grind)
  _ = _ := by
    have h1 := integrableOn_log_log_mul_rpow hs
    have h2 (C : ℝ) : IntegrableOn (C * · ^ (-s)) (.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul C
    have : IntegrableOn (fun x ↦ f.E₂ x * x ^ (-s)) (.Ioi 1) := by
      refine Integrable.mono'
        (g := fun x ↦ |log (log x) * x ^ (-s)| + (|f.M| + f.C₂ / log 2) * x ^ (-s))
        (h1.abs.add (h2 _)) (aestronglyMeasurable (by unfold E₂; fun_prop))
        (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx ↦ ?_)
      have : 0 < x := by grind
      have : 0 ≤ x ^ (-s) := by positivity
      grw [norm_mul, abs_mul, norm_eq_abs, norm_eq_abs, abs_of_nonneg this, f.E₂_bound_weak]
      <;> grind
    rw [MeasureTheory.integral_add, MeasureTheory.integral_add, mul_add, mul_add,
        eulerMascheroniConstant_eq_neg_integral_log_log hs, MeasureTheory.integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
    · nth_rw 4 [← integral_comp_rpow_Ioi_of_pos' (by linarith : 0 < s - 1) zero_le_one]
      simp only [Real.one_rpow, sub_add_cancel_left, neg_neg, smul_eq_mul]
      congr
      · grind
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun (by measurability) (fun x hx ↦ ?_)
      have : 0 < x := by grind
      rw [← rpow_mul this.le, ← rpow_mul this.le, mul_inv_cancel₀ (by linarith), Real.rpow_one]
      trans (s - 1) * (f.E₂ x * (x ^ (s - 1 - 1) * x ^ ((s - 1) * -2)))
      · rw [← rpow_add this]; ring_nf
      · ring
    exacts [h1, h2 f.M, h1.add (h2 f.M), ‹_›]

/-- An asymptotic for the Dirichlet series associated to Mertens' second theorem. -/
theorem sum_div_log_mul_pow_add_tendsto :
    Tendsto (fun s ↦ ∑' n : ℕ, (log n)⁻¹ * f n * n ^ (1 - s) + log (s - 1)) (𝓝[>] 1)
    (𝓝 (f.M - eulerMascheroniConstant)) := by
  have := f.C₂_nonneg
  suffices Tendsto (fun (s : ℝ) ↦ ∫ x in .Ioi 1, (f.E₂ (x ^ (s - 1)⁻¹)) * x ^ (-2 : ℝ)) (𝓝[>] 1)
      (𝓝 0) by
    rw [← tendsto_sub_nhds_zero_iff]
    apply this.congr'
    filter_upwards [eventually_mem_nhdsWithin]
    grind [sum_div_log_mul_pow_eq]
  apply squeeze_zero_norm (fun _ ↦ norm_integral_le_lintegral_norm _)
    ((tendsto_toReal zero_ne_top).comp _)
  convert tendsto_lintegral_filter_of_dominated_convergence (l := 𝓝[>] (1 : ℝ)) (f := 0)
    (fun x ↦ ENNReal.ofReal ((|log (log x)| + |f.M| + f.C₂ / log 2) * x ^ (-2 : ℝ)))
    ?_ ?_ ?_ ?_
  · simp
  · unfold E₂; filter_upwards; fun_prop
  · filter_upwards [eventually_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds] with s hs hs'
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    gcongr
    rw [Set.mem_Ioi] at hs hx
    have : 0 < s - 1 := by linarith
    grw [norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ x ^ (-2 : ℝ))]
    gcongr
    rcases le_or_gt 2 (x ^ (s - 1)⁻¹) with h | h
    · grw [f.E₂_bound h, ← h, le_add_iff_nonneg_left]
      positivity
    · have : x ≤ x ^ (s - 1)⁻¹ := self_le_rpow_of_one_le hx.le (by field_simp; linarith)
      have : 1 ≤ x ^ (s - 1)⁻¹ := by linarith
      grw [f.E₂_bound_weak this]
      gcongr 2
      grw [← neg_le_abs, abs_of_nonpos, neg_le_neg_iff]
      · exact log_le_log (log_pos hx) (log_le_log (by linarith) ‹_›)
      apply log_nonpos (log_nonneg this)
      grw [h, log_two_lt_d9]
      norm_num
  · rw [lintegral_ofReal_ne_top_iff_integrable (aestronglyMeasurable (by fun_prop))
        (Eventually.of_forall fun _ ↦ by simp only [Pi.zero_apply, rpow_neg_ofNat]; positivity)]
    simp_rw [add_assoc, add_mul _ (|f.M| + f.C₂ / log 2)]
    apply Integrable.add
    exacts [IntegrableOn.congr_fun (integrableOn_log_log_mul_rpow (by norm_num : 1 < (2 : ℝ))).abs
      (fun _ _ ↦ by simp [zpow_ofNat]) measurableSet_Ioi,
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul _]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    suffices Tendsto (fun s : ℝ ↦ f.E₂ (x ^ (s - 1)⁻¹) * x ^ (-2 : ℝ)) (𝓝[>] 1)
        (𝓝 (0 * x ^ (-2 : ℝ))) by simpa using ENNReal.tendsto_ofReal this.norm
    have h : Tendsto f.E₂ atTop (𝓝 0) := by
      apply squeeze_zero_norm' (a := (f.C₂ / log ·)) _ (tendsto_log_atTop.const_div_atTop _)
      filter_upwards [eventually_ge_atTop 2] with x hx
      simpa using f.E₂_bound hx
    have : Tendsto (· - (1 : ℝ)) (𝓝[>] 1) (𝓝[>] 0) := by convert tendsto_map; simp
    exact (h.comp ((tendsto_rpow_atTop_of_base_gt_one _ hx).comp
           (tendsto_inv_nhdsGT_zero.comp this))).mul_const _

end Weight

end Mertens
