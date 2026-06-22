/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Pietro Monticone, Terence Tao, Yi Yuan
-/
module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Log.InvLog
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.NumberTheory.Chebyshev

/-!
# Mertens theorems

This file establishes the Mertens theorems that estimate sums and products involving primes
or the von Mangoldt function.

## Main definitions

- `E₁Λ`: The error `∑ d ∈ Ioc 0 ⌊x⌋₊, (Λ d) / d - log x` in the von Mangoldt form
of Mertens' first theorem.
- `E₁p`: The error `∑ p ∈ primesLE ⌊x⌋₊, (log p) / p - log x` in the prime form of Mertens' first
theorem.

## Main results

- Mertens' first theorem: `|E₁Λ x|` and `|E₁p x|` are both bounded (by `log 4 + 1` and `3`
respectively).  For natural numbers `N`, we obtain the improvement `|E₁p x| ≤ 2`.
- Abstract conversion from first theorem to second theorem

## TODO

Add Mertens' second and third theorems.

## References

Parts of this file were upstreamed from the PrimeNumberTheoremAnd project by Kontorovich et al,
https://github.com/alexKontorovich/PrimeNumberTheoremAnd.

-/

@[expose] public section

namespace Mertens

open Nat hiding log
open Finset Filter Real Chebyshev intervalIntegral Asymptotics MeasureTheory
open ArithmeticFunction hiding log
open scoped Nat.Prime

/-!
## Bounds on the partial sum of the logarithm

The partial sum of the logarithm can also be expressed as the logarithm of the factorial, as well
as a sum involving the von Mangoldt function.  Here we state these identities and also provide
some upper and lower bounds on the partial sum of `log n`.

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
      exact ae_restrict_of_forall_mem (by measurability) (fun _ _ ↦ (Real.log_pos (by grind)).le)
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

section FirstTheorem

/-!
## Mertens' first theorem

Mertens' first theorem can be formulated in terms of two error terms:

* `E₁Λ x = ∑ d ∈ Ioc 0 ⌊x⌋₊, (Λ d) / d - log x` (von Mangoldt error).  We bound this
error between `-2` and `log 4 + 1`, or between `-1` and `log 4 + 1` in the natural number case.
* `E₁p x = ∑ p ∈ primesLE ⌊x⌋₊, (log p) / p - log x` (prime error). We bound this error
between `-3` and `log 4`, or between `-2` and `log 4` in the natural number case.

The difference `E₁Λ x - E₁p x` ranges between `0` and a certain constant `E₁ = 0.755366...`.
We bound this constant betweeen `0` and `1`.

-/

variable (x : ℝ) (N : ℕ)

/-- The error term in the von Mangoldt form of Mertens' first theorem. -/
noncomputable def E₁Λ : ℝ := ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d - log x

/-- The error term in the prime form of Mertens' first theorem. -/
noncomputable def E₁p : ℝ := ∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x

theorem sum_mangoldt_div_eq : ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d = log x + E₁Λ x := by simp [E₁Λ]

theorem sum_mangoldt_div_eq_nat : ∑ d ∈ Ioc 0 N, Λ d / d = log N + E₁Λ N := by
  simpa using sum_mangoldt_div_eq (x := N)

theorem sum_log_prime_div_eq : ∑ p ∈ primesLE ⌊x⌋₊, log p / p = log x + E₁p x := by simp [E₁p]

theorem sum_log_prime_div_eq_nat : ∑ p ∈ primesLE N, log p / p = log N + E₁p N := by
  simpa using sum_log_prime_div_eq (x := N)

theorem E₁p_le_E₁Λ : E₁p x ≤ E₁Λ x := by
  unfold E₁p E₁Λ; rw [primesLE_eq_filter_Ioc_zero, sum_filter]
  gcongr with p _
  split_ifs with hp
  · simp [vonMangoldt_apply_prime hp]
  have : 0 ≤ Λ p := vonMangoldt_nonneg
  positivity

/-- One can lower bound `E₁Λ x` using a partial sum of logarithms. -/
theorem le_mul_log_add_E₁Λ {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * (log x + E₁Λ x) := calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by rw [←sum_mangoldt_div_eq, mul_sum]; ring_nf
  _ ≥ _ := by
    rw [sum_log_eq_sum_mangoldt]
    gcongr; exacts [vonMangoldt_nonneg, floor_le <| div_nonneg (by linarith) (by linarith)]

/-- One can upper bound `E₁Λ x` using a partial sum of logarithms. -/
theorem mul_log_add_E₁Λ_le (x : ℝ) :
    x * (log x + E₁Λ x) ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n + ψ x := calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by rw [←sum_mangoldt_div_eq, mul_sum]; ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr; exacts [vonMangoldt_nonneg, lt_floor_add_one _|>.le]
  _ = _ := by simp [psi, mul_add, sum_add_distrib, sum_log_eq_sum_mangoldt]

/-- One can lower bound `E₁p x` using a partial sum of logarithms. -/
theorem mul_log_add_E₁p_le (x : ℝ) : x * (log x + E₁p x) ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n + θ x := calc
  _ = ∑ p ∈ primesLE ⌊x⌋₊, log p * (x / p) := by
    rw [←sum_log_prime_div_eq, mul_sum]; ring_nf
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

/-- The summand defining the constant `E₁` below. -/
noncomputable def e₁ : ℕ → ℝ := fun p ↦ if p.Prime then log p / (p * (p - 1)) else 0

/-- The constant `E₁ = 0.755366...` (https://oeis.org/A138312) is defined as the sum of
`log p / (p * (p-1))` over primes `p`. -/
noncomputable def E₁ : ℝ := ∑' p : ℕ, e₁ p

lemma e₁_nonneg (p : ℕ) : 0 ≤ e₁ p := by
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
    · grind [Set.uIcc_of_le]
    apply ((ContinuousOn.log (f := (2 * · + 3)) (by fun_prop) (by grind [Set.uIcc_of_le])).div₀
        (by fun_prop) _).intervalIntegrable
    rw [Set.uIcc_of_le hN]; simp; grind
  linarith [log_two_lt_d9, log_three_lt_d9]

theorem E₁_nonneg : 0 ≤ E₁ := tsum_nonneg e₁_nonneg

theorem E₁Λ_le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) : E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ primesLE ⌊x⌋₊, log p / p + E₁ by linarith
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
    _ ≤ ∑ p ∈ primesLE ⌊x⌋₊, log p / (p * (p - 1)) := by
      rw [sum_comm]
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
    _ ≤ _ := by
      rw [primesLE_eq_filter_Ioc_zero, sum_filter]
      exact e₁_summable.sum_le_tsum _ fun p _ ↦ e₁_nonneg p

/-- A general upper bound for `E₁p`. -/
theorem E₁p_le {x : ℝ} (hx : 1 ≤ x) : E₁p x ≤ log 4 := by
  suffices x * (log x + E₁p x) ≤ x * (log x + log 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  grw [mul_log_add_E₁p_le x, theta_le_log4_mul_x (by linarith), sum_log_le' hx]
  ring_nf; rfl

/-- A general upper bound for `E₁Λ`. -/
theorem E₁Λ_le {x : ℝ} (hx : 1 ≤ x) : E₁Λ x ≤ log 4 + 1 := by
  linarith [E₁p_le hx, E₁Λ_le_E₁p_add_E₁ hx, E₁_le]

/-- A general lower bound for `E₁Λ`. -/
theorem le_E₁Λ {x : ℝ} (hx : 1 ≤ x) : -2 ≤ E₁Λ x := by
  suffices x * (log x - 2) ≤ x * (log x + E₁Λ x) by
     linarith [le_of_mul_le_mul_left this (by linarith)]
  grw [← le_mul_log_add_E₁Λ (by linarith), ← le_sum_log' hx]
  linarith [log_le_self (by linarith : 0 ≤ x)]

/-- A sharper lower bound for `E₁Λ` in the natural number case. -/
theorem le_E₁Λ_nat (N : ℕ) : -1 ≤ E₁Λ N := by
  by_cases! hN : N = 0
  · simp [hN, E₁Λ]
  suffices N * (log N - 1) ≤ N * (log N + E₁Λ N) by
    linarith [le_of_mul_le_mul_left this (by norm_cast; lia)]
  grw [← le_mul_log_add_E₁Λ (by linarith), floor_natCast, ←le_sum_log_nat]
  ring_nf; rfl

/-- A general lower bound for `E₁p`. -/
theorem le_E₁p {x : ℝ} (hx : 1 ≤ x) : -3 ≤ E₁p x := by
  linarith [E₁Λ_le_E₁p_add_E₁ hx, le_E₁Λ hx, E₁_le]

/-- A sharper lower bound for `E₁p` in the natural number case. -/
theorem le_E₁p_nat (N : ℕ) : -2 ≤ E₁p N := by
  by_cases! hN : N = 0
  · simp [hN, E₁p]
  have : 1 ≤ (N:ℝ) := mod_cast (by lia)
  linarith [E₁Λ_le_E₁p_add_E₁ this, le_E₁Λ_nat N, E₁_le]

theorem sum_mangoldt_div_sub_log_bound {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d - log x| ≤ log 4 + 1 := by
  rw [abs_le, sum_mangoldt_div_eq]
  split_ands <;> linarith [E₁Λ_le hx, le_E₁Λ hx, log_four_eq, log_two_gt_d9]

theorem E₁Λ_bounded : E₁Λ =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one, eventually_atTop]
  exact ⟨log 4 + 1, 1, fun _ ↦ sum_mangoldt_div_sub_log_bound⟩

theorem sum_mangoldt_div_sim_log :
    (∑ d ∈ Ioc 0 ⌊·⌋₊, Λ d / d) ~[atTop] log :=
  (E₁Λ_bounded.trans_isLittleO (isLittleO_const_log_atTop)).isEquivalent

theorem sum_log_prime_div_sub_log_bound {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x| ≤ 3 := by
  simp only [sum_log_prime_div_eq, add_sub_cancel_left, abs_le']
  and_intros <;>
    linarith [le_E₁p hx, E₁_le, E₁p_le hx, sum_log_prime_div_eq, log_four_eq, log_two_lt_d9]

theorem sum_log_prime_div_sub_log_bound_nat (N : ℕ) :
    |∑ p ∈ primesLE N, log p / p - log N| ≤ 2 := by
  by_cases! hN : N = 0
  · simp [hN]
  have hx : 1 ≤ (N : ℝ) := mod_cast (by lia)
  simp only [sum_log_prime_div_eq_nat, add_sub_cancel_left]
  rw [abs_le']; and_intros <;>
    linarith [le_E₁p_nat N, E₁_le, E₁p_le hx, sum_log_prime_div_eq, log_four_eq, log_two_lt_d9]

theorem E₁p_bounded : E₁p =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one, eventually_atTop]
  exact ⟨3, 1, fun _ ↦ sum_log_prime_div_sub_log_bound⟩

theorem sum_log_prime_div_sim_log : (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, log p / p)
    ~[atTop] log := by
  apply (IsBigO.trans_isLittleO _ (isLittleO_const_log_atTop (c := 1))).isEquivalent
  convert! E₁p_bounded using 1

end FirstTheorem

section AbstractSecondTheorem

/-!
## An abstract version of Mertens' second theorem

We give API for converting abstract bounds on first Mertens theorem type errors to bounds
on second Mertens type errors, as well as an associated Meissel--Mertens constant, all associated
to a suitable weight function `f : ℕ → ℝ` that obeys a Mertens first theorem type bound
`∑ n ∈ Ioc 0 ⌊x⌋₊, f n = log x + O(1)`.

-/
open intervalIntegral

variable (f : ℕ → ℝ) (x : ℝ) {C_lo C_hi : ℝ}

/-- The first Mertens error for a function `f : ℕ → ℝ` is defined as
`E₁f f x = ∑ n ∈ Ioc 0 ⌊x⌋₊, f n - log x`. -/
noncomputable def E₁f := ∑ n ∈ Icc 0 ⌊x⌋₊, f n - log x

/- Move? -/
attribute [fun_prop] measurable_from_top

lemma sum_f_eq : ∑ n ∈ Icc 0 ⌊x⌋₊, f n = log x + E₁f f x := by grind [E₁f]

/-- The Meissel--Mertens constant associated to a function `f : ℕ → ℝ` is defined as
`Mf f = (∫ t in .Ioi 2, (t * log t^2)⁻¹ * E₁f f t) + 1 - log (log 2)`.
-/
noncomputable def Mf := (∫ t in .Ioi 2, (t * log t^2)⁻¹ * E₁f f t) + 1 - log (log 2)

/-- The second Mertens error for a function `f : ℕ → ℝ` is defined as
`E₂f f x = ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - Mf f`. -/
noncomputable def E₂f := ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - Mf f

lemma sum_f_div_log_eq : ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * f n = log (log x) + Mf f + E₂f f x := by
  grind [E₂f]

private noncomputable def inv : ℝ → ℝ := (·⁻¹)
private noncomputable def inv_log : ℝ → ℝ := inv ∘ log
private noncomputable def log_log : ℝ → ℝ := fun x ↦ log (log x)

private lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv log_log x = (inv * inv_log^2 * log) x := by
  unfold log_log
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  simp [inv, inv_log, field]

@[fun_prop]
private lemma ContinuousOn.log_Ioi_one : ContinuousOn log (.Ioi 1) :=
  continuousOn_log.mono (by grind)

@[fun_prop]
private lemma ContinuousOn.log_inv_Ioi_one : ContinuousOn inv_log (.Ioi 1) :=
  log_Ioi_one.inv₀ (by simp; grind)

@[fun_prop]
private lemma ContinuousOn.inv_Ioi_one : ContinuousOn inv (.Ioi 1) :=
  continuousOn_inv₀.mono (by grind)

@[fun_prop]
private lemma DifferentiableOn.log_log : DifferentiableOn ℝ log_log (.Ioi 1) :=
  (differentiableOn_log.mono (by grind)).log (by simp; grind)

/-- Remove after #40872 lands -/
@[fun_prop]
theorem ContinuousOn.const_smul' {M : Type*} {α : Type*} {β : Type*} [TopologicalSpace α]
    [SMul M α] [ContinuousConstSMul M α] [TopologicalSpace β] {g : β → α} {s : Set β}
    (hg : ContinuousOn g s) (c : M) : ContinuousOn (c • g) s := hg.const_smul c

/-- Remove after #40872 lands -/
@[to_additive (attr := fun_prop)]
theorem ContinuousOn.inv' {G : Type*} {X : Type*} [TopologicalSpace X] [TopologicalSpace G] [Inv G]
[ContinuousInv G] {f : X → G} {s : Set X}
    (hf : ContinuousOn f s) : ContinuousOn f⁻¹ s := hf.inv

/-- Remove after #40872 lands -/
@[fun_prop]
theorem ContinuousOn.pow' {M : Type*} {X : Type*} [TopologicalSpace X] [TopologicalSpace M]
    [Monoid M] [ContinuousMul M] {f : X → M} {s : Set X} (hf : ContinuousOn f s) (n : ℕ) :
    ContinuousOn (f^n) s := hf.pow n

private lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    (∫ (t : ℝ) in 2..x, (t * log t ^ 2)⁻¹ * log t) = log (log x) - log (log 2) := by
  suffices ∫ (t : ℝ) in 2..x, (inv * inv_log ^ 2 * log) t = log_log x - log_log 2 by
    unfold inv_log inv log_log at this; convert this; simp [field]
  rw [← integral_deriv_eq_sub (f := log_log)]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [deriv_log_log (by linarith)]
  · intro t ht
    exact DifferentiableOn.log_log.differentiableAt (Ioi_mem_nhds (by grind [Set.uIcc_of_le]))
  · refine (ContinuousOn.congr (f := inv * inv_log^2 * log) ?_ ?_).intervalIntegrable
    · apply ContinuousOn.mono (s := .Ioi 1) _ (by grind [Set.uIcc_of_le])
      exact (by fun_prop : ContinuousOn (inv * inv_log^2 * log) (.Ioi 1))
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    IntegrableOn (c • (inv * inv_log^2)) (.Ioi x) volume := by
  apply Integrable.const_mul
  refine integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by fun_prop (disch := grind)
    convert! this.hasDerivAt using 1
    simp [deriv_inv_log, inv, inv_log, field]
  · intro t ht
    have : 0 < t := by grind
    simp only [Pi.mul_apply, inv, Pi.pow_apply]; positivity

private theorem E₁f_bound {f : ℕ → ℝ}
    (h_lo : ∀ t ≥ 1, C_lo ≤ E₁f f t) (h_hi : ∀ t ≥ 1, E₁f f t ≤ C_hi) :
    ∀ t ≥ 1, |E₁f f t| ≤ max (-C_lo) C_hi := by
  intro t ht; grw [abs_le, ←h_lo t ht, h_hi t ht]; grind

theorem E₁f_div_integrable {f : ℕ → ℝ} {x : ℝ} (hx : 2 ≤ x)
    (h_lo : ∀ t ≥ 1, C_lo ≤ E₁f f t) (h_hi : ∀ t ≥ 1, E₁f f t ≤ C_hi) :
    IntegrableOn (fun t ↦ (t * log t^2)⁻¹ * E₁f f t) (.Ioi x) volume := by
  have hbound := E₁f_bound h_lo h_hi
  set C := max (-C_lo) C_hi
  apply Integrable.mono (integrable_const_div_mul_log_sq C hx)
  · exact Measurable.aestronglyMeasurable (by unfold E₁f; fun_prop)
  filter_upwards [ae_restrict_mem (by measurability)] with t ht
  simp only [Set.mem_Ioi, mul_inv_rev, norm_mul, norm_inv, norm_pow, norm_eq_abs, sq_abs, inv_log,
    Pi.smul_apply, Pi.mul_apply, inv, Pi.pow_apply, Function.comp_apply, inv_pow,
    smul_eq_mul] at ht ⊢
  have : 0 < log t := log_pos (by linarith)
  grw [hbound t (by linarith), le_abs_self C]
  simp [field]

theorem E₂f_eq {x : ℝ} (hx : 2 ≤ x)
    (h_lo : ∀ t ≥ 1, C_lo ≤ E₁f f t) (h_hi : ∀ t ≥ 1, E₁f f t ≤ C_hi)
    (h0 : f 0 = 0) (h1 : f 1 = 0) :
    E₂f f x = (log x)⁻¹ * E₁f f x - ∫ t in .Ioi x, (t * log t^2)⁻¹ * E₁f f t := by
  have hbound := E₁f_bound h_lo h_hi
  set C := max (-C_lo) C_hi
  have : 0 < log x := log_pos (by linarith)
  suffices ∫ t in 2..x, (t * log t^2)⁻¹ * E₁f f t = ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * f n -
    (log x)⁻¹ * (∑ n ∈ Icc 0 ⌊x⌋₊, f n) - log (log x) + log (log 2) by
    have : (∫ t in 2..x, (t * log t^2)⁻¹ * E₁f f t) + ∫ t in .Ioi x, (t * log t ^ 2)⁻¹ * E₁f f t
      = ∫ t in .Ioi 2, (t * log t^2)⁻¹ * E₁f f t := integral_interval_add_Ioi
        (E₁f_div_integrable (by rfl) h_lo h_hi) (E₁f_div_integrable hx h_lo h_hi)
    have : (log x)⁻¹ * E₁f f x = (log x)⁻¹ * (∑ n ∈ Icc 0 ⌊x⌋₊, f n) - 1 := by
      unfold E₁f; field_simp
    unfold E₂f Mf; linarith
  have : ∫ (t : ℝ) in 2..x, (t * log t ^ 2)⁻¹ * ∑ n ∈ Icc 0 ⌊t⌋₊, f n =
      (∫ (t : ℝ) in 2..x, (t * log t ^ 2)⁻¹ * log t)
      + ∫ (t : ℝ) in 2..x, (t * log t ^ 2)⁻¹ * (E₁f f t) := by
    simp only [mul_inv_rev, sum_f_eq, mul_add]
    apply intervalIntegral.integral_add
    <;> rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    · apply (ContinuousOn.integrableOn_Icc _).mono_set Set.Ioc_subset_Icc_self
      apply ContinuousOn.mono (s := .Ioi 1) _ (by grind)
      convert (by fun_prop : ContinuousOn (inv * inv_log^2 * log) (.Ioi 1)) using 2
      simp [inv, inv_log, field]
    apply Integrable.mono (g := fun t ↦ (log 2 ^ 2)⁻¹ * t⁻¹ * C)
    · apply (ContinuousOn.integrableOn_Icc _).mono_set Set.Ioc_subset_Icc_self
      apply ContinuousOn.mono (s := .Ioi 1) _ (by grind)
      convert (by fun_prop : ContinuousOn (((log 2 ^ 2)⁻¹ * C) • inv) (.Ioi (1:ℝ))) using 2
      simp [inv, field]
    · exact Measurable.aestronglyMeasurable (by unfold E₁f; fun_prop)
    filter_upwards [ae_restrict_mem (by measurability)] with t ht
    simp [Set.mem_Ioc] at ht
    simp only [norm_mul, norm_inv, norm_pow, norm_eq_abs, sq_abs]
    grw [hbound t (by linarith), le_abs_self C]; gcongr; order
  rw [integral_one_div_mul_log hx] at this
  rw [sum_mul_eq_sub_integral_mul₁ _ h0 h1 x (f := fun t ↦ (log t)⁻¹)]
  · suffices ∫ t in .Ioc 2 x, deriv (fun t ↦ (log t)⁻¹) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k =
        - ∫ t in 2..x, (t * log t ^ 2)⁻¹ * ∑ n ∈ Icc 0 ⌊t⌋₊, f n by linarith
    rw [← intervalIntegral.integral_neg, intervalIntegral.integral_of_le hx]
    apply setIntegral_congr_fun (by measurability)
    intro t ht
    simp [field]
  · intro t ht
    simp at ht
    exact DifferentiableAt.fun_inv (by simp; linarith) (by simp; grind)
  · apply (ContinuousOn.mono (s := .Ioi 1) _ (by grind)).integrableOn_Icc
    rw [deriv_inv_log']
    convert (by fun_prop : ContinuousOn (-inv * inv_log^2) (.Ioi (1:ℝ))) using 2
    simp [inv, inv_log, field]

private theorem integ_div_mul_log_sq {x : ℝ} (C : ℝ) (hx : 2 ≤ x) :
    ∫ (t : ℝ) in .Ioi x, (t * log t ^ 2)⁻¹ * C = C / log x := by
    convert! integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := (- C / log ·)) ?_
      (integrable_const_div_mul_log_sq C hx) ?_ using 1
    · simp [inv, inv_log]; grind
    · field
    · intro t ht; simp at ht
      convert! (hasDerivAt_const _ (-C)).fun_div (hasDerivAt_log (by linarith)) ?_ using 1
      · simp [inv, inv_log]; grind
      simp; grind
    convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-C) using 1
    simp

private lemma inv_mul_sq_nonneg {x t : ℝ} (ht : t ∈ Set.Ioi x) (hx : 1 < x)
    : 0 ≤ (t * log t ^ 2)⁻¹ := by
  simp at ht
  have : 0 < t := by linarith
  have : 0 < log t := log_pos (by linarith)
  positivity

theorem E₂f_abs_le {x : ℝ} (hx : 2 ≤ x) (h_lo : ∀ t ≥ 1, C_lo ≤ E₁f f t)
 (h_hi : ∀ t ≥ 1, E₁f f t ≤ C_hi) (h0 : f 0 = 0) (h1 : f 1 = 0) :
    |E₂f f x| ≤ (C_hi - C_lo) / log x := by
  have : 0 < log x := log_pos (by linarith)
  have := E₁f_div_integrable hx h_lo h_hi
  have hinteg (C : ℝ) : IntegrableOn (fun t ↦ (t * log t ^ 2)⁻¹ * C) (.Ioi x) volume := by
    convert integrable_const_div_mul_log_sq C hx using 2 with x; simp [inv_log, inv]; grind
  have : NullMeasurableSet (.Ioi x) volume := by measurability
  rw [E₂f_eq f hx h_lo h_hi h0 h1, abs_le]
  constructor
  · calc
      _ ≥ (log x)⁻¹ * C_lo - ∫ t in .Ioi x, (t * log t ^ 2)⁻¹ * C_hi := by
        gcongr with t ht
        exacts [h_lo _ (by linarith), hinteg C_hi,
          inv_mul_sq_nonneg ht (by linarith), h_hi _ (by grind)]
      _ = _ := by rw [integ_div_mul_log_sq C_hi hx]; simp [field]
  · calc
      _ ≤ (log x)⁻¹ * C_hi - ∫ t in .Ioi x, (t * log t ^ 2)⁻¹ * C_lo := by
        gcongr with t ht
        exacts [h_hi _ (by linarith), hinteg C_lo,
          inv_mul_sq_nonneg ht (by linarith), h_lo _ (by grind)]
      _ = _ := by rw [integ_div_mul_log_sq C_lo hx]; simp [field]

theorem γf_bounds (h_lo : ∀ t ≥ 1, C_lo ≤ E₁f f t) (h_hi : ∀ t ≥ 1, E₁f f t ≤ C_hi) :
    Mf f ≤ C_hi / (log 2) + 1 - log (log 2) ∧ C_lo / (log 2) + 1 - log (log 2) ≤ Mf f := by
  have hbound : ∀ t ≥ 1, |E₁f f t| ≤ max (-C_lo) C_hi := by
    intro t ht; grw [abs_le, ←h_lo t ht, h_hi t ht]; grind
  unfold Mf
  rw [← integ_div_mul_log_sq C_hi (by rfl), ← integ_div_mul_log_sq C_lo (by rfl)]
  have := E₁f_div_integrable (by rfl) h_lo h_hi
  have hinteg (C : ℝ) : IntegrableOn (fun t ↦ (t * log t ^ 2)⁻¹ * C) (.Ioi 2) volume := by
    convert integrable_const_div_mul_log_sq C (by rfl) using 2 with x; simp [inv_log, inv]; grind
  have : NullMeasurableSet (.Ioi (2 : ℝ)) volume := by measurability
  constructor <;> gcongr with t ht
  exacts [hinteg C_hi, inv_mul_sq_nonneg ht (by norm_num), h_hi _ (by grind),
          hinteg C_lo, inv_mul_sq_nonneg ht (by norm_num), h_lo _ (by grind)]

end AbstractSecondTheorem

end Mertens
