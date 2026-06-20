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
theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x := calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (mod_cast hn.1) (le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    exacts [log_nonneg hx, floor_le (by linarith)]

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
      intervalIntegral.intervalIntegrable_const
    intro _ _; rify at this; gcongr <;> grind
  _ ≥ _ := by
    have : 0 ≤ log x := log_nonneg hx
    have : x - ⌊x⌋₊ ≤ 1 := by linarith [lt_floor_add_one x]
    grw [integral_log, log_one, intervalIntegral.integral_const, smul_eq_mul, this]
    linarith

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
    have denom : (p : ℝ) * ((p : ℝ) - 1) ≥ p ^ 2 / 2 := by nlinarith
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
    simp [e₁, Nat.prime_two, Nat.prime_three, (by decide : ¬ Nat.Prime 4)]
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

theorem E₁Λ_le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
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
  grw [mul_log_add_E₁p_le x, theta_le_log4_mul_x (by linarith), sum_log_le hx]
  ring_nf; rfl

/-- A general upper bound for `E₁Λ`. -/
theorem E₁Λ_le {x : ℝ} (hx : 1 ≤ x) : E₁Λ x ≤ log 4 + 1 := by
  linarith [E₁p_le hx, E₁Λ_le_E₁p_add_E₁ hx, E₁_le]

/-- A general lower bound for `E₁Λ`. -/
theorem le_E₁Λ {x : ℝ} (hx : 1 ≤ x) : -2 ≤ E₁Λ x := by
  suffices x * (log x - 2) ≤ x * (log x + E₁Λ x) by
     linarith [le_of_mul_le_mul_left this (by linarith)]
  grw [← le_mul_log_add_E₁Λ (by linarith), ← le_sum_log hx]
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

end Mertens
