/-
Copyright (c) 2026 Yan Senez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Senez
-/
module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Mertens' First Theorem

The present file establishes **Mertens' First Theorem** (1874):
$$\sum_{p \le x} \frac{\log p}{p} \;=\; \log x \,+\, O(1) \qquad (x \to \infty).$$

The argument we follow is, in essence, that of Mertens himself: it proceeds
through Chebyshev's function `θ(x) := ∑_{p \le x} \log p` (available in
`Mathlib.NumberTheory.Chebyshev`) and Abel summation
(`Mathlib.NumberTheory.AbelSummation`), by means of Legendre's classical identity
`log(N!) = ∑_d Λ(d) ⌊N/d⌋` together with the effective Stirling expansion of
`log(N!)`.

## Main definitions

* `Mertens.partialSum x` — the partial sum `∑_{p ≤ x} 1/p` over primes.
* `Mertens.partialSumLog x` — auxiliary partial sum `∑_{p ≤ x} (log p) / p`.

## Main theorem

* `Mertens.first` — Mertens' First Theorem:
  `∃ C, ∀ x ≥ 2, |partialSumLog x - log x| ≤ C`.

## References

* F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. Reine Angew. Math.
  78 (1874), 46–62.
* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*,
  6th ed., Oxford University Press (2008), Theorem 425.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*,
  3rd ed., Graduate Studies in Mathematics 163 (2015), §I.1.4.
-/
@[expose] public section

namespace Mertens

open Real Nat Finset
open scoped BigOperators


/-! ### Partial sums -/

/-- **`partialSum x`**: the partial sum `∑_{p ≤ x, prime} 1/p`, indexed by the
    natural-number cutoff `⌊x⌋₊`. We rely on `Nat.primesBelow` (the primes strictly
    less than `n`) applied to `n = ⌊x⌋₊ + 1`, which is precisely the set of primes
    `≤ ⌊x⌋₊`.

    For `x < 0` one has `⌊x⌋₊ = 0`, so the sum is empty; for `x ∈ [0, 2)` it
    remains empty, since there are no primes `≤ 1`. -/
noncomputable def partialSum (x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 : ℝ) / p

/-- **`partialSumLog x`**: the auxiliary partial sum `∑_{p ≤ x, prime} (log p)/p`,
    which appears in Mertens' First Theorem (`first` below). -/
noncomputable def partialSumLog (x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), Real.log p / p

/-! ### Trivial boundary cases (no `sorry`) -/

/-- For `x < 2`, the natural-number floor `⌊x⌋₊` is at most `1`. -/
private lemma floor_le_one_of_lt_two {x : ℝ} (hx : x < 2) : ⌊x⌋₊ ≤ 1 := by
  by_cases hx0 : 0 ≤ x
  · -- 0 ≤ x < 2 ⇒ ⌊x⌋₊ < 2 (via Nat.floor_lt) ⇒ ⌊x⌋₊ ≤ 1
    have : ⌊x⌋₊ < 2 := by
      rw [Nat.floor_lt hx0]
      exact_mod_cast hx
    omega
  · -- x < 0 ⇒ ⌊x⌋₊ = 0
    have hx0' : x < 0 := lt_of_not_ge hx0
    have : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    omega

/-- `primesBelow n = ∅` whenever `n ≤ 2`. -/
private lemma primesBelow_eq_empty_of_le_two {n : ℕ} (hn : n ≤ 2) :
    Nat.primesBelow n = ∅ := by
  rw [Nat.primesBelow_eq_filter_range]
  apply Finset.filter_eq_empty_iff.mpr
  intro p hp
  have hpr : p < n := Finset.mem_range.mp hp
  have hp2 : p < 2 := lt_of_lt_of_le hpr hn
  intro hprime
  exact absurd (hprime.two_le) (by omega)

/-- The Mertens sum vanishes on the empty range `x < 2`: indeed, there are no
    primes `≤ x` for such `x`. -/
theorem partialSum_lt_two {x : ℝ} (hx : x < 2) : partialSum x = 0 := by
  unfold partialSum
  have hx_floor : ⌊x⌋₊ ≤ 1 := floor_le_one_of_lt_two hx
  rw [primesBelow_eq_empty_of_le_two (by omega : ⌊x⌋₊ + 1 ≤ 2), Finset.sum_empty]

/-- Likewise, the log-weighted sum vanishes for `x < 2`. -/
theorem partialSumLog_lt_two {x : ℝ} (hx : x < 2) : partialSumLog x = 0 := by
  unfold partialSumLog
  have hx_floor : ⌊x⌋₊ ≤ 1 := floor_le_one_of_lt_two hx
  rw [primesBelow_eq_empty_of_le_two (by omega : ⌊x⌋₊ + 1 ≤ 2), Finset.sum_empty]

/-- `partialSum` is non-negative for every `x`: each summand `1/p` is non-negative
    whenever `p` is a positive prime, and the sum is trivially `0` below `x = 2`. -/
theorem partialSum_nonneg (x : ℝ) : 0 ≤ partialSum x := by
  unfold partialSum
  apply Finset.sum_nonneg
  intro p hp
  have hp_pos : 0 < p := by
    rw [Nat.primesBelow_eq_filter_range, Finset.mem_filter] at hp
    exact hp.2.pos
  positivity

/-- `partialSumLog` is non-negative for every `x`: each summand `log p / p ≥ 0`,
    since primes are `≥ 2` and hence `log p ≥ log 2 > 0`. -/
theorem partialSumLog_nonneg (x : ℝ) : 0 ≤ partialSumLog x := by
  unfold partialSumLog
  apply Finset.sum_nonneg
  intro p hp
  have hp_prime : Nat.Prime p := by
    rw [Nat.primesBelow_eq_filter_range, Finset.mem_filter] at hp
    exact hp.2
  have hp_ge_two : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
  have hp_pos : (0 : ℝ) < p := by linarith
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  positivity

/-! ### Building blocks toward M1: Legendre's log-factorial identity

The classical Mertens 1874 proof of M1 (which predates the Prime Number Theorem)
rests on combining Stirling's approximation `log n! = n log n − n + O(log n)`
with the **Legendre summatory identity**

$$\log N! \;=\; \sum_{d=1}^{N} \Lambda(d) \,\lfloor N/d\rfloor,$$

which is nothing but the summatory form of `Λ * 1 = log` (Mathlib's
`ArithmeticFunction.vonMangoldt_sum`). Mathlib provides the pointwise identity
at each `n`, but not yet the summatory version over `Icc 1 N`. The lemma below
fills this gap by induction on `N`, using `Nat.succ_div` to control the
increment `⌊(N+1)/d⌋ − ⌊N/d⌋ = [d ∣ N+1]`. -/

open scoped ArithmeticFunction in
/-- **Legendre's log-factorial identity (summatory form).** For every
    natural `N`,

    `log N! = ∑_{d ∈ Icc 1 N} Λ(d) · ⌊N/d⌋`.

    Equivalently, `(Λ * 1)` summed over `[1, N]` equals `log N!`. Such is the
    analytic identity that underlies Mertens' First Theorem; it is the summatory
    counterpart of `ArithmeticFunction.vonMangoldt_sum`. -/
lemma log_factorial_eq_sum_vonMangoldt_mul_floor (N : ℕ) :
    Real.log ((N.factorial : ℕ) : ℝ)
      = ∑ d ∈ Finset.Icc 1 N,
          ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    -- `(n+1)! = (n+1) · n!`, so `log (n+1)! = log (n+1) + log n!`.
    have h_split : Real.log (((n + 1).factorial : ℕ) : ℝ)
        = Real.log ((n + 1 : ℕ) : ℝ) + Real.log ((n.factorial : ℕ) : ℝ) := by
      have h1 : (((n + 1).factorial : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) * ((n.factorial : ℕ) : ℝ) := by
        push_cast [Nat.factorial_succ]; ring
      rw [h1, Real.log_mul (by exact_mod_cast (Nat.succ_ne_zero n))
            (by exact_mod_cast n.factorial_ne_zero)]
    rw [h_split, ih]
    have h_icc_split : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext k
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [h_icc_split, Finset.sum_insert (by simp : n + 1 ∉ Finset.Icc 1 n)]
    rw [show ((n + 1) / (n + 1) : ℕ) = 1 by exact Nat.div_self (Nat.succ_pos n)]
    -- Expand `(n+1)/d` via `Nat.succ_div : (n+1)/d = n/d + (if d ∣ n+1 then 1 else 0)`.
    have h_inner : ∀ d ∈ Finset.Icc 1 n,
        ArithmeticFunction.vonMangoldt d * (((n + 1) / d : ℕ) : ℝ)
          = ArithmeticFunction.vonMangoldt d * ((n / d : ℕ) : ℝ)
            + ArithmeticFunction.vonMangoldt d
                * (if d ∣ n + 1 then (1 : ℝ) else 0) := by
      intro d _
      rw [Nat.succ_div]
      by_cases hdvd : d ∣ n + 1
      · simp [hdvd]; ring
      · simp [hdvd]
    rw [Finset.sum_congr rfl h_inner, Finset.sum_add_distrib]
    -- The `if d ∣ n+1 then 1 else 0` piece selects divisors of `n+1` lying in `Icc 1 n`;
    -- adding `Λ(n+1)` gives the sum over `(n+1).divisors`, which equals `log(n+1)`
    -- via `ArithmeticFunction.vonMangoldt_sum`.
    have h_div_sum : ArithmeticFunction.vonMangoldt (n + 1)
        + ∑ d ∈ Finset.Icc 1 n,
            ArithmeticFunction.vonMangoldt d * (if d ∣ n + 1 then (1 : ℝ) else 0)
        = Real.log ((n + 1 : ℕ) : ℝ) := by
      have h_indicator : ∀ d ∈ Finset.Icc 1 n,
          ArithmeticFunction.vonMangoldt d * (if d ∣ n + 1 then (1 : ℝ) else 0)
            = if d ∣ n + 1 then ArithmeticFunction.vonMangoldt d else 0 := by
        intro d _; split_ifs <;> ring
      rw [Finset.sum_congr rfl h_indicator]
      rw [← Finset.sum_filter]
      have h_div_eq : (n + 1).divisors
          = insert (n + 1) ((Finset.Icc 1 n).filter (fun d => d ∣ n + 1)) := by
        ext d
        rw [Nat.mem_divisors]
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨hdvd, _⟩
          have hd_pos : 1 ≤ d := by
            rcases Nat.eq_zero_or_pos d with rfl | h
            · exact absurd (Nat.eq_zero_of_zero_dvd hdvd) (Nat.succ_ne_zero n)
            · exact h
          have hd_le : d ≤ n + 1 := Nat.le_of_dvd (Nat.succ_pos n) hdvd
          by_cases h : d = n + 1
          · left; exact h
          · right; exact ⟨⟨hd_pos, by omega⟩, hdvd⟩
        · rintro (rfl | ⟨⟨_, _⟩, hdvd⟩)
          · exact ⟨dvd_refl _, Nat.succ_ne_zero _⟩
          · exact ⟨hdvd, Nat.succ_ne_zero _⟩
      have h_not_mem : n + 1 ∉ (Finset.Icc 1 n).filter (fun d => d ∣ n + 1) := by
        intro hmem
        rw [Finset.mem_filter, Finset.mem_Icc] at hmem
        omega
      rw [show ArithmeticFunction.vonMangoldt (n + 1)
            + ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d ∣ n + 1),
                ArithmeticFunction.vonMangoldt d
          = ∑ d ∈ insert (n + 1) ((Finset.Icc 1 n).filter (fun d => d ∣ n + 1)),
              ArithmeticFunction.vonMangoldt d
          from (Finset.sum_insert h_not_mem).symm]
      rw [← h_div_eq]
      exact ArithmeticFunction.vonMangoldt_sum
    have h_one_mul : ArithmeticFunction.vonMangoldt (n + 1) * (1 : ℝ)
        = ArithmeticFunction.vonMangoldt (n + 1) := mul_one _
    linarith [h_div_sum]

/-! ### Abel summation pivot: `partialSumLog` as `θ(x)/x` plus an integral

The classical Mertens 1874 proof of M1 begins by **partial summation**, rewriting
`∑_{p ≤ x} (log p)/p` in terms of the Chebyshev function `θ(x) := ∑_{p ≤ x} log p`:

$$\sum_{p \le x} \frac{\log p}{p}
   \;=\; \frac{\theta(x)}{x} \,+\, \int_2^x \frac{\theta(t)}{t^2}\,dt.$$

This is the analogue, for `f(t) = 1/t`, of Mathlib's
`Chebyshev.primeCounting_eq_theta_div_log_add_integral` (which uses
`f(t) = 1/log t`). Once at our disposal, the identity combined with the
elementary Chebyshev bound `θ(t) = O(t)` yields M1: the boundary term is `O(1)`
and the integral is `O(log x) - O(1)`. More precisely, for M1 it is enough to
invoke `θ(t) = t + o(t)`, whence `partialSumLog x = log x + O(1)`.
-/

open Asymptotics Filter MeasureTheory in
/-- **Abel-summation pivot for Mertens M1.**

For every `x ≥ 2`,
$$\sum_{p \le x} \frac{\log p}{p}
   \;=\; \frac{\theta(x)}{x} \,+\, \int_2^x \frac{\theta(t)}{t^2}\,dt.$$

This is the Mertens analogue of Mathlib's
`Chebyshev.primeCounting_eq_theta_div_log_add_integral`, applied to
`f(t) = 1/t` rather than `f(t) = 1/\log t`. Such is the standard analytic
backbone of **Mertens' First Theorem**: combined with Chebyshev's bound
`θ(t) ≤ (\log 4) · t`, the right-hand side equals `log x + O(1)`. -/
theorem partialSumLog_eq_theta_div_x_add_integral {x : ℝ} (hx : 2 ≤ x) :
    partialSumLog x = Chebyshev.theta x / x
      + ∫ t in (2 : ℝ)..x, Chebyshev.theta t / t ^ 2 := by
  -- Rewrite `partialSumLog x` in the form to which Abel summation applies.
  unfold partialSumLog
  rw [Nat.primesBelow_eq_filter_range, Nat.range_succ_eq_Icc_zero, Finset.sum_filter]
  -- Abel-summation "sequence" `a(n) = log n · [n prime]`.
  let a : ℕ → ℝ := Set.indicator (setOf Nat.Prime) (fun n ↦ Real.log n)
  trans ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ((n : ℝ))⁻¹ * a n
  · refine Finset.sum_congr rfl fun n _hn ↦ ?_
    by_cases h : Nat.Prime n
    · simp [a, h, Set.indicator_of_mem, div_eq_mul_inv, mul_comm]
    · simp [a, h, Set.indicator_of_notMem]
  rw [sum_mul_eq_sub_integral_mul₁ a (f := fun t ↦ t⁻¹)
        (by simp [a]) (by simp [a, Nat.not_prime_one]),
      ← intervalIntegral.integral_of_le hx]
  · have hderiv : ∀ u ∈ Set.uIcc (2 : ℝ) x, deriv (fun t : ℝ ↦ t⁻¹) u = -(u ^ 2)⁻¹ := by
      intro u _; simp [deriv_inv']
    have int_deriv (g : ℝ → ℝ) :
        ∫ u in (2 : ℝ)..x, deriv (fun t : ℝ ↦ t⁻¹) u * g u
          = ∫ u in (2 : ℝ)..x, g u * -(u ^ 2)⁻¹ :=
      intervalIntegral.integral_congr fun u hu ↦ by
        rw [hderiv u hu]; ring
    rw [int_deriv]
    have hθ_sum : ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, a k = Chebyshev.theta x := by
      rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      by_cases h : Nat.Prime n
      · simp [a, h, Set.indicator_of_mem]
      · simp [a, h, Set.indicator_of_notMem]
    have hθ_partial : ∀ t : ℝ,
        ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, a k = Chebyshev.theta t := by
      intro t
      rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      by_cases h : Nat.Prime n
      · simp [a, h, Set.indicator_of_mem]
      · simp [a, h, Set.indicator_of_notMem]
    rw [hθ_sum]
    have hint_eq :
        ∫ u in (2 : ℝ)..x, Chebyshev.theta u * -(u ^ 2)⁻¹
          = -∫ u in (2 : ℝ)..x, Chebyshev.theta u / u ^ 2 := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun u _ ↦ ?_
      simp [div_eq_mul_inv]
    have hint_eq' :
        ∫ u in (2 : ℝ)..x, (∑ k ∈ Finset.Icc 0 ⌊u⌋₊, a k) * -(u ^ 2)⁻¹
          = ∫ u in (2 : ℝ)..x, Chebyshev.theta u * -(u ^ 2)⁻¹ :=
      intervalIntegral.integral_congr fun u _ ↦ by rw [hθ_partial u]
    rw [hint_eq', hint_eq]
    rw [sub_neg_eq_add]
    congr 1
    rw [mul_comm, div_eq_mul_inv]
  · -- Differentiability of `t ↦ t⁻¹` on `[2, x]` (avoiding `0`).
    intro z hz
    have hz_pos : (0 : ℝ) < z := by
      have : (2 : ℝ) ≤ z := hz.1
      linarith
    have hzne : z ≠ 0 := ne_of_gt hz_pos
    exact differentiableAt_inv hzne
  · -- Integrability of `deriv (·⁻¹) = -(·^2)⁻¹` on `[2, x]`: `deriv_inv'` gives an
    -- unconditional pointwise equality of functions, reducing to continuity of `-(z^2)⁻¹`.
    have hderiv_fn : (deriv fun t : ℝ ↦ t⁻¹) = fun z : ℝ ↦ -(z ^ 2)⁻¹ := deriv_inv'
    rw [hderiv_fn]
    refine ContinuousOn.integrableOn_Icc ?_
    intro z hz
    have hz_pos : (0 : ℝ) < z := by
      have : (2 : ℝ) ≤ z := hz.1
      linarith
    have hzne : z ≠ 0 := ne_of_gt hz_pos
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hzne
    exact ContinuousAt.continuousWithinAt (by fun_prop)

/-! ### Mertens' First Theorem (M1)

**Mertens' First Theorem.** The log-weighted partial sum of prime reciprocals
satisfies

$$\sum_{p \le x} \frac{\log p}{p} \;=\; \log x \,+\, O(1).$$

Equivalently, there exists a constant `C` such that
`|partialSumLog x - log x| ≤ C` for every `x ≥ 2`.

Such is the analytic input fed into Mertens' Third Theorem.

## Status (audit 2026-05-16)

The Abel-summation pivot `partialSumLog_eq_theta_div_x_add_integral` (lines ~322–403,
`sorry`-free) yields the identity
`partialSumLog x = θ(x)/x + ∫₂ˣ θ(t)/t² dt`.

**Route A (Abel + Chebyshev) is blocked by current Mathlib.**
Mathlib's elementary Chebyshev bounds (`Chebyshev.theta_le_log4_mul_x`,
`Chebyshev.theta_ge'`) sandwich `θ(t)` between `c·t` and `(log 4)·t` with
`c < 1 < log 4`. Plugging into the pivot gives
`partialSumLog x = c'·log x + O(1)` for **some** `c' ∈ [log 2 / 2, log 4]` —
the coefficient is not pinned to `1`. To get coefficient exactly `1` requires
one of the following ingredients:

* a **PNT-level estimate** `θ(t) = t + O(t/log t)`, currently **absent** from
  Mathlib (no `Chebyshev.theta_sub_self_isBigO`, no
  `tendsto_theta_div_id_atTop`); or
* a **Selberg-style elementary refinement** (Erdős–Selberg 1949), not in Mathlib
  either.

**Route B (Legendre + Stirling, Mertens' original 1874 proof)** is viable but
not yet implemented. The building blocks already available in Mathlib together
with the present file are:

1. `log_factorial_eq_sum_vonMangoldt_mul_floor` (this file, **closed**):
   `log N! = ∑_{d ≤ N} Λ(d) · ⌊N/d⌋`.
2. `Stirling.le_log_factorial_stirling` (Mathlib, effective lower bound):
   `n·log n - n + log n / 2 + log(2π)/2 ≤ log n!`.
3. `Stirling.log_stirlingSeq'_antitone` + `log_stirlingSeq_bounded_by_constant`
   give an effective two-sided bound: `log(stirlingSeq n)` is bounded by an
   explicit constant for all `n ≥ 1`, hence
   `|log n! - (n·log n - n + (1/2)·log(2n))| ≤ C_S` (explicit `C_S`).
4. `Chebyshev.psi_le_const_mul_self` (Mathlib): `ψ(n) ≤ C·n`.

The proof then runs:

  (a) Use Stirling to get `log n! = n·log n - n + O(log n)`.
  (b) Split the Legendre sum: `∑ Λ(d) ⌊n/d⌋ = n·∑ Λ(d)/d - ∑ Λ(d)·{n/d}`,
      where the fractional-part sum is `≤ ψ(n) ≤ C·n`.
  (c) Bound the prime-power tail:
      `∑_{d ≤ n} Λ(d)/d - partialSumLog n = ∑_{p^k ≤ n, k ≥ 2} (log p)/p^k`,
      which is `O(1)` (bounded by `∑_p (log p)/(p(p-1))`, convergent).
  (d) Divide by `n`, take `n = ⌊x⌋`, control `log x - log ⌊x⌋ ≤ log 2`.

## Effective Stirling bound

An effective version of Stirling's approximation, extracted from Mathlib's
`Stirling.log_stirlingSeq_formula`, `log_stirlingSeq_bounded_by_constant`, and
`log_stirlingSeq'_antitone`. The resulting bound
`|log n! − (n log n − n)| ≤ C · (1 + log n)` then feeds into the
Legendre–Stirling floor identity below.
-/

/-- **Effective Stirling bound.** There exists a constant `C ≥ 0`
such that, for every `n ≥ 1`,

  `|log n! − (n · log n − n)| ≤ C · (1 + log n)`.

Such is the variant of Stirling's approximation required for Mertens M1 via the
Legendre + Stirling route: the error term is `O(log n)`, which becomes `o(n)`
once divided by `n` in the Mertens estimate. -/
lemma stirling_log_factorial_effective :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      |Real.log ((n.factorial : ℕ) : ℝ) - ((n : ℝ) * Real.log n - n)| ≤ C * (1 + Real.log n) := by
  -- Set the bounds for log(stirlingSeq m) for m ≥ 1.
  -- Lower: 1 - 1/12 - log 2 / 2 ≤ log(stirlingSeq (k+1)) (k ≥ 0).
  -- Upper: log(stirlingSeq (k+1)) ≤ log(stirlingSeq 1) = 1 - log 2 / 2 (antitone).
  set Clo : ℝ := 1 - 12⁻¹ - Real.log 2 / 2 with hClodef
  set Chi : ℝ := 1 - Real.log 2 / 2 with hChidef
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- M := max |Clo| |Chi| bounds |log(stirlingSeq (k+1))|.
  set M : ℝ := |Clo| + |Chi| + 1 with hMdef
  have hM_nonneg : 0 ≤ M := by positivity
  -- The Stirling constant from the formula: |log n! - (n log n - n + log(2n)/2)| ≤ M.
  -- Bound from `log_stirlingSeq_formula`: log(stirlingSeq n) = log n! - log(2n)/2 - n*log(n/e).
  -- For n ≥ 1: n*log(n/e) = n*log n - n, so
  --   log n! = log(stirlingSeq n) + log(2n)/2 + n*log n - n.
  -- and |log(stirlingSeq n)| ≤ M (using bounds above).
  -- The full error |log n! - (n log n - n)| ≤ |log(stirlingSeq n)| + log(2n)/2
  -- ≤ M + log n/2 + log 2/2.
  -- Take C := M + log 2 / 2 + 1/2.
  refine ⟨M + Real.log 2 / 2 + 1, ?_, ?_⟩
  · positivity
  intro n hn
  -- Case n ≥ 1: n = k+1 for some k ≥ 0.
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  -- log_stirlingSeq_formula n: log(stirlingSeq n) = log n! - log(2n)/2 - n*log(n/e)
  have hform := Stirling.log_stirlingSeq_formula (k + 1)
  -- Compute n*log(n/e) = n*log n - n (since log(n/e) = log n - log e = log n - 1).
  have hkpos : (0 : ℝ) < (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
  have hkne : ((k + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hkpos
  have hlog_div : Real.log (((k + 1 : ℕ) : ℝ) / Real.exp 1)
      = Real.log ((k + 1 : ℕ) : ℝ) - 1 := by
    rw [Real.log_div hkne (Real.exp_ne_zero 1), Real.log_exp]
  have h_n_log_div :
      ((k + 1 : ℕ) : ℝ) * Real.log (((k + 1 : ℕ) : ℝ) / Real.exp 1)
        = ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ) := by
    rw [hlog_div]; ring
  -- log(stirlingSeq (k+1)) = log n! - log(2n)/2 - (n*log n - n).
  rw [h_n_log_div] at hform
  -- Bounds: Clo ≤ log(stirlingSeq (k+1)) ≤ Chi.
  have hlo : Clo ≤ Real.log (Stirling.stirlingSeq (k + 1)) := by
    have := Stirling.log_stirlingSeq_bounded_by_constant k
    -- Mathlib: 1 - 12⁻¹ - log 2 / 2 ≤ log(stirlingSeq (n+1))
    simpa [hClodef] using this
  have hhi : Real.log (Stirling.stirlingSeq (k + 1)) ≤ Chi := by
    -- antitone: log(stirlingSeq (m+1)) ≤ log(stirlingSeq 1) for m ≥ 0.
    have hanti := Stirling.log_stirlingSeq'_antitone (Nat.zero_le k)
    -- log_stirlingSeq'_antitone applies to `log ∘ stirlingSeq ∘ succ`,
    -- so hanti has type log(stirlingSeq (k+1)) ≤ log(stirlingSeq 1).
    -- compute Real.log (stirlingSeq 1) = 1 - log 2 / 2.
    have hs1 : Real.log (Stirling.stirlingSeq 1) = 1 - Real.log 2 / 2 := by
      rw [Stirling.stirlingSeq_one, Real.log_div (Real.exp_ne_zero 1)
        (by positivity : (Real.sqrt 2) ≠ 0), Real.log_exp, Real.log_sqrt (by norm_num)]
    -- hanti : Real.log (stirlingSeq (k+1)) ≤ Real.log (stirlingSeq 1)
    have hanti' : Real.log (Stirling.stirlingSeq (k + 1))
        ≤ Real.log (Stirling.stirlingSeq 1) := hanti
    rw [hs1] at hanti'
    exact hanti'.trans_eq hChidef.symm
  -- Derive |log(stirlingSeq (k+1))| ≤ M.
  have hClo_le : |Clo| ≤ M := by
    have : 0 ≤ |Chi| := abs_nonneg _
    have : (0 : ℝ) ≤ 1 := by norm_num
    change |Clo| ≤ |Clo| + |Chi| + 1
    linarith [abs_nonneg Chi]
  have hChi_le : |Chi| ≤ M := by
    change |Chi| ≤ |Clo| + |Chi| + 1
    linarith [abs_nonneg Clo]
  have habs_stir : |Real.log (Stirling.stirlingSeq (k + 1))| ≤ M := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h1 : -|Clo| ≤ Clo := neg_abs_le _
      have h2 : -M ≤ -|Clo| := by linarith
      linarith
    · calc Real.log (Stirling.stirlingSeq (k + 1))
          ≤ Chi := hhi
        _ ≤ |Chi| := le_abs_self _
        _ ≤ M := hChi_le
  -- From hform: log(stirlingSeq (k+1)) = log n! - log(2n)/2 - n*log n + n
  -- So log n! - (n*log n - n) = log(stirlingSeq (k+1)) + log(2n)/2.
  have heq :
      Real.log ((((k + 1 : ℕ).factorial : ℕ) : ℝ))
        - (((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ))
      = Real.log (Stirling.stirlingSeq (k + 1))
        + (1 : ℝ) / 2 * Real.log (2 * ((k + 1 : ℕ) : ℝ)) := by
    linarith [hform]
  rw [heq]
  -- |log(stirlingSeq (k+1)) + log(2n)/2| ≤ M + log(2n)/2.
  have h_one_le_2kp1 : (1 : ℝ) ≤ 2 * ((k + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    linarith
  have h_log_2n_nonneg : 0 ≤ Real.log (2 * ((k + 1 : ℕ) : ℝ)) :=
    Real.log_nonneg h_one_le_2kp1
  have h_log_2n_split : Real.log (2 * ((k + 1 : ℕ) : ℝ))
      = Real.log 2 + Real.log ((k + 1 : ℕ) : ℝ) :=
    Real.log_mul (by norm_num) hkne
  have h_log_n_nonneg : 0 ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
  have htri : |Real.log (Stirling.stirlingSeq (k + 1))
      + (1 : ℝ) / 2 * Real.log (2 * ((k + 1 : ℕ) : ℝ))|
      ≤ M + (1 : ℝ) / 2 * Real.log (2 * ((k + 1 : ℕ) : ℝ)) := by
    have habsadd := abs_add_le (Real.log (Stirling.stirlingSeq (k + 1)))
      ((1 : ℝ) / 2 * Real.log (2 * ((k + 1 : ℕ) : ℝ)))
    have habs_half : |(1 : ℝ) / 2 * Real.log (2 * ((k + 1 : ℕ) : ℝ))|
        = (1 : ℝ) / 2 * Real.log (2 * ((k + 1 : ℕ) : ℝ)) := by
      rw [abs_of_nonneg]
      positivity
    rw [habs_half] at habsadd
    linarith
  calc |Real.log (Stirling.stirlingSeq (k + 1))
        + (1 : ℝ) / 2 * Real.log (2 * ((k + 1 : ℕ) : ℝ))|
      ≤ M + (1 : ℝ) / 2 * Real.log (2 * ((k + 1 : ℕ) : ℝ)) := htri
    _ = M + (Real.log 2 + Real.log ((k + 1 : ℕ) : ℝ)) / 2 := by
        rw [h_log_2n_split]; ring
    _ ≤ (M + Real.log 2 / 2 + 1) * (1 + Real.log ((k + 1 : ℕ) : ℝ)) := by
        have hL2 : 0 ≤ Real.log 2 := le_of_lt hlog2_pos
        nlinarith [h_log_n_nonneg, hL2, hM_nonneg]

/-! ## Real-to-integer reduction

We reduce the real form of Mertens M1 to its integer form, by means of the
identity `partialSumLog x = partialSumLog ⌊x⌋₊` (immediate from the definition)
together with the elementary estimate `|log x − log ⌊x⌋₊| ≤ log 2` for `x ≥ 2`. -/

/-- The `partialSumLog` partial sum depends on `x` only through `⌊x⌋₊`. -/
lemma partialSumLog_eq_partialSumLog_floor (x : ℝ) :
    partialSumLog x = partialSumLog ((⌊x⌋₊ : ℕ) : ℝ) := by
  unfold partialSumLog
  congr 1
  rw [Nat.floor_natCast]

/-- For `x ≥ 2`, `log x − log ⌊x⌋₊` is bounded by `log 2`. -/
lemma abs_log_sub_log_floor_le {x : ℝ} (hx : 2 ≤ x) :
    |Real.log x - Real.log ((⌊x⌋₊ : ℕ) : ℝ)| ≤ Real.log 2 := by
  have h_floor_pos : (1 : ℝ) ≤ (⌊x⌋₊ : ℕ) := by
    have : (2 : ℕ) ≤ ⌊x⌋₊ := by
      rw [Nat.le_floor_iff (by linarith : (0 : ℝ) ≤ x)]
      exact_mod_cast hx
    exact_mod_cast (by omega : 1 ≤ ⌊x⌋₊)
  have h_floor_le_x : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
  have h_x_lt_succ : x < ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one x
    push_cast
    push_cast at this
    linarith
  -- log ⌊x⌋₊ ≤ log x ≤ log(⌊x⌋₊ + 1) ≤ log(2 · ⌊x⌋₊) = log 2 + log ⌊x⌋₊.
  have h_floor_pos_r : (0 : ℝ) < ((⌊x⌋₊ : ℕ) : ℝ) := by linarith
  have hlog_ge : Real.log ((⌊x⌋₊ : ℕ) : ℝ) ≤ Real.log x :=
    Real.log_le_log h_floor_pos_r h_floor_le_x
  have hsucc_le : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * ((⌊x⌋₊ : ℕ) : ℝ) := by
    push_cast; linarith
  have hlog_le : Real.log x ≤ Real.log (2 * ((⌊x⌋₊ : ℕ) : ℝ)) := by
    apply Real.log_le_log (by linarith : (0 : ℝ) < x)
    linarith
  have hlog_2n_split : Real.log (2 * ((⌊x⌋₊ : ℕ) : ℝ))
      = Real.log 2 + Real.log ((⌊x⌋₊ : ℕ) : ℝ) :=
    Real.log_mul (by norm_num) (ne_of_gt h_floor_pos_r)
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- −log 2 ≤ log x − log ⌊x⌋₊, equivalently log ⌊x⌋₊ − log 2 ≤ log x.
    have hlog2_nonneg : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos one_lt_two)
    linarith
  · -- log x − log ⌊x⌋₊ ≤ log 2.
    rw [hlog_2n_split] at hlog_le
    linarith

/-- **Real-to-integer reduction.** Given a uniform bound on `|partialSumLog N − log N|`
for natural numbers `N ≥ 2`, the same bound, shifted by `log 2`, holds for every
real `x ≥ 2`. -/
lemma first_of_nat
    (h : ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → |partialSumLog ((N : ℕ) : ℝ) - Real.log ((N : ℕ) : ℝ)| ≤ C) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |partialSumLog x - Real.log x| ≤ C := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C + Real.log 2, ?_⟩
  intro x hx
  have h_floor_ge : (2 : ℕ) ≤ ⌊x⌋₊ := by
    rw [Nat.le_floor_iff (by linarith : (0 : ℝ) ≤ x)]
    exact_mod_cast hx
  have hbnd := hC ⌊x⌋₊ h_floor_ge
  have hreduce := partialSumLog_eq_partialSumLog_floor x
  have habs := abs_log_sub_log_floor_le hx
  -- |partialSumLog x - log x| = |partialSumLog ⌊x⌋₊ - log x|
  --                       ≤ |partialSumLog ⌊x⌋₊ - log ⌊x⌋₊| + |log ⌊x⌋₊ - log x|
  --                       ≤ C + log 2.
  calc |partialSumLog x - Real.log x|
      = |partialSumLog ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x| := by rw [hreduce]
    _ = |partialSumLog ((⌊x⌋₊ : ℕ) : ℝ) - Real.log ((⌊x⌋₊ : ℕ) : ℝ)
          + (Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x)| := by ring_nf
    _ ≤ |partialSumLog ((⌊x⌋₊ : ℕ) : ℝ) - Real.log ((⌊x⌋₊ : ℕ) : ℝ)|
          + |Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x| :=
        abs_add_le _ _
    _ ≤ C + Real.log 2 := by
        have h1 : |Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x|
            = |Real.log x - Real.log ((⌊x⌋₊ : ℕ) : ℝ)| := abs_sub_comm _ _
        rw [h1]
        linarith

/-! ## Prime-power tail of `Λ(n)/n`

The prime-power tail — that is, the contribution of `Λ(p^k) = log p` for `k ≥ 2`
to `∑ Λ(n)/n` — is **absolutely summable**. Such is the second analytic input
into Mertens M1 via the Legendre + Stirling route.

The proof re-derives the unnamed (private) Mathlib machinery of
`Mathlib.NumberTheory.LSeries.PrimesInAP` (the lemmas `F''_le` and
`summable_F''`, lines 178–220 of that file), repackaged here as public lemmas
usable from this file. The bound is uniform in `n`:

  `(Λ(p^{k+2}) / p^{k+2}) = log p / p^{k+2} ≤ 2 · p^{-(k + 3/2)}`,

and the double sum over `(p, k) ∈ Primes × ℕ` is then dominated by the product
of a geometric series in `k` and the convergent `p`-series `∑ 1/p^{3/2}`.
-/

open ArithmeticFunction in
/-- Pointwise bound: `Λ(p^{k+2}) / p^{k+2} ≤ 2 · p^{-(k + 3/2)}` for every prime `p`
    and every `k : ℕ`. Repackaging of Mathlib's private `F''_le`. -/
private lemma vonMangoldt_prime_pow_div_le (p : Nat.Primes) (k : ℕ) :
    Real.log (p.val : ℝ) * ((p.val : ℝ)⁻¹) ^ (k + 2)
      ≤ 2 * ((p.val : ℝ)⁻¹) ^ (k + 3 / 2 : ℝ) := by
  calc Real.log (p.val : ℝ) * ((p.val : ℝ)⁻¹) ^ (k + 2)
      ≤ (p.val : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) * ((p.val : ℝ)⁻¹) ^ (k + 2) :=
        mul_le_mul_of_nonneg_right (Real.log_le_rpow_div p.val.cast_nonneg one_half_pos)
          (pow_nonneg (inv_nonneg_of_nonneg (Nat.cast_nonneg ↑p)) (k + 2))
    _ = 2 * ((p.val : ℝ)⁻¹) ^ (-1 / 2 : ℝ) * ((p.val : ℝ)⁻¹) ^ (k + 2) := by
        simp only [← div_mul, div_one, mul_comm, neg_div, Real.inv_rpow p.val.cast_nonneg,
          ← Real.rpow_neg p.val.cast_nonneg, neg_neg]
    _ = 2 * ((p.val : ℝ)⁻¹) ^ (k + 3 / 2 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_natCast (((p.val : ℝ))⁻¹) (k + 2),
          ← Real.rpow_add <| by have := p.prop.pos; positivity, Nat.cast_add, Nat.cast_two,
          add_comm, add_assoc]
        norm_num

set_option maxHeartbeats 400000 in
-- Increased heartbeats: the proof unfolds an `rpow`/geometric-series bound term-by-term
-- on a product index `Nat.Primes × ℕ`, with several `Real.rpow` manipulations and
-- `congr` rewrites that exceed the default budget on the slowest CI runners.
/-- Summability of `(p, k) ↦ Λ(p^{k+2}) / p^{k+2}` over `Nat.Primes × ℕ`.
    Repackaging of Mathlib's private `summable_F''`. -/
private lemma summable_prime_pow_tail_prod :
    Summable (fun pk : Nat.Primes × ℕ =>
      Real.log (pk.1.val : ℝ) * ((pk.1.val : ℝ)⁻¹) ^ (pk.2 + 2)) := by
  have hp₀ (p : Nat.Primes) : 0 < (p.val : ℝ)⁻¹ :=
    inv_pos_of_pos (Nat.cast_pos.mpr p.prop.pos)
  have hp₁ (p : Nat.Primes) : (p.val : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ <| mod_cast p.prop.pos).mpr <| Nat.one_lt_cast.mpr <| p.prop.one_lt
  -- Bound the function by the rpow form which factors as a geometric × p-series.
  suffices Summable fun (pk : Nat.Primes × ℕ) ↦ ((pk.1.val : ℝ)⁻¹) ^ (pk.2 + 3 / 2 : ℝ) by
    refine (Summable.mul_left 2 this).of_nonneg_of_le (fun pk ↦ ?_)
      (fun pk ↦ vonMangoldt_prime_pow_div_le pk.1 pk.2)
    have hpos : (0 : ℝ) ≤ ((pk.1.val : ℝ))⁻¹ := le_of_lt (hp₀ pk.1)
    have h1 : (0 : ℝ) ≤ Real.log (pk.1.val : ℝ) :=
      Real.log_nonneg (by exact_mod_cast pk.1.prop.one_lt.le)
    exact mul_nonneg h1 (pow_nonneg hpos _)
  conv => enter [1, pk]; rw [Real.rpow_add <| hp₀ pk.1, Real.rpow_natCast]
  refine (summable_prod_of_nonneg (fun _ ↦ by positivity)).mpr ⟨(fun p ↦ ?_), ?_⟩
  · dsimp only
    exact Summable.mul_right _ <| summable_geometric_of_lt_one (hp₀ p).le (hp₁ p)
  · dsimp only
    conv => enter [1, p]; rw [tsum_mul_right, tsum_geometric_of_lt_one (hp₀ p).le (hp₁ p)]
    -- Bound: `∑' p, (p⁻¹)^(3/2) * (1 - p⁻¹)⁻¹ ≤ 2 · ∑' p, p^(-3/2)`, a convergent
    -- `p`-series, lifted via the `Subtype.val` injection from `Nat.Primes` to `ℕ`.
    have h_summable_primes : Summable (fun p : Nat.Primes ↦ 2 * ((p.val : ℝ)⁻¹) ^ (3 / 2 : ℝ)) := by
      have hbase : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
        Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1)
      have hbase2 : Summable (fun n : ℕ ↦ 2 * (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
        hbase.mul_left 2
      have hinj : Function.Injective (fun p : Nat.Primes => (p.val : ℕ)) :=
        fun p q h => Subtype.ext h
      have h_comp : Summable (fun p : Nat.Primes ↦ 2 * ((p.val : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) :=
        hbase2.comp_injective hinj
      refine h_comp.congr ?_
      intro p
      rw [Real.inv_rpow p.val.cast_nonneg, Real.rpow_neg p.val.cast_nonneg]
    refine h_summable_primes.of_nonneg_of_le (fun p ↦ ?_) (fun p ↦ ?_)
    · positivity [sub_pos.mpr (hp₁ p)]
    · -- Reduces to `(1 - p⁻¹)⁻¹ ≤ 2`, since `(p⁻¹)^(3/2) ≥ 0`.
      have h_factor_nn : 0 ≤ ((p.val : ℝ)⁻¹) ^ (3 / 2 : ℝ) :=
        Real.rpow_nonneg (le_of_lt (hp₀ p)) _
      have h_one_sub_pos : 0 < (1 - (p.val : ℝ)⁻¹) := sub_pos.mpr (hp₁ p)
      have h_inv_le_two : (1 - (p.val : ℝ)⁻¹)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ h_one_sub_pos zero_lt_two, le_sub_comm,
          show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num,
          inv_le_inv₀ (mod_cast p.prop.pos) zero_lt_two]
        exact Nat.ofNat_le_cast.mpr p.prop.two_le
      exact mul_le_mul_of_nonneg_right h_inv_le_two h_factor_nn

/-- Auxiliary function `F₀` from Mathlib's `PrimesInAP` private machinery,
    repackaged here. It is `0` on primes and on non-prime-powers, and equals
    `Λ(n) / n` on prime powers `p^k` with `k ≥ 2`. -/
private noncomputable def primePowerTailFn (n : ℕ) : ℝ :=
  (if n.Prime then 0 else ArithmeticFunction.vonMangoldt n) / (n : ℝ)

open ArithmeticFunction in
private lemma primePowerTailFn_nonneg (n : ℕ) : 0 ≤ primePowerTailFn n := by
  unfold primePowerTailFn
  split_ifs with h
  · simp
  · positivity [vonMangoldt_nonneg (n := n)]

set_option maxHeartbeats 400000 in
-- Increased heartbeats: the proof transports summability across the equivalence
-- `Nat.Primes × ℕ ≃ {n // IsPrimePow n}` and the injective shift `(p,j) ↦ (p, j+1)`,
-- which generates many `simp`/`rw`/`Function.Injective.summable_iff` steps.
/-- **Summability of the prime-power tail.** The function `n ↦ Λ(n)/n`
    restricted to non-primes is summable. Equivalently, the contribution of
    prime powers `p^k` with `k ≥ 2` to `∑ Λ(n)/n` is finite. -/
private lemma summable_primePowerTailFn : Summable primePowerTailFn := by
  -- Factor through the equivalence `Nat.Primes × ℕ ≃ {n // IsPrimePow n}` and the
  -- injective shift `(p, j) ↦ (p, j + 1)` (which excludes `(p, 0)` corresponding
  -- to `p^1 = p` — a prime, where `primePowerTailFn = 0`).
  have hF0_on_prime (p : Nat.Primes) : primePowerTailFn p.val = 0 := by
    simp only [primePowerTailFn, p.prop, ↓reduceIte, zero_div]
  have hF0_off_pp : ∀ n : ℕ, ¬ IsPrimePow n → primePowerTailFn n = 0 := by
    intro n hn
    have hΛ : ArithmeticFunction.vonMangoldt n = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
    have hnp : ¬ n.Prime := fun hp => hn hp.isPrimePow
    simp [primePowerTailFn, hΛ, hnp]
  -- Reduce to summability on `{n // IsPrimePow n}` (vanishes outside this set).
  suffices h_sub : Summable (primePowerTailFn ∘ (Subtype.val : {n : ℕ // IsPrimePow n} → ℕ)) by
    have h_ind : Summable (({n : ℕ | IsPrimePow n}).indicator primePowerTailFn) :=
      (summable_subtype_iff_indicator (f := primePowerTailFn)
        (s := {n : ℕ | IsPrimePow n})).mp h_sub
    refine h_ind.congr ?_
    intro n
    exact Set.indicator_apply_eq_self.mpr (fun hn => hF0_off_pp n hn)
  -- Transport across `Nat.Primes × ℕ ≃ {n // IsPrimePow n}` via `prodNatEquiv`;
  -- `coe_prodNatEquiv_apply` gives `(prodNatEquiv (p, k) : ℕ) = p^(k+1)`.
  rw [← Nat.Primes.prodNatEquiv.summable_iff]
  set g : Nat.Primes × ℕ → ℝ :=
    fun pk => primePowerTailFn ((pk.1.val : ℕ) ^ (pk.2 + 1)) with hg_def
  have h_goal_eq : ((primePowerTailFn ∘ Subtype.val) ∘ Nat.Primes.prodNatEquiv) = g := by
    funext pk
    obtain ⟨p, k⟩ := pk
    simp only [Function.comp_apply, g, Nat.Primes.coe_prodNatEquiv_apply]
  rw [h_goal_eq]
  -- The shift `Prod.map id (· + 1)` is injective with image `{pk | pk.2 ≥ 1}`;
  -- the complement is `{pk | pk.2 = 0}`, where `g` vanishes (since `p^1 = p` is prime).
  have h_inj : Function.Injective
      ((Prod.map _root_.id (· + 1)) : Nat.Primes × ℕ → Nat.Primes × ℕ) :=
    Function.Injective.prodMap (fun ⦃_ _⦄ a ↦ a) (fun _ _ h => by omega)
  have h_zero_outside : ∀ pk ∉ Set.range
      ((Prod.map _root_.id (· + 1)) : Nat.Primes × ℕ → Nat.Primes × ℕ),
      g pk = 0 := by
    intro pk hpk
    have hpk2 : pk.2 = 0 := by
      by_contra hne
      apply hpk
      refine ⟨(pk.1, pk.2 - 1), ?_⟩
      simp only [Prod.map_apply, id_eq]
      ext
      · rfl
      · dsimp; omega
    simp only [g, hpk2, zero_add, pow_one, hF0_on_prime]
  rw [← Function.Injective.summable_iff h_inj h_zero_outside]
  refine summable_prime_pow_tail_prod.congr ?_
  intro pj
  obtain ⟨p, k⟩ := pj
  change Real.log (p.val : ℝ) * ((p.val : ℝ)⁻¹) ^ (k + 2)
    = primePowerTailFn ((p.val : ℕ) ^ (k + 1 + 1))
  have h_pow_eq : k + 1 + 1 = k + 2 := by omega
  rw [h_pow_eq]
  have h_ne_prime : ¬ ((p.val : ℕ) ^ (k + 2)).Prime :=
    Nat.Prime.not_prime_pow (by omega : 2 ≤ k + 2)
  have hΛ : ArithmeticFunction.vonMangoldt ((p.val : ℕ) ^ (k + 2))
      = Real.log (p.val : ℝ) := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : k + 2 ≠ 0),
      ArithmeticFunction.vonMangoldt_apply_prime p.prop]
  change Real.log (p.val : ℝ) * ((p.val : ℝ)⁻¹) ^ (k + 2)
    = (if ((p.val : ℕ) ^ (k + 2)).Prime then 0
        else ArithmeticFunction.vonMangoldt ((p.val : ℕ) ^ (k + 2))) /
          (((p.val : ℕ) ^ (k + 2) : ℕ) : ℝ)
  rw [if_neg h_ne_prime, hΛ]
  push_cast
  rw [div_eq_mul_inv, inv_pow]

set_option maxHeartbeats 400000 in
-- Increased heartbeats: the `congr` against `summable_primePowerTailFn` requires
-- a `by_cases` on `n.Prime` followed by `simp only` rewrites involving
-- `ArithmeticFunction.vonMangoldt_apply_prime` and conditional arithmetic.
/-- The prime-power tail of `∑ Λ(n)/n` is absolutely summable: concretely,
    `Λ(n)/n − [n prime] · log n / n` is summable. -/
theorem summable_vonMangoldt_prime_power_tail :
    Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n
        - (if n.Prime then Real.log n else 0)) / (n : ℝ)) := by
  -- Pointwise, this expression equals `primePowerTailFn n`:
  --   if n.Prime: (log n − log n)/n = 0 = (if n.Prime then 0 else Λ n) / n.
  --   else:      (Λ n − 0)/n = Λ n / n = (if n.Prime then 0 else Λ n) / n.
  refine summable_primePowerTailFn.congr ?_
  intro n
  unfold primePowerTailFn
  by_cases h : n.Prime
  · simp only [h, ↓reduceIte, ArithmeticFunction.vonMangoldt_apply_prime h, sub_self,
      zero_div]
  · simp only [h, ↓reduceIte, sub_zero]

/-! ## Legendre-Stirling floor identity (integer form)

We combine `log_factorial_eq_sum_vonMangoldt_mul_floor` (Legendre),
`stirling_log_factorial_effective`, `Chebyshev.psi_le_const_mul_self`, and
`summable_vonMangoldt_prime_power_tail` so as to produce a uniform `O(1)` bound
on `|partialSumLog N − log N|`, valid for every natural `N ≥ 2`.

The proof relies on the decomposition `(N / d : ℕ) = (N : ℝ)/d − ((N % d : ℕ)/d)`,
together with the estimate `∑ Λ(d) · (N % d / d) ≤ ψ(N)` and the prime-power
tail bound established above. -/

/-- For every `N ≥ 1` and `d ≥ 1`, casting Mathlib's natural-number division
`(N / d : ℕ)` to `ℝ` equals `N/d − (N % d)/d`. -/
private lemma cast_nat_div_eq_real_div_sub_mod (N d : ℕ) (hd : 1 ≤ d) :
    (((N / d : ℕ) : ℕ) : ℝ) = (N : ℝ) / d - ((N % d : ℕ) : ℝ) / d := by
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  have h_eq : (N : ℝ) = (d : ℝ) * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) := by
    have := Nat.div_add_mod N d
    have hcast : ((d * (N / d) + N % d : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast this
    push_cast at hcast
    linarith
  field_simp
  linarith

set_option maxHeartbeats 800000 in
-- Increased heartbeats: this is the core integer-form lemma combining the Legendre
-- identity, Stirling's effective bound, Chebyshev's ψ-bound and the prime-power
-- tail. The proof carries several `field_simp`/`linarith`/`Finset.sum_congr`
-- steps over the same goal, well above the default budget.
/-- Integer-form Legendre-Stirling identity: there exists a constant `C ≥ 0`
    such that, for every natural `N ≥ 2`,

    `|partialSumLog N − log N| ≤ C`.

    Such is the heart of Mertens' First Theorem; it follows from the Legendre
    identity `log N! = ∑ Λ(d) ⌊N/d⌋`, Stirling's effective form, Chebyshev's
    `ψ`-bound, and the absolute summability of the prime-power tail of
    `∑ Λ(n)/n`. -/
lemma partialSumLog_floor_eq_log_floor_add_bounded :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → |partialSumLog ((N : ℕ) : ℝ) - Real.log ((N : ℕ) : ℝ)| ≤ C := by
  -- Set up the constants from the closed sub-lemmas.
  obtain ⟨C_S, hC_S_nn, hStirling⟩ := stirling_log_factorial_effective
  set T : ℝ := ∑' n : ℕ,
      (ArithmeticFunction.vonMangoldt n
        - (if n.Prime then Real.log n else 0)) / (n : ℝ) with hT_def
  have hT_nn : 0 ≤ T := by
    refine tsum_nonneg (fun n => ?_)
    -- Pointwise: `(Λ(n) − [n.Prime] log n) / n = primePowerTailFn n ≥ 0`.
    have hpp_nn : 0 ≤ primePowerTailFn n := primePowerTailFn_nonneg n
    rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
    · subst hn0; simp
    · by_cases hp : n.Prime
      · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
      · simp only [hp, ↓reduceIte, sub_zero]
        unfold primePowerTailFn at hpp_nn
        simp only [hp, ↓reduceIte] at hpp_nn
        exact hpp_nn
  set C_psi : ℝ := Real.log 4 + 4 with hC_psi_def
  have hC_psi_nn : 0 ≤ C_psi := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  refine ⟨C_S + C_psi + T + 1, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  have hN_pos : 0 < N := by omega
  have hN_R_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have hN_R_ge_2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN_R_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_R_pos
  have h_log_N_nn : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by linarith)
  -- Legendre identity `log N! = ∑ Λ(d) ⌊N/d⌋`, decomposed via
  -- `cast_nat_div_eq_real_div_sub_mod` into a main `N · ∑ Λ(d)/d` part and a fractional
  -- residual `∑ Λ(d) · (N % d)/d` controlled by Chebyshev's `ψ`.
  have hLegendre := log_factorial_eq_sum_vonMangoldt_mul_floor N
  have h_decomp : ∀ d ∈ Finset.Icc 1 N,
      ArithmeticFunction.vonMangoldt d * (((N / d : ℕ) : ℕ) : ℝ)
        = (N : ℝ) * (ArithmeticFunction.vonMangoldt d / d)
          - ArithmeticFunction.vonMangoldt d * (((N % d : ℕ) : ℝ) / d) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd_pos : 0 < d := hd.1
    have hd_R_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
    have hd_R_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_R_pos
    rw [cast_nat_div_eq_real_div_sub_mod N d hd.1]
    field_simp
  rw [Finset.sum_congr rfl h_decomp] at hLegendre
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hLegendre
  -- `hLegendre : log N! = N * S_main - S_resid`.
  set S_main : ℝ := ∑ d ∈ Finset.Icc 1 N,
    ArithmeticFunction.vonMangoldt d / (d : ℝ) with hS_main_def
  set S_resid : ℝ := ∑ d ∈ Finset.Icc 1 N,
    ArithmeticFunction.vonMangoldt d * (((N % d : ℕ) : ℝ) / d) with hS_resid_def
  have h_resid_nn_each : ∀ d ∈ Finset.Icc 1 N,
      (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt d * (((N % d : ℕ) : ℝ) / d) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd_pos : 0 < d := hd.1
    have hd_R_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
    have hΛ_nn : 0 ≤ ArithmeticFunction.vonMangoldt d :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hmod_nn : 0 ≤ ((N % d : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
    positivity
  have h_resid_each_le : ∀ d ∈ Finset.Icc 1 N,
      ArithmeticFunction.vonMangoldt d * (((N % d : ℕ) : ℝ) / d)
        ≤ ArithmeticFunction.vonMangoldt d := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd_pos : 0 < d := hd.1
    have hd_R_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
    have hΛ_nn : 0 ≤ ArithmeticFunction.vonMangoldt d :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hmod_lt : N % d < d := Nat.mod_lt N hd_pos
    have hmod_le : ((N % d : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hmod_lt.le
    have h_frac_le_one : ((N % d : ℕ) : ℝ) / d ≤ 1 := by
      rw [div_le_one hd_R_pos]; exact hmod_le
    have h_frac_nn : 0 ≤ ((N % d : ℕ) : ℝ) / d := by
      apply div_nonneg
      · exact_mod_cast Nat.zero_le _
      · exact le_of_lt hd_R_pos
    calc ArithmeticFunction.vonMangoldt d * (((N % d : ℕ) : ℝ) / d)
        ≤ ArithmeticFunction.vonMangoldt d * 1 :=
          mul_le_mul_of_nonneg_left h_frac_le_one hΛ_nn
      _ = ArithmeticFunction.vonMangoldt d := by ring
  -- Bound `S_resid ≤ ψ(N) ≤ C_psi · N` via Chebyshev's `ψ`-bound (with `⌊N⌋₊ = N`).
  have h_S_resid_nn : 0 ≤ S_resid :=
    Finset.sum_nonneg h_resid_nn_each
  have h_psi_eq : Chebyshev.psi (N : ℝ) =
      ∑ d ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt d := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  have h_psi_le : Chebyshev.psi (N : ℝ) ≤ C_psi * (N : ℝ) :=
    Chebyshev.psi_le_const_mul_self (le_of_lt hN_R_pos)
  have h_S_resid_le_psi : S_resid ≤ Chebyshev.psi (N : ℝ) := by
    rw [h_psi_eq]
    have h_sub : ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d
        ≤ ∑ d ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        rw [Finset.mem_Icc] at *
        omega
      · intros
        exact ArithmeticFunction.vonMangoldt_nonneg
    calc S_resid
        ≤ ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d :=
          Finset.sum_le_sum h_resid_each_le
      _ ≤ ∑ d ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt d := h_sub
  have h_S_resid_le : S_resid ≤ C_psi * (N : ℝ) :=
    le_trans h_S_resid_le_psi h_psi_le
  -- Express `partialSumLog N = ∑ p ∈ primesBelow (N+1), log p / p` as a sum over
  -- `Icc 1 N` of `[d.Prime] * log d / d`. `range (N+1) = {0,...,N}` and `Icc 1 N`
  -- differ only at `d = 0`, which is not prime, so the filters agree.
  have h_partialSumLog_as_sum :
      partialSumLog ((N : ℕ) : ℝ)
        = ∑ d ∈ Finset.Icc 1 N,
            (if d.Prime then Real.log (d : ℝ) else 0) / (d : ℝ) := by
    unfold partialSumLog
    rw [Nat.floor_natCast]
    rw [Nat.primesBelow_eq_filter_range]
    rw [show (∑ d ∈ Finset.Icc 1 N,
              (if d.Prime then Real.log (d : ℝ) else 0) / (d : ℝ))
          = ∑ d ∈ Finset.Icc 1 N with d.Prime, Real.log (d : ℝ) / (d : ℝ) from ?_]
    · apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext d
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      constructor
      · rintro ⟨hd_lt, hd_prime⟩
        refine ⟨⟨hd_prime.one_lt.le, by omega⟩, hd_prime⟩
      · rintro ⟨⟨hd_ge, hd_le⟩, hd_prime⟩
        exact ⟨by omega, hd_prime⟩
    · rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      by_cases h : d.Prime
      · simp [h]
      · simp [h]
  -- `S_tail = S_main − partialSumLog N`, the finite prime-power tail.
  set S_tail : ℝ := ∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.vonMangoldt d
        - (if d.Prime then Real.log (d : ℝ) else 0)) / (d : ℝ) with hS_tail_def
  have h_S_main_decomp : S_main = partialSumLog ((N : ℕ) : ℝ) + S_tail := by
    rw [hS_main_def, h_partialSumLog_as_sum, hS_tail_def, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd_pos : 0 < d := hd.1
    have hd_R_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
    have hd_R_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_R_pos
    field_simp
    ring
  -- S_tail is bounded by T (the full tsum).
  have h_S_tail_nn : 0 ≤ S_tail := by
    apply Finset.sum_nonneg
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd_pos : 0 < d := hd.1
    have hd_R_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
    have hpp_nn : 0 ≤ primePowerTailFn d := primePowerTailFn_nonneg d
    by_cases hp : d.Prime
    · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp only [hp, ↓reduceIte, sub_zero]
      unfold primePowerTailFn at hpp_nn
      simp only [hp, ↓reduceIte] at hpp_nn
      exact hpp_nn
  have h_S_tail_le_T : S_tail ≤ T := by
    rw [hT_def]
    have h_sum_eq : S_tail = ∑ d ∈ Finset.Icc 1 N,
        (fun n : ℕ => (ArithmeticFunction.vonMangoldt n
          - (if n.Prime then Real.log n else 0)) / (n : ℝ)) d := by
      rfl
    rw [h_sum_eq]
    apply Summable.sum_le_tsum (f := fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n
        - (if n.Prime then Real.log n else 0)) / (n : ℝ))
    · intro n _
      have hpp_nn : 0 ≤ primePowerTailFn n := primePowerTailFn_nonneg n
      rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
      · subst hn0; simp
      · by_cases hp : n.Prime
        · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
        · simp only [hp, ↓reduceIte, sub_zero]
          unfold primePowerTailFn at hpp_nn
          simp only [hp, ↓reduceIte] at hpp_nn
          exact hpp_nn
    · exact summable_vonMangoldt_prime_power_tail
  -- Substitute the decomposition `S_main = partialSumLog N + S_tail` into the
  -- Legendre identity to get `log N! = N · partialSumLog N + N · S_tail − S_resid`,
  -- then bring in Stirling: `log N! = N log N − N + δ` with `|δ| ≤ C_S · (1 + log N)`.
  -- Rearranging and dividing by `N` yields
  -- `partialSumLog N − log N = (−N + δ + S_resid − N · S_tail) / N`,
  -- bounded by `(1 + T + C_psi + C_S) · 1` since `(1 + log N) / N ≤ 1` for `N ≥ 1`.
  have hLegendre' : Real.log ((N.factorial : ℕ) : ℝ)
      = (N : ℝ) * partialSumLog ((N : ℕ) : ℝ) + (N : ℝ) * S_tail - S_resid := by
    rw [hLegendre, h_S_main_decomp]; ring
  have hStir := hStirling N hN1
  set δ : ℝ := Real.log ((N.factorial : ℕ) : ℝ) - ((N : ℝ) * Real.log N - N) with hδ_def
  have hδ_abs : |δ| ≤ C_S * (1 + Real.log N) := hStir
  have h_eqδ : Real.log ((N.factorial : ℕ) : ℝ) = (N : ℝ) * Real.log N - N + δ := by
    rw [hδ_def]; ring
  rw [h_eqδ] at hLegendre'
  have h_key : (N : ℝ) * partialSumLog ((N : ℕ) : ℝ) - (N : ℝ) * Real.log N
      = -(N : ℝ) + δ + S_resid - (N : ℝ) * S_tail := by linarith
  have h_div : partialSumLog ((N : ℕ) : ℝ) - Real.log N
      = (- (N : ℝ) + δ + S_resid - (N : ℝ) * S_tail) / N := by
    have : (N : ℝ) * (partialSumLog ((N : ℕ) : ℝ) - Real.log N)
        = -(N : ℝ) + δ + S_resid - (N : ℝ) * S_tail := by
      rw [mul_sub]; linarith
    field_simp at this ⊢
    linarith
  rw [h_div]
  rw [abs_div, abs_of_pos hN_R_pos]
  rw [div_le_iff₀ hN_R_pos]
  have h_log_inv : (1 + Real.log (N : ℝ)) ≤ (N : ℝ) := by
    -- `Real.log x ≤ x - 1`, so `1 + log x ≤ x` for `x > 0`.
    have h := Real.log_le_sub_one_of_pos hN_R_pos
    linarith
  have h_logN_div : C_S * (1 + Real.log (N : ℝ)) ≤ C_S * (N : ℝ) :=
    mul_le_mul_of_nonneg_left h_log_inv hC_S_nn
  have hδ_le_CSN : |δ| ≤ C_S * (N : ℝ) := le_trans hδ_abs h_logN_div
  have h_abs : |-(N : ℝ) + δ + S_resid - (N : ℝ) * S_tail|
      ≤ (N : ℝ) + |δ| + S_resid + (N : ℝ) * S_tail := by
    have h1 : |-(N : ℝ) + δ + S_resid - (N : ℝ) * S_tail|
        ≤ |-(N : ℝ) + δ + S_resid| + |(N : ℝ) * S_tail| := by
      have := abs_sub (-(N : ℝ) + δ + S_resid) ((N : ℝ) * S_tail)
      exact this
    have h2 : |-(N : ℝ) + δ + S_resid| ≤ |-(N : ℝ) + δ| + |S_resid| :=
      abs_add_le _ _
    have h3 : |-(N : ℝ) + δ| ≤ |-(N : ℝ)| + |δ| :=
      abs_add_le _ _
    have h4 : |-(N : ℝ)| = (N : ℝ) := by rw [abs_neg, abs_of_pos hN_R_pos]
    have h5 : |S_resid| = S_resid := abs_of_nonneg h_S_resid_nn
    have h6 : |(N : ℝ) * S_tail| = (N : ℝ) * S_tail := by
      rw [abs_mul, abs_of_pos hN_R_pos, abs_of_nonneg h_S_tail_nn]
    linarith
  have h_S_tail_le_T' : (N : ℝ) * S_tail ≤ (N : ℝ) * T :=
    mul_le_mul_of_nonneg_left h_S_tail_le_T (le_of_lt hN_R_pos)
  have h_combine : (N : ℝ) + |δ| + S_resid + (N : ℝ) * S_tail
      ≤ (N : ℝ) + C_S * (N : ℝ) + C_psi * (N : ℝ) + (N : ℝ) * T := by
    linarith
  calc |-(N : ℝ) + δ + S_resid - (N : ℝ) * S_tail|
      ≤ (N : ℝ) + |δ| + S_resid + (N : ℝ) * S_tail := h_abs
    _ ≤ (N : ℝ) + C_S * (N : ℝ) + C_psi * (N : ℝ) + (N : ℝ) * T := h_combine
    _ = (C_S + C_psi + T + 1) * (N : ℝ) := by ring

/-- **Mertens' First Theorem (M1).** The log-weighted partial sum of prime
    reciprocals equals `log x + O(1)`. -/
theorem first :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |partialSumLog x - Real.log x| ≤ C :=
  first_of_nat partialSumLog_floor_eq_log_floor_add_bounded

end Mertens
