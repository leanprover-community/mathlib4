/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude)
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Log.Sum

import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.Exponential

/-!
# Mertens' first theorem

We prove Mertens' first theorem in explicit form: for every natural number `N ≥ 1`,

  `log N - 1 ≤ ∑ n ∈ Ioc 0 N, Λ n / n ≤ log N + (log 4 + 4)`.

The proof is elementary: `log N! = ∑ d ≤ N, Λ d * ⌊N / d⌋` and Chebyshev's bound
`ψ N ≤ (log 4 + 4) N`.

## Main statements

* `Mertens.log_factorial_eq`: `log N! = ∑ d ∈ Ioc 0 N, Λ d * ⌊N / d⌋`
* `Mertens.mertens_first`: the two-sided bound above
* `Mertens.sum_vonMangoldt_div_unbounded`: `∑ n ≤ N, Λ n / n` is unbounded
-/

@[expose] public section

namespace Mertens


open ArithmeticFunction Finset Chebyshev Real

/-- `log N! = Σ_{d ≤ N} Λ(d) ⌊N/d⌋`. -/
theorem log_factorial_eq (N : ℕ) :
    Real.log (Nat.factorial N : ℕ) = ∑ d ∈ Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
  have h1 : Real.log (Nat.factorial N : ℕ) = ∑ n ∈ Ioc 0 N, Real.log n := by
    rw [← Real.log_prod]
    · congr 1
      have hI : Ioc 0 N = Ico 1 (N + 1) := by ext x; simp only [mem_Ioc, mem_Ico]; omega
      rw [hI, ← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial]
    · intro n hn
      have : 0 < n := (mem_Ioc.mp hn).1
      exact_mod_cast this.ne'
  have h2 : ∑ n ∈ Ioc 0 N, Real.log n = ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, Λ d := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [vonMangoldt_sum]
  rw [h1, h2]
  have h3 : ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, Λ d =
      ∑ d ∈ Ioc 0 N, ∑ n ∈ (Ioc 0 N).filter (d ∣ ·), Λ d := by
    refine Finset.sum_comm' fun n d => ?_
    simp only [mem_Ioc, Nat.mem_divisors, mem_filter]
    constructor
    · rintro ⟨⟨hn0, hnN⟩, hdn, _⟩
      exact ⟨⟨⟨hn0, hnN⟩, hdn⟩, Nat.pos_of_dvd_of_pos hdn hn0,
        (Nat.le_of_dvd hn0 hdn).trans hnN⟩
    · rintro ⟨⟨⟨hn0, hnN⟩, hdn⟩, _, _⟩
      exact ⟨⟨hn0, hnN⟩, hdn, hn0.ne'⟩
  rw [h3]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]
  ring

/-- `log N! ≤ N log N`. -/
theorem log_factorial_le (N : ℕ) : Real.log (Nat.factorial N : ℕ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h : (Nat.factorial N : ℝ) ≤ (N : ℝ) ^ N := by exact_mod_cast Nat.factorial_le_pow N
  have hpos : (0 : ℝ) < (Nat.factorial N : ℝ) := by exact_mod_cast Nat.factorial_pos N
  calc Real.log (Nat.factorial N : ℕ) ≤ Real.log ((N : ℝ) ^ N) := Real.log_le_log hpos h
    _ = N * Real.log N := Real.log_pow N _

/-- `N log N − N ≤ log N!`. -/
theorem log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (Nat.factorial N : ℕ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < (Nat.factorial N : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have h := Real.pow_div_factorial_le_exp (x := (N : ℝ)) hN0.le N
  have h2 : Real.log ((N : ℝ) ^ N / (Nat.factorial N : ℝ)) ≤ N := by
    calc Real.log ((N : ℝ) ^ N / (Nat.factorial N : ℝ)) ≤ Real.log (Real.exp N) :=
          Real.log_le_log (by positivity) h
      _ = N := Real.log_exp _
  rw [Real.log_div (by positivity) hpos.ne', Real.log_pow] at h2
  linarith

/-- The fractional part `{N/d}` as `N/d − ⌊N/d⌋`. -/
private noncomputable def frac (N d : ℕ) : ℝ := (N : ℝ) / d - ((N / d : ℕ) : ℝ)

private theorem frac_nonneg (N d : ℕ) : 0 ≤ frac N d := by
  unfold frac
  have h := Nat.floor_le (show (0 : ℝ) ≤ (N : ℝ) / d by positivity)
  rw [Nat.floor_div_eq_div] at h
  linarith

private theorem frac_le_one (N d : ℕ) : frac N d ≤ 1 := by
  unfold frac
  have h := Nat.lt_floor_add_one ((N : ℝ) / d)
  rw [Nat.floor_div_eq_div] at h
  linarith

/-- `N · Σ Λ(d)/d = log N! + Σ Λ(d) {N/d}`. -/
private theorem mul_sum_eq (N : ℕ) :
    (N : ℝ) * ∑ d ∈ Ioc 0 N, Λ d / d =
      Real.log (Nat.factorial N : ℕ) + ∑ d ∈ Ioc 0 N, Λ d * frac N d := by
  rw [log_factorial_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : (d : ℝ) ≠ 0 := by
    have : 0 < d := (mem_Ioc.mp hd).1
    exact_mod_cast this.ne'
  unfold frac
  field_simp
  ring

private theorem sum_frac_nonneg (N : ℕ) : 0 ≤ ∑ d ∈ Ioc 0 N, Λ d * frac N d :=
  Finset.sum_nonneg fun d _ => mul_nonneg vonMangoldt_nonneg (frac_nonneg N d)

private theorem sum_frac_le_psi (N : ℕ) : ∑ d ∈ Ioc 0 N, Λ d * frac N d ≤ ψ N := by
  unfold Chebyshev.psi
  rw [Nat.floor_natCast]
  exact Finset.sum_le_sum fun d _ => by
    have := frac_le_one N d
    have h0 : 0 ≤ Λ d := vonMangoldt_nonneg
    nlinarith

/-- **Mertens' first theorem**, explicit: for every `N ≥ 1`,
`log N − 1 ≤ Σ_{n ≤ N} Λ(n)/n ≤ log N + log 4 + 4`. -/
theorem mertens_first (N : ℕ) (hN : 1 ≤ N) :
    Real.log N - 1 ≤ ∑ d ∈ Ioc 0 N, Λ d / d ∧
      ∑ d ∈ Ioc 0 N, Λ d / d ≤ Real.log N + (Real.log 4 + 4) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have key := mul_sum_eq N
  have hF0 := sum_frac_nonneg N
  have hF1 := sum_frac_le_psi N
  have hpsi := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) hN0.le
  have hlo := log_factorial_ge N
  have hhi := log_factorial_le N
  set S := ∑ d ∈ Ioc 0 N, Λ d / d
  constructor
  · by_contra h
    have h' := not_le.mp h
    nlinarith [mul_lt_mul_of_pos_left h' hN0]
  · by_contra h
    have h' := not_le.mp h
    nlinarith [mul_lt_mul_of_pos_left h' hN0]

/-- `Σ_{n ≤ N} Λ(n)/n` is unbounded. -/
theorem sum_vonMangoldt_div_unbounded (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ B < ∑ d ∈ Ioc 0 N, Λ d / d := by
  refine ⟨⌈Real.exp (|B| + 2)⌉₊, ?_, ?_⟩
  · have : (1 : ℝ) ≤ Real.exp (|B| + 2) := Real.one_le_exp (by positivity)
    exact (Nat.one_le_iff_ne_zero.mpr (by
      intro h; have := Nat.ceil_eq_zero.mp h; linarith [Real.exp_pos (|B| + 2)]))
  · set N := ⌈Real.exp (|B| + 2)⌉₊ with hNdef
    have hge : Real.exp (|B| + 2) ≤ N := Nat.le_ceil _
    have hN1 : 1 ≤ N := by
      have : (1 : ℝ) ≤ Real.exp (|B| + 2) := Real.one_le_exp (by positivity)
      have h1 : (1 : ℝ) ≤ N := this.trans hge
      exact_mod_cast h1
    have hlog : |B| + 2 ≤ Real.log N := by
      rw [← Real.log_exp (|B| + 2)]
      exact Real.log_le_log (Real.exp_pos _) hge
    have := (mertens_first N hN1).1
    have hB := le_abs_self B
    linarith


end Mertens
