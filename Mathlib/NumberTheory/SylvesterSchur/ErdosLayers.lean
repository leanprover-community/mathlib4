/-
Copyright (c) 2026 Meta Platforms, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
module

public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.NumberTheory.SylvesterSchur.ChooseFactorization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Erdős layer products for Sylvester-Schur

This file packages the Erdős layer-product estimates and the elementary
large-`n` inequalities used by the residual cases.
-/

@[expose] public section

namespace Nat.SylvesterSchur

open scoped BigOperators

open Finset Nat

/-! ### Erdős layer products -/

/- Scaling monotonicity for descending factorials.  Termwise,
`N * (M - i) ≤ M * (N - i)` whenever `i ≤ M ≤ N`; multiplying over `i < r`
gives the comparison used to lift lower bounds from `Nat.choose M r` to
`Nat.choose N r`. -/
private lemma pow_mul_descFactorial_le_pow_mul_descFactorial {M N r : ℕ}
    (hrM : r ≤ M) (hMN : M ≤ N) :
    N ^ r * M.descFactorial r ≤ M ^ r * N.descFactorial r := by
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
  calc
    N ^ r * ∏ i ∈ Finset.range r, (M - i)
        = (∏ _i ∈ Finset.range r, N) * ∏ i ∈ Finset.range r, (M - i) := by
          simp
    _ = ∏ i ∈ Finset.range r, (N * (M - i)) := by
          rw [Finset.prod_mul_distrib]
    _ ≤ ∏ i ∈ Finset.range r, (M * (N - i)) := by
          apply Finset.prod_le_prod'
          intro i hi
          have hir : i < r := Finset.mem_range.mp hi
          have hiM : i ≤ M := by omega
          let d := N - M
          have hN : N = M + d := by
            dsimp [d]
            omega
          have hNsub : N - i = (M - i) + d := by
            dsimp [d]
            omega
          rw [hNsub, hN]
          have hsub : M - i ≤ M := Nat.sub_le M i
          nlinarith
    _ = (∏ _i ∈ Finset.range r, M) * ∏ i ∈ Finset.range r, (N - i) := by
          rw [Finset.prod_mul_distrib]
    _ = M ^ r * ∏ i ∈ Finset.range r, (N - i) := by
          simp

/-- Scaled monotonicity for binomial coefficients:
`N^r * (M choose r) ≤ M^r * (N choose r)` for `r ≤ M ≤ N`.

Equivalently, `(Nat.choose N r : ℚ) / N^r` is monotone decreasing in this range.
This form stays in `ℕ`, avoiding division. -/
theorem pow_mul_choose_le_pow_mul_choose {M N r : ℕ}
    (hrM : r ≤ M) (hMN : M ≤ N) :
    N ^ r * Nat.choose M r ≤ M ^ r * Nat.choose N r := by
  have hdesc :=
    pow_mul_descFactorial_le_pow_mul_descFactorial (M := M) (N := N) (r := r)
      hrM hMN
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at hdesc
  have hmul :
      r ! * (N ^ r * Nat.choose M r) ≤ r ! * (M ^ r * Nat.choose N r) := by
    calc
      r ! * (N ^ r * Nat.choose M r) = N ^ r * (r ! * Nat.choose M r) := by
        ring
      _ ≤ M ^ r * (r ! * Nat.choose N r) := hdesc
      _ = r ! * (M ^ r * Nat.choose N r) := by
        ring
  exact Nat.le_of_mul_le_mul_left hmul (Nat.factorial_pos r)

/- Contrapositive of the central-range Erdős layer bound. -/
private lemma exists_large_prime_dvd_choose_of_prod_erdos_central_layers_lt_choose {N r : ℕ}
    (hN : 0 < N) (hrN : r ≤ N) (h2rN : 2 * r ≤ N) (hNlt3r : N < 3 * r)
    (hN6 : 6 ≤ N)
    (hbound :
      (∏ j ∈ Finset.range (Nat.log 2 N),
          if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N)) <
        Nat.choose N r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le
  intro hsmall
  exact (not_lt_of_ge
    (choose_le_prod_erdos_central_layers_of_no_large hN hrN h2rN hNlt3r hN6 hsmall))
    hbound

/- Contrapositive of the `N / 3` first-layer Erdős bound. -/
private lemma exists_large_prime_dvd_choose_of_prod_erdos_div_three_layers_lt_choose {N r : ℕ}
    (hN : 0 < N) (hrN : r ≤ N) (h2rN : 2 * r ≤ N) (hN6 : 6 ≤ N)
    (hbound :
      (∏ j ∈ Finset.range (Nat.log 2 N),
          if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N)) <
        Nat.choose N r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le
  intro hsmall
  exact (not_lt_of_ge
    (choose_le_prod_erdos_div_three_layers_of_no_large hN hrN h2rN hN6 hsmall))
    hbound

/- Rational lower-bound formulation using the central-range Erdős layer bound. -/
private lemma exists_large_prime_dvd_choose_of_prod_erdos_central_layers_lt_lower_bound
    {N r : ℕ} (hN : 0 < N) (hrN : r ≤ N) (h2rN : 2 * r ≤ N)
    (hNlt3r : N < 3 * r) (hN6 : 6 ≤ N)
    (hbound :
      (((∏ j ∈ Finset.range (Nat.log 2 N),
          if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N) : ℕ) : ℚ) <
        ((N + 1 - r : ℕ) ^ r : ℚ) / (r ! : ℚ))) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  exact exists_large_prime_dvd_choose_of_upper_lt_lower
    (fun hsmall =>
      choose_le_prod_erdos_central_layers_of_no_large hN hrN h2rN hNlt3r hN6 hsmall)
    hbound

/- Rational lower-bound formulation using the `N / 3` first-layer Erdős bound. -/
private lemma exists_large_prime_dvd_choose_of_prod_erdos_div_three_layers_lt_lower_bound
    {N r : ℕ} (hN : 0 < N) (hrN : r ≤ N) (h2rN : 2 * r ≤ N) (hN6 : 6 ≤ N)
    (hbound :
      (((∏ j ∈ Finset.range (Nat.log 2 N),
          if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N) : ℕ) :
          ℚ) <
        ((N + 1 - r : ℕ) ^ r : ℚ) / (r ! : ℚ))) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  exact exists_large_prime_dvd_choose_of_upper_lt_lower
    (fun hsmall => choose_le_prod_erdos_div_three_layers_of_no_large hN hrN h2rN hN6 hsmall)
    hbound

/-- Natural-number version of
`exists_large_prime_dvd_choose_of_prod_erdos_central_layers_lt_lower_bound`. -/
theorem exists_large_prime_dvd_choose_of_factorial_mul_prod_erdos_central_layers_lt_lower_pow
    {N r : ℕ} (hN : 0 < N) (hrN : r ≤ N) (h2rN : 2 * r ≤ N)
    (hNlt3r : N < 3 * r) (hN6 : 6 ≤ N)
    (hbound :
      r ! * (∏ j ∈ Finset.range (Nat.log 2 N),
          if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N)) <
        (N + 1 - r) ^ r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_prod_erdos_central_layers_lt_lower_bound
    hN hrN h2rN hNlt3r hN6
  rw [lt_div_iff₀' (by exact_mod_cast Nat.factorial_pos r)]
  norm_cast

/-- Natural-number version of
`exists_large_prime_dvd_choose_of_prod_erdos_div_three_layers_lt_lower_bound`. -/
theorem exists_large_prime_dvd_choose_of_factorial_mul_prod_erdos_div_three_layers_lt_lower_pow
    {N r : ℕ} (hN : 0 < N) (hrN : r ≤ N) (h2rN : 2 * r ≤ N) (hN6 : 6 ≤ N)
    (hbound :
      r ! * (∏ j ∈ Finset.range (Nat.log 2 N),
          if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N)) <
        (N + 1 - r) ^ r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_prod_erdos_div_three_layers_lt_lower_bound
    hN hrN h2rN hN6
  rw [lt_div_iff₀' (by exact_mod_cast Nat.factorial_pos r)]
  norm_cast

/-- Near the central range, the central-binomial lower bound turns the central Erdős layer
estimate into a large-prime criterion. -/
theorem exists_large_prime_dvd_choose_of_mul_prod_erdos_central_layers_lt_four_pow
    {N r : ℕ} (hr : 4 ≤ r) (h2rN : 2 * r ≤ N) (hNlt3r : N < 3 * r)
    (hN6 : 6 ≤ N)
    (hbound :
      r * (∏ j ∈ Finset.range (Nat.log 2 N),
          if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N)) <
        4 ^ r) :
    ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
  apply exists_large_prime_dvd_choose_of_prod_erdos_central_layers_lt_choose
  · omega
  · omega
  · exact h2rN
  · exact hNlt3r
  · exact hN6
  have hcentral_le : Nat.centralBinom r ≤ Nat.choose N r := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    exact Nat.choose_le_choose r h2rN
  have hlower : 4 ^ r < r * Nat.choose N r := by
    exact (Nat.four_pow_lt_mul_centralBinom r hr).trans_le
      (Nat.mul_le_mul_left r hcentral_le)
  by_contra hnot
  push Not at hnot
  have hmul :
      r * Nat.choose N r ≤
        r * (∏ j ∈ Finset.range (Nat.log 2 N),
          if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N)) :=
    Nat.mul_le_mul_left r hnot
  exact (not_lt_of_ge hbound.le) (hlower.trans_le hmul)

end Nat.SylvesterSchur
