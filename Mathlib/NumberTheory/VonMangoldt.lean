/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module number_theory.von_mangoldt
! leanprover-community/mathlib commit c946d6097a6925ad16d7ec55677bbc977f9846de
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.IsPrimePow
import Mathbin.NumberTheory.ArithmeticFunction
import Mathbin.Analysis.SpecialFunctions.Log.Basic

/-!
# The von Mangoldt Function

In this file we define the von Mangoldt function: the function on natural numbers that returns
`log p` if the input can be expressed as `p^k` for a prime `p`.

## Main Results

The main definition for this file is

- `nat.arithmetic_function.von_mangoldt`: The von Mangoldt function `Λ`.

We then prove the classical summation property of the von Mangoldt function in
`nat.arithmetic_function.von_mangoldt_sum`, that `∑ i in n.divisors, Λ i = real.log n`, and use this
to deduce alternative expressions for the von Mangoldt function via Möbius inversion, see
`nat.arithmetic_function.sum_moebius_mul_log_eq`.

## Notation

We use the standard notation `Λ` to represent the von Mangoldt function.

-/


namespace Nat

namespace ArithmeticFunction

open Finset

open scoped ArithmeticFunction

/-- `log` as an arithmetic function `ℕ → ℝ`. Note this is in the `nat.arithmetic_function`
namespace to indicate that it is bundled as an `arithmetic_function` rather than being the usual
real logarithm. -/
noncomputable def log : ArithmeticFunction ℝ :=
  ⟨fun n => Real.log n, by simp⟩
#align nat.arithmetic_function.log Nat.ArithmeticFunction.log

@[simp]
theorem log_apply {n : ℕ} : log n = Real.log n :=
  rfl
#align nat.arithmetic_function.log_apply Nat.ArithmeticFunction.log_apply

/--
The `von_mangoldt` function is the function on natural numbers that returns `log p` if the input can
be expressed as `p^k` for a prime `p`.
In the case when `n` is a prime power, `min_fac` will give the appropriate prime, as it is the
smallest prime factor.

In the `arithmetic_function` locale, we have the notation `Λ` for this function.
-/
noncomputable def vonMangoldt : ArithmeticFunction ℝ :=
  ⟨fun n => if IsPrimePow n then Real.log (minFac n) else 0, if_neg not_isPrimePow_zero⟩
#align nat.arithmetic_function.von_mangoldt Nat.ArithmeticFunction.vonMangoldt

-- mathport name: von_mangoldt
scoped[ArithmeticFunction] notation "Λ" => Nat.ArithmeticFunction.vonMangoldt

theorem vonMangoldt_apply {n : ℕ} : Λ n = if IsPrimePow n then Real.log (minFac n) else 0 :=
  rfl
#align nat.arithmetic_function.von_mangoldt_apply Nat.ArithmeticFunction.vonMangoldt_apply

@[simp]
theorem vonMangoldt_apply_one : Λ 1 = 0 := by simp [von_mangoldt_apply]
#align nat.arithmetic_function.von_mangoldt_apply_one Nat.ArithmeticFunction.vonMangoldt_apply_one

@[simp]
theorem vonMangoldt_nonneg {n : ℕ} : 0 ≤ Λ n :=
  by
  rw [von_mangoldt_apply]
  split_ifs
  · exact Real.log_nonneg (one_le_cast.2 (Nat.minFac_pos n))
  rfl
#align nat.arithmetic_function.von_mangoldt_nonneg Nat.ArithmeticFunction.vonMangoldt_nonneg

theorem vonMangoldt_apply_pow {n k : ℕ} (hk : k ≠ 0) : Λ (n ^ k) = Λ n := by
  simp only [von_mangoldt_apply, isPrimePow_pow_iff hk, pow_min_fac hk]
#align nat.arithmetic_function.von_mangoldt_apply_pow Nat.ArithmeticFunction.vonMangoldt_apply_pow

theorem vonMangoldt_apply_prime {p : ℕ} (hp : p.Prime) : Λ p = Real.log p := by
  rw [von_mangoldt_apply, prime.min_fac_eq hp, if_pos hp.prime.is_prime_pow]
#align nat.arithmetic_function.von_mangoldt_apply_prime Nat.ArithmeticFunction.vonMangoldt_apply_prime

theorem vonMangoldt_ne_zero_iff {n : ℕ} : Λ n ≠ 0 ↔ IsPrimePow n :=
  by
  rcases eq_or_ne n 1 with (rfl | hn); · simp [not_isPrimePow_one]
  exact (Real.log_pos (one_lt_cast.2 (min_fac_prime hn).one_lt)).ne'.ite_ne_right_iff
#align nat.arithmetic_function.von_mangoldt_ne_zero_iff Nat.ArithmeticFunction.vonMangoldt_ne_zero_iff

theorem vonMangoldt_pos_iff {n : ℕ} : 0 < Λ n ↔ IsPrimePow n :=
  vonMangoldt_nonneg.lt_iff_ne.trans (ne_comm.trans vonMangoldt_ne_zero_iff)
#align nat.arithmetic_function.von_mangoldt_pos_iff Nat.ArithmeticFunction.vonMangoldt_pos_iff

theorem vonMangoldt_eq_zero_iff {n : ℕ} : Λ n = 0 ↔ ¬IsPrimePow n :=
  vonMangoldt_ne_zero_iff.not_right
#align nat.arithmetic_function.von_mangoldt_eq_zero_iff Nat.ArithmeticFunction.vonMangoldt_eq_zero_iff

open scoped BigOperators

theorem vonMangoldt_sum {n : ℕ} : (∑ i in n.divisors, Λ i) = Real.log n :=
  by
  refine' rec_on_prime_coprime _ _ _ n
  · simp
  · intro p k hp
    rw [sum_divisors_prime_pow hp, cast_pow, Real.log_pow, Finset.sum_range_succ', pow_zero,
      von_mangoldt_apply_one]
    simp [von_mangoldt_apply_pow (Nat.succ_ne_zero _), von_mangoldt_apply_prime hp]
  intro a b ha' hb' hab ha hb
  simp only [von_mangoldt_apply, ← sum_filter] at ha hb⊢
  rw [mul_divisors_filter_prime_pow hab, filter_union,
    sum_union (disjoint_divisors_filter_prime_pow hab), ha, hb, Nat.cast_mul,
    Real.log_mul (cast_ne_zero.2 (pos_of_gt ha').ne') (cast_ne_zero.2 (pos_of_gt hb').ne')]
#align nat.arithmetic_function.von_mangoldt_sum Nat.ArithmeticFunction.vonMangoldt_sum

@[simp]
theorem vonMangoldt_mul_zeta : Λ * ζ = log := by ext n; rw [coe_mul_zeta_apply, von_mangoldt_sum];
  rfl
#align nat.arithmetic_function.von_mangoldt_mul_zeta Nat.ArithmeticFunction.vonMangoldt_mul_zeta

@[simp]
theorem zeta_mul_vonMangoldt : (ζ : ArithmeticFunction ℝ) * Λ = log := by rw [mul_comm]; simp
#align nat.arithmetic_function.zeta_mul_von_mangoldt Nat.ArithmeticFunction.zeta_mul_vonMangoldt

@[simp]
theorem log_mul_moebius_eq_vonMangoldt : log * μ = Λ := by
  rw [← von_mangoldt_mul_zeta, mul_assoc, coe_zeta_mul_coe_moebius, mul_one]
#align nat.arithmetic_function.log_mul_moebius_eq_von_mangoldt Nat.ArithmeticFunction.log_mul_moebius_eq_vonMangoldt

@[simp]
theorem moebius_mul_log_eq_vonMangoldt : (μ : ArithmeticFunction ℝ) * log = Λ := by rw [mul_comm];
  simp
#align nat.arithmetic_function.moebius_mul_log_eq_von_mangoldt Nat.ArithmeticFunction.moebius_mul_log_eq_vonMangoldt

theorem sum_moebius_mul_log_eq {n : ℕ} : (∑ d in n.divisors, (μ d : ℝ) * log d) = -Λ n :=
  by
  simp only [← log_mul_moebius_eq_von_mangoldt, mul_comm log, mul_apply, log_apply, int_coe_apply, ←
    Finset.sum_neg_distrib, neg_mul_eq_mul_neg]
  rw [sum_divisors_antidiagonal fun i j => (μ i : ℝ) * -Real.log j]
  have :
    (∑ i : ℕ in n.divisors, (μ i : ℝ) * -Real.log (n / i : ℕ)) =
      ∑ i : ℕ in n.divisors, (μ i : ℝ) * Real.log i - μ i * Real.log n :=
    by
    apply sum_congr rfl
    simp only [and_imp, Int.cast_eq_zero, mul_eq_mul_left_iff, Ne.def, neg_inj, mem_divisors]
    intro m mn hn
    have : (m : ℝ) ≠ 0 := by
      rw [cast_ne_zero]
      rintro rfl
      exact hn (by simpa using mn)
    rw [Nat.cast_div mn this, Real.log_div (cast_ne_zero.2 hn) this, neg_sub, mul_sub]
  rw [this, sum_sub_distrib, ← sum_mul, ← Int.cast_sum, ← coe_mul_zeta_apply, eq_comm, sub_eq_self,
    moebius_mul_coe_zeta, mul_eq_zero, Int.cast_eq_zero]
  rcases eq_or_ne n 1 with (hn | hn) <;> simp [hn]
#align nat.arithmetic_function.sum_moebius_mul_log_eq Nat.ArithmeticFunction.sum_moebius_mul_log_eq

theorem vonMangoldt_le_log : ∀ {n : ℕ}, Λ n ≤ Real.log (n : ℝ)
  | 0 => by simp
  | n + 1 => by
    rw [← von_mangoldt_sum]
    exact single_le_sum (fun _ _ => von_mangoldt_nonneg) (mem_divisors_self _ n.succ_ne_zero)
#align nat.arithmetic_function.von_mangoldt_le_log Nat.ArithmeticFunction.vonMangoldt_le_log

end ArithmeticFunction

end Nat

