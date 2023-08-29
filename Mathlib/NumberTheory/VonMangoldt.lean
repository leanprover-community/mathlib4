/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.IsPrimePow
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.SpecialFunctions.Log.Basic

#align_import number_theory.von_mangoldt from "leanprover-community/mathlib"@"c946d6097a6925ad16d7ec55677bbc977f9846de"

/-!
# The von Mangoldt Function

In this file we define the von Mangoldt function: the function on natural numbers that returns
`log p` if the input can be expressed as `p^k` for a prime `p`.

## Main Results

The main definition for this file is

- `Nat.ArithmeticFunction.vonMangoldt`: The von Mangoldt function `Λ`.

We then prove the classical summation property of the von Mangoldt function in
`Nat.ArithmeticFunction.vonMangoldt_sum`, that `∑ i in n.divisors, Λ i = Real.log n`, and use this
to deduce alternative expressions for the von Mangoldt function via Möbius inversion, see
`Nat.ArithmeticFunction.sum_moebius_mul_log_eq`.

## Notation

We use the standard notation `Λ` to represent the von Mangoldt function.

-/


namespace Nat

namespace ArithmeticFunction

open Finset

open scoped ArithmeticFunction

/-- `log` as an arithmetic function `ℕ → ℝ`. Note this is in the `Nat.ArithmeticFunction`
namespace to indicate that it is bundled as an `ArithmeticFunction` rather than being the usual
real logarithm. -/
noncomputable def log : ArithmeticFunction ℝ :=
  ⟨fun n => Real.log n, by simp⟩
                           -- 🎉 no goals
#align nat.arithmetic_function.log Nat.ArithmeticFunction.log

@[simp]
theorem log_apply {n : ℕ} : log n = Real.log n :=
  rfl
#align nat.arithmetic_function.log_apply Nat.ArithmeticFunction.log_apply

/--
The `vonMangoldt` function is the function on natural numbers that returns `log p` if the input can
be expressed as `p^k` for a prime `p`.
In the case when `n` is a prime power, `min_fac` will give the appropriate prime, as it is the
smallest prime factor.

In the `ArithmeticFunction` locale, we have the notation `Λ` for this function.
-/
noncomputable def vonMangoldt : ArithmeticFunction ℝ :=
  ⟨fun n => if IsPrimePow n then Real.log (minFac n) else 0, if_neg not_isPrimePow_zero⟩
#align nat.arithmetic_function.von_mangoldt Nat.ArithmeticFunction.vonMangoldt

scoped[Nat.ArithmeticFunction] notation "Λ" => Nat.ArithmeticFunction.vonMangoldt

theorem vonMangoldt_apply {n : ℕ} : Λ n = if IsPrimePow n then Real.log (minFac n) else 0 :=
  rfl
#align nat.arithmetic_function.von_mangoldt_apply Nat.ArithmeticFunction.vonMangoldt_apply

@[simp]
theorem vonMangoldt_apply_one : Λ 1 = 0 := by simp [vonMangoldt_apply]
                                              -- 🎉 no goals
#align nat.arithmetic_function.von_mangoldt_apply_one Nat.ArithmeticFunction.vonMangoldt_apply_one

@[simp]
theorem vonMangoldt_nonneg {n : ℕ} : 0 ≤ Λ n := by
  rw [vonMangoldt_apply]
  -- ⊢ 0 ≤ if IsPrimePow n then Real.log ↑(minFac n) else 0
  split_ifs
  -- ⊢ 0 ≤ Real.log ↑(minFac n)
  · exact Real.log_nonneg (one_le_cast.2 (Nat.minFac_pos n))
    -- 🎉 no goals
  rfl
  -- 🎉 no goals
#align nat.arithmetic_function.von_mangoldt_nonneg Nat.ArithmeticFunction.vonMangoldt_nonneg

theorem vonMangoldt_apply_pow {n k : ℕ} (hk : k ≠ 0) : Λ (n ^ k) = Λ n := by
  simp only [vonMangoldt_apply, isPrimePow_pow_iff hk, pow_minFac hk]
  -- 🎉 no goals
#align nat.arithmetic_function.von_mangoldt_apply_pow Nat.ArithmeticFunction.vonMangoldt_apply_pow

theorem vonMangoldt_apply_prime {p : ℕ} (hp : p.Prime) : Λ p = Real.log p := by
  rw [vonMangoldt_apply, Prime.minFac_eq hp, if_pos hp.prime.isPrimePow]
  -- 🎉 no goals
#align nat.arithmetic_function.von_mangoldt_apply_prime Nat.ArithmeticFunction.vonMangoldt_apply_prime

theorem vonMangoldt_ne_zero_iff {n : ℕ} : Λ n ≠ 0 ↔ IsPrimePow n := by
  rcases eq_or_ne n 1 with (rfl | hn); · simp [not_isPrimePow_one]
  -- ⊢ ↑Λ 1 ≠ 0 ↔ IsPrimePow 1
                                         -- 🎉 no goals
  exact (Real.log_pos (one_lt_cast.2 (minFac_prime hn).one_lt)).ne'.ite_ne_right_iff
  -- 🎉 no goals
#align nat.arithmetic_function.von_mangoldt_ne_zero_iff Nat.ArithmeticFunction.vonMangoldt_ne_zero_iff

theorem vonMangoldt_pos_iff {n : ℕ} : 0 < Λ n ↔ IsPrimePow n :=
  vonMangoldt_nonneg.lt_iff_ne.trans (ne_comm.trans vonMangoldt_ne_zero_iff)
#align nat.arithmetic_function.von_mangoldt_pos_iff Nat.ArithmeticFunction.vonMangoldt_pos_iff

theorem vonMangoldt_eq_zero_iff {n : ℕ} : Λ n = 0 ↔ ¬IsPrimePow n :=
  vonMangoldt_ne_zero_iff.not_right
#align nat.arithmetic_function.von_mangoldt_eq_zero_iff Nat.ArithmeticFunction.vonMangoldt_eq_zero_iff

open scoped BigOperators

theorem vonMangoldt_sum {n : ℕ} : ∑ i in n.divisors, Λ i = Real.log n := by
  refine' recOnPrimeCoprime _ _ _ n
  · simp
    -- 🎉 no goals
  · intro p k hp
    -- ⊢ ∑ i in divisors (p ^ k), ↑Λ i = Real.log ↑(p ^ k)
    rw [sum_divisors_prime_pow hp, cast_pow, Real.log_pow, Finset.sum_range_succ', pow_zero,
      vonMangoldt_apply_one]
    simp [vonMangoldt_apply_pow (Nat.succ_ne_zero _), vonMangoldt_apply_prime hp]
    -- 🎉 no goals
  intro a b ha' hb' hab ha hb
  -- ⊢ ∑ i in divisors (a * b), ↑Λ i = Real.log ↑(a * b)
  simp only [vonMangoldt_apply, ← sum_filter] at ha hb ⊢
  -- ⊢ ∑ a in filter (fun a => IsPrimePow a) (divisors (a * b)), Real.log ↑(minFac  …
  rw [mul_divisors_filter_prime_pow hab, filter_union,
    sum_union (disjoint_divisors_filter_isPrimePow hab), ha, hb, Nat.cast_mul,
    Real.log_mul (cast_ne_zero.2 (pos_of_gt ha').ne') (cast_ne_zero.2 (pos_of_gt hb').ne')]
#align nat.arithmetic_function.von_mangoldt_sum Nat.ArithmeticFunction.vonMangoldt_sum

@[simp]
theorem vonMangoldt_mul_zeta : Λ * ζ = log := by
  ext n; rw [coe_mul_zeta_apply, vonMangoldt_sum]; rfl
  -- ⊢ ↑(Λ * ↑ζ) n = ↑log n
         -- ⊢ Real.log ↑n = ↑log n
                                                   -- 🎉 no goals
#align nat.arithmetic_function.von_mangoldt_mul_zeta Nat.ArithmeticFunction.vonMangoldt_mul_zeta

@[simp]
theorem zeta_mul_vonMangoldt : (ζ : ArithmeticFunction ℝ) * Λ = log := by rw [mul_comm]; simp
                                                                          -- ⊢ Λ * ↑ζ = log
                                                                                         -- 🎉 no goals
#align nat.arithmetic_function.zeta_mul_von_mangoldt Nat.ArithmeticFunction.zeta_mul_vonMangoldt

@[simp]
theorem log_mul_moebius_eq_vonMangoldt : log * μ = Λ := by
  rw [← vonMangoldt_mul_zeta, mul_assoc, coe_zeta_mul_coe_moebius, mul_one]
  -- 🎉 no goals
#align nat.arithmetic_function.log_mul_moebius_eq_von_mangoldt Nat.ArithmeticFunction.log_mul_moebius_eq_vonMangoldt

@[simp]
theorem moebius_mul_log_eq_vonMangoldt : (μ : ArithmeticFunction ℝ) * log = Λ := by
  rw [mul_comm]; simp
  -- ⊢ log * ↑μ = Λ
                 -- 🎉 no goals
#align nat.arithmetic_function.moebius_mul_log_eq_von_mangoldt Nat.ArithmeticFunction.moebius_mul_log_eq_vonMangoldt

theorem sum_moebius_mul_log_eq {n : ℕ} : (∑ d in n.divisors, (μ d : ℝ) * log d) = -Λ n := by
  simp only [← log_mul_moebius_eq_vonMangoldt, mul_comm log, mul_apply, log_apply, intCoe_apply, ←
    Finset.sum_neg_distrib, neg_mul_eq_mul_neg]
  rw [sum_divisorsAntidiagonal fun i j => (μ i : ℝ) * -Real.log j]
  -- ⊢ ∑ x in divisors n, ↑(↑μ x) * Real.log ↑x = ∑ i in divisors n, ↑(↑μ i) * -Rea …
  have : (∑ i : ℕ in n.divisors, (μ i : ℝ) * -Real.log (n / i : ℕ)) =
      ∑ i : ℕ in n.divisors, ((μ i : ℝ) * Real.log i - μ i * Real.log n) := by
    apply sum_congr rfl
    simp only [and_imp, Int.cast_eq_zero, mul_eq_mul_left_iff, Ne.def, neg_inj, mem_divisors]
    intro m mn hn
    have : (m : ℝ) ≠ 0 := by
      rw [cast_ne_zero]
      rintro rfl
      exact hn (by simpa using mn)
    rw [Nat.cast_div mn this, Real.log_div (cast_ne_zero.2 hn) this, neg_sub, mul_sub]
  rw [this, sum_sub_distrib, ← sum_mul, ← Int.cast_sum, ← coe_mul_zeta_apply, eq_comm, sub_eq_self,
    moebius_mul_coe_zeta]
  rcases eq_or_ne n 1 with (hn | hn) <;> simp [hn]
  -- ⊢ ↑(↑1 n) * Real.log ↑n = 0
                                         -- 🎉 no goals
                                         -- 🎉 no goals
#align nat.arithmetic_function.sum_moebius_mul_log_eq Nat.ArithmeticFunction.sum_moebius_mul_log_eq

theorem vonMangoldt_le_log : ∀ {n : ℕ}, Λ n ≤ Real.log (n : ℝ)
  | 0 => by simp
            -- 🎉 no goals
  | n + 1 => by
    rw [← vonMangoldt_sum]
    -- ⊢ ↑Λ (n + 1) ≤ ∑ i in divisors (n + 1), ↑Λ i
    exact single_le_sum (by exact fun _ _ => vonMangoldt_nonneg)
      (mem_divisors_self _ n.succ_ne_zero)
#align nat.arithmetic_function.von_mangoldt_le_log Nat.ArithmeticFunction.vonMangoldt_le_log

end ArithmeticFunction

end Nat
