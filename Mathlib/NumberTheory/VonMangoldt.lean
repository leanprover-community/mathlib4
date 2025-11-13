/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.ArithmeticFunction

/-!
# The von Mangoldt Function

In this file we define the von Mangoldt function: the function on natural numbers that returns
`log p` if the input can be expressed as `p^k` for a prime `p`.

## Main Results

The main definition for this file is

- `ArithmeticFunction.vonMangoldt`: The von Mangoldt function `Λ`.

We then prove the classical summation property of the von Mangoldt function in
`ArithmeticFunction.vonMangoldt_sum`, that `∑ i ∈ n.divisors, Λ i = Real.log n`, and use this
to deduce alternative expressions for the von Mangoldt function via Möbius inversion, see
`ArithmeticFunction.sum_moebius_mul_log_eq`.

## Notation

We use the standard notation `Λ` to represent the von Mangoldt function.
It is accessible in the locales `ArithmeticFunction` (like the notations for other arithmetic
functions) and also in the scope `ArithmeticFunction.vonMangoldt`.

-/

namespace ArithmeticFunction

open Finset Nat

open scoped ArithmeticFunction

/-- `log` as an arithmetic function `ℕ → ℝ`. Note this is in the `ArithmeticFunction`
namespace to indicate that it is bundled as an `ArithmeticFunction` rather than being the usual
real logarithm. -/
noncomputable def log : ArithmeticFunction ℝ :=
  ⟨fun n => Real.log n, by simp⟩

@[simp]
theorem log_apply {n : ℕ} : log n = Real.log n :=
  rfl

/--
The `vonMangoldt` function is the function on natural numbers that returns `log p` if the input can
be expressed as `p^k` for a prime `p`.
In the case when `n` is a prime power, `Nat.minFac` will give the appropriate prime, as it is the
smallest prime factor.

In the `ArithmeticFunction` locale, we have the notation `Λ` for this function.
This is also available in the `ArithmeticFunction.vonMangoldt` locale, allowing for selective
access to the notation.
-/
noncomputable def vonMangoldt : ArithmeticFunction ℝ :=
  ⟨fun n => if IsPrimePow n then Real.log (minFac n) else 0, if_neg not_isPrimePow_zero⟩

@[inherit_doc] scoped[ArithmeticFunction] notation "Λ" => ArithmeticFunction.vonMangoldt

@[inherit_doc] scoped[ArithmeticFunction.vonMangoldt] notation "Λ" =>
  ArithmeticFunction.vonMangoldt

theorem vonMangoldt_apply {n : ℕ} : Λ n = if IsPrimePow n then Real.log (minFac n) else 0 :=
  rfl

@[simp]
theorem vonMangoldt_apply_one : Λ 1 = 0 := by simp [vonMangoldt_apply]

@[simp]
theorem vonMangoldt_nonneg {n : ℕ} : 0 ≤ Λ n := by
  rw [vonMangoldt_apply]
  split_ifs
  · exact Real.log_nonneg (one_le_cast.2 (Nat.minFac_pos n))
  rfl

theorem vonMangoldt_apply_pow {n k : ℕ} (hk : k ≠ 0) : Λ (n ^ k) = Λ n := by
  simp only [vonMangoldt_apply, isPrimePow_pow_iff hk, pow_minFac hk]

theorem vonMangoldt_apply_prime {p : ℕ} (hp : p.Prime) : Λ p = Real.log p := by
  rw [vonMangoldt_apply, Prime.minFac_eq hp, if_pos hp.prime.isPrimePow]

theorem vonMangoldt_ne_zero_iff {n : ℕ} : Λ n ≠ 0 ↔ IsPrimePow n := by
  rcases eq_or_ne n 1 with (rfl | hn); · simp [not_isPrimePow_one]
  exact (Real.log_pos (one_lt_cast.2 (minFac_prime hn).one_lt)).ne'.ite_ne_right_iff

theorem vonMangoldt_pos_iff {n : ℕ} : 0 < Λ n ↔ IsPrimePow n :=
  vonMangoldt_nonneg.lt_iff_ne.trans (ne_comm.trans vonMangoldt_ne_zero_iff)

theorem vonMangoldt_eq_zero_iff {n : ℕ} : Λ n = 0 ↔ ¬IsPrimePow n :=
  vonMangoldt_ne_zero_iff.not_right

theorem vonMangoldt_sum {n : ℕ} : ∑ i ∈ n.divisors, Λ i = Real.log n := by
  refine recOnPrimeCoprime ?_ ?_ ?_ n
  · simp
  · intro p k hp
    rw [sum_divisors_prime_pow hp, cast_pow, Real.log_pow, Finset.sum_range_succ', Nat.pow_zero,
      vonMangoldt_apply_one]
    simp [vonMangoldt_apply_pow (Nat.succ_ne_zero _), vonMangoldt_apply_prime hp]
  intro a b ha' hb' hab ha hb
  simp only [vonMangoldt_apply, ← sum_filter] at ha hb ⊢
  rw [mul_divisors_filter_prime_pow hab, filter_union,
    sum_union (disjoint_divisors_filter_isPrimePow hab), ha, hb, Nat.cast_mul,
    Real.log_mul (cast_ne_zero.2 (pos_of_gt ha').ne') (cast_ne_zero.2 (pos_of_gt hb').ne')]

-- access notation `ζ` and `μ`
open scoped zeta Moebius

@[simp]
theorem vonMangoldt_mul_zeta : Λ * ζ = log := by
  ext n; rw [coe_mul_zeta_apply, vonMangoldt_sum]; rfl

@[simp]
theorem zeta_mul_vonMangoldt : (ζ : ArithmeticFunction ℝ) * Λ = log := by rw [mul_comm]; simp

@[simp]
theorem log_mul_moebius_eq_vonMangoldt : log * μ = Λ := by
  rw [← vonMangoldt_mul_zeta, mul_assoc, coe_zeta_mul_coe_moebius, mul_one]

@[simp]
theorem moebius_mul_log_eq_vonMangoldt : (μ : ArithmeticFunction ℝ) * log = Λ := by
  rw [mul_comm]; simp

theorem sum_moebius_mul_log_eq {n : ℕ} : (∑ d ∈ n.divisors, (μ d : ℝ) * log d) = -Λ n := by
  simp only [← log_mul_moebius_eq_vonMangoldt, mul_comm log, mul_apply, log_apply, intCoe_apply, ←
    Finset.sum_neg_distrib, neg_mul_eq_mul_neg]
  rw [sum_divisorsAntidiagonal fun i j => (μ i : ℝ) * -Real.log j]
  have : (∑ i ∈ n.divisors, (μ i : ℝ) * -Real.log (n / i : ℕ)) =
      ∑ i ∈ n.divisors, ((μ i : ℝ) * Real.log i - μ i * Real.log n) := by
    apply sum_congr rfl
    simp only [and_imp, Ne, mem_divisors]
    intro m mn hn
    have : (m : ℝ) ≠ 0 := by
      rw [cast_ne_zero]
      rintro rfl
      exact hn (by simpa using mn)
    rw [Nat.cast_div mn this, Real.log_div (cast_ne_zero.2 hn) this, neg_sub, mul_sub]
  rw [this, sum_sub_distrib, ← sum_mul, ← Int.cast_sum, ← coe_mul_zeta_apply, eq_comm, sub_eq_self,
    moebius_mul_coe_zeta]
  rcases eq_or_ne n 1 with (hn | hn) <;> simp [hn]

theorem vonMangoldt_le_log : ∀ {n : ℕ}, Λ n ≤ Real.log (n : ℝ)
  | 0 => by simp
  | n + 1 => by
    rw [← vonMangoldt_sum]
    exact single_le_sum (by exact fun _ _ => vonMangoldt_nonneg)
      (mem_divisors_self _ n.succ_ne_zero)

end ArithmeticFunction
