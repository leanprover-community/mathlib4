/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Pietro Monticone, Robby Sneiderman, Guiseppe Sorge, Terence Tao,
Yan Yablonovskiy, Yi Yuan
-/
module

public import Mathlib.NumberTheory.Mertens.Construction
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
# Mertens' theorems

This file proves Mertens' first and second theorems for the von Mangoldt and prime weights,
as concrete statements about sums over integers and primes.

-/

@[expose] public section

namespace Mertens

open Nat hiding log log_pos
open Finset Filter Real Chebyshev intervalIntegral Asymptotics MeasureTheory Topology
  Measurable ContinuousOn
open ArithmeticFunction hiding log
open scoped Nat.Prime

open Weight

section FirstTheorem

/-
## The first Mertens theorem

-/

variable {x : ℝ} (N : ℕ)

theorem le_sum_vonMangoldt_div_sub (hx : 1 ≤ x) : - 2 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x :=
 vonMangoldt.le_first' x hx

/-- A sharper lower bound in the case of natural numbers. -/
theorem le_sum_vonMangoldt_div_sub_nat : - 1 ≤ ∑ n ∈ Ioc 0 N, Λ n / n - log N := by
  by_cases! hN : N = 0
  · simp [hN]
  suffices N * (log N - 1) ≤ N * ∑ n ∈ Ioc 0 ⌊(N : ℝ)⌋₊, Weight.vonMangoldt n by
    simp [vonMangoldtFun] at this
    linarith [le_of_mul_le_mul_left this (by norm_cast; omega)]
  have := le_mul_sum_vonMangoldt (x := N) (by positivity)
  simp only [floor_natCast, vonMangoldtFun] at this ⊢
  grw [← this, ←le_sum_log_nat]
  simp [field]

theorem le_sum_log_prime_div_sub (hx : 1 ≤ x) : - 3 ≤ ∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x :=
  (sum_prime_eq _).symm ▸ prime.le_first' x hx

/-- A sharper lower bound in the case of natural numbers. -/
theorem le_sum_log_prime_div_sub_nat : - 2 ≤ ∑ p ∈ primesLE N, log p / p - log N := by
  by_cases! hN : N = 0
  · simp [hN]
  have := sum_vonMangoldt_le_sum_prime_add_E₁ (mod_cast (by omega) : 1 ≤ (N : ℝ))
  simp at this
  linarith [le_sum_vonMangoldt_div_sub_nat N, E₁_le]

theorem sum_vonMangoldt_div_sub_le (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x ≤ log 4 + 1 :=
  vonMangoldt.first_le' x hx

theorem sum_log_prime_div_sub_le (hx : 1 ≤ x) : ∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x ≤ log 4 :=
  (sum_prime_eq _).symm ▸ prime.first_le' x hx

theorem abs_sum_vonMangoldt_div_sub_le (hx : 1 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x| ≤ log 4 + 1 :=
  vonMangoldt.sum_sub_log_bound hx|>.trans_eq vonMangoldt_C₁_eq

theorem abs_sum_vonMangoldt_div_sub_le_nat : |∑ n ∈ Ioc 0 N, Λ n / n - log N| ≤ log 4 + 1 :=
  vonMangoldt.sum_sub_log_bound_nat N|>.trans_eq vonMangoldt_C₁_eq

theorem abs_sum_log_prime_div_sub_le (hx : 1 ≤ x) : |∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x| ≤ 3 :=
  (sum_prime_eq _).symm ▸ prime.sum_sub_log_bound hx|>.trans_eq prime_C₁_eq

/-- A sharper bound in the case of natural numbers. -/
theorem abs_sum_log_prime_div_sub_le_nat : |∑ p ∈ primesLE N, log p / p - log N| ≤ 2 := by
  by_cases! hN : N = 0
  · simp [hN]
  have : 1 ≤ (N : ℝ) := mod_cast (by omega)
  rw [abs_le']; constructor
  · trans log 4
    · simpa using sum_log_prime_div_sub_le this
    · linarith [log_four_eq, log_two_lt_d9]
  linarith [le_sum_log_prime_div_sub_nat N]

theorem sum_vonMangoldt_div_sub_bounded : (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x)
    =O[atTop] fun _ ↦ (1 : ℝ) := vonMangoldt.sum_sub_log_bounded

theorem sum_vonMangoldt_div_sub_bounded_nat : (fun N ↦ ∑ n ∈ Ioc 0 N, Λ n / n - log N)
    =O[atTop] fun _ ↦ (1 : ℝ) := vonMangoldt.sum_sub_log_bounded_nat

theorem sum_log_prime_div_sub_bounded : (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x)
    =O[atTop] fun _ ↦ (1 : ℝ) := by
  convert prime.sum_sub_log_bounded using 3
  rw [sum_prime_eq]

theorem sum_log_prime_div_sub_bounded_nat : (fun N ↦ ∑ p ∈ primesLE N, log p / p - log N)
    =O[atTop] fun _ ↦ (1 : ℝ) := by
  convert prime.sum_sub_log_bounded_nat using 3
  rw [sum_prime_eq]

theorem sum_vonMangoldt_div_asymp : (∑ n ∈ Ioc 0 ⌊·⌋₊, Λ n / n) ~[atTop] log :=
  vonMangoldt.sum_asymp

theorem sum_vonMangoldt_div_asymp_nat : (∑ n ∈ Ioc 0 ·, Λ n / n) ~[atTop] (log ↑·) :=
  vonMangoldt.sum_asymp_nat

theorem sum_log_prime_div_asymp : (∑ p ∈ primesLE ⌊·⌋₊, log p / p) ~[atTop] log := by
  convert prime.sum_asymp using 2
  rw [sum_prime_eq]

theorem sum_log_prime_div_asymp_nat : (∑ p ∈ primesLE ·, log p / p) ~[atTop] (log ↑·) := by
  convert prime.sum_asymp_nat using 2
  rw [sum_prime_eq]

end FirstTheorem

section SecondTheorem

/-
## The second Mertens theorem
-/

variable {x : ℝ} {N : ℕ}

/-- Rewrites the von Mangoldt weight sum in the form `∑ Λ n / (n * log n)`. -/
private lemma Weight.vonMangoldt_sum_inv_log_mul_eq :
    ∑ n ∈ Ioc 0 N, (log n)⁻¹ * vonMangoldt n = ∑ n ∈ Ioc 0 N, Λ n / (n * log n) := by
  congr! 1; simp [vonMangoldtFun]; field

/-- Rewrites the prime weight sum in the form `∑ 1 / p` over the primes `≤ N`. -/
private lemma Weight.prime_sum_inv_log_mul_eq :
    ∑ n ∈ Ioc 0 N, (log n)⁻¹ * Weight.prime n = ∑ p ∈ primesLE N, 1 / (p : ℝ) := by
  simp only [primeFun, mul_ite, mul_zero, primesLE_eq_filter_Ioc_zero, sum_filter]
  congr! 2 with p _ hp
  have := hp.log_pos
  field_simp (disch := positivity)

theorem sum_vonMangoldt_div_mul_log_sub_sub_bound (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - log (log x) - eulerMascheroniConstant| ≤
      (log 4 + 3) / log x := by
  simpa [← vonMangoldt_sum_inv_log_mul_eq] using vonMangoldt.sum_div_log_sub_sub_bound hx

theorem sum_vonMangoldt_div_mul_log_sub_sub_bound_nat (hN : 2 ≤ N) :
    |∑ n ∈ Ioc 0 N, Λ n / (n * log n) - log (log N) - eulerMascheroniConstant| ≤
      (log 4 + 3) / log N := by
  simpa using sum_vonMangoldt_div_mul_log_sub_sub_bound (x := N) (mod_cast hN)

theorem sum_prime_inv_sub_sub_bound (hx : 2 ≤ x) :
    |∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ) - log (log x) - prime.M| ≤ (log 4 + 3) / log x := by
  simpa only [prime_sum_inv_log_mul_eq, prime_C₂_eq] using prime.sum_div_log_sub_sub_bound hx

theorem sum_prime_inv_sub_sub_bound_nat (hN : 2 ≤ N) :
    |∑ p ∈ primesLE N, 1 / (p : ℝ) - log (log N) - prime.M| ≤ (log 4 + 3) / log N := by
  simpa using sum_prime_inv_sub_sub_bound (x := N) (mod_cast hN)

theorem sum_vonMangoldt_div_mul_log_sub_sub_isBigO :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - log (log x) - eulerMascheroniConstant)
    =O[atTop] fun x ↦ (log x)⁻¹ := by
  simpa [← vonMangoldt_sum_inv_log_mul_eq] using vonMangoldt.sum_div_log_sub_sub_isBigO

theorem sum_vonMangoldt_div_mul_log_sub_sub_isBigO_nat :
    (fun N : ℕ ↦ ∑ n ∈ Ioc 0 N, Λ n / (n * log n) - log (log N) - eulerMascheroniConstant)
    =O[atTop] fun N ↦ (log N)⁻¹ := by
  simpa [← vonMangoldt_sum_inv_log_mul_eq] using Weight.vonMangoldt.sum_div_log_sub_sub_isBigO_nat

theorem sum_prime_div_mul_log_sub_sub_isBigO :
    (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ) - log (log x) - prime.M)
    =O[atTop] fun x ↦ (log x)⁻¹ := by
  simpa only [← prime_sum_inv_log_mul_eq] using prime.sum_div_log_sub_sub_isBigO

theorem sum_prime_div_mul_log_sub_sub_isBigO_nat :
    (fun (N : ℕ) ↦ ∑ p ∈ primesLE N, 1 / (p : ℝ) - log (log N) - prime.M)
    =O[atTop] fun N ↦ (log N)⁻¹ := by
  simpa only [← prime_sum_inv_log_mul_eq] using prime.sum_div_log_sub_sub_isBigO_nat

theorem sum_vonMangoldt_div_mul_log_sub_sub_isLittleO :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - log (log x) - eulerMascheroniConstant)
    =o[atTop] fun _ ↦ (1 : ℝ) := by
  simpa [← vonMangoldt_sum_inv_log_mul_eq] using vonMangoldt.sum_div_log_sub_sub_isLittleO

theorem sum_vonMangoldt_div_mul_log_sub_sub_isLittleO_nat :
    (fun (N : ℕ) ↦ ∑ n ∈ Ioc 0 N, Λ n / (n * log n) - log (log N) - eulerMascheroniConstant)
    =o[atTop] fun _ ↦ (1 : ℝ) := by
  simpa [← vonMangoldt_sum_inv_log_mul_eq] using vonMangoldt.sum_div_log_sub_sub_isLittleO_nat

theorem sum_prime_inv_sub_sub_isLittleO :
    (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ) - log (log x) - prime.M)
    =o[atTop] fun _ ↦ (1 : ℝ) := by
  simpa only [← prime_sum_inv_log_mul_eq] using prime.sum_div_log_sub_sub_isLittleO

theorem sum_prime_inv_sub_sub_isLittleO_nat :
    (fun (N : ℕ) ↦ ∑ p ∈ primesLE N, 1 / (p : ℝ) - log (log N) - prime.M)
    =o[atTop] fun _ ↦ (1 : ℝ) := by
  simpa only [← prime_sum_inv_log_mul_eq] using prime.sum_div_log_sub_sub_isLittleO_nat

theorem sum_vonMangoldt_div_mul_log_sub_isBigO :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - log (log x)) =O[atTop] fun _ ↦ (1 : ℝ) := by
  simpa only [← vonMangoldt_sum_inv_log_mul_eq] using vonMangoldt.sum_div_log_sub_isBigO

theorem sum_vonMangoldt_div_mul_log_sub_isBigO_nat
    : (fun (N : ℕ) ↦ ∑ n ∈ Ioc 0 N, Λ n / (n * log n) - log (log N)) =O[atTop] fun _ ↦ (1 : ℝ)
    := by
  simpa [← vonMangoldt_sum_inv_log_mul_eq] using  vonMangoldt.sum_div_log_sub_isBigO_nat

theorem sum_prime_inv_sub_isBigO :
    (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ) - log (log x)) =O[atTop] fun _ ↦ (1 : ℝ) := by
  simpa only [← prime_sum_inv_log_mul_eq] using prime.sum_div_log_sub_isBigO

theorem sum_prime_inv_sub_isBigO_nat
    : (fun (N : ℕ) ↦ ∑ p ∈ primesLE N, 1 / (p : ℝ) - log (log N)) =O[atTop] fun _ ↦ (1 : ℝ) := by
  simpa only [← prime_sum_inv_log_mul_eq] using prime.sum_div_log_sub_isBigO_nat

theorem sum_vonMangoldt_div_mul_log_asymp :
    (∑ n ∈ Ioc 0 ⌊·⌋₊, Λ n / (n * log n)) ~[atTop] fun x ↦ log (log x) := by
  simpa [← vonMangoldt_sum_inv_log_mul_eq] using vonMangoldt.sum_div_log_asymp

theorem sum_vonMangoldt_div_mul_log_asymp_nat :
    (∑ n ∈ Ioc 0 ·, Λ n / (n * log n)) ~[atTop] fun N ↦ log (log N) := by
  simpa [← vonMangoldt_sum_inv_log_mul_eq] using vonMangoldt.sum_div_log_asymp_nat

theorem sum_prime_inv_asymp :
    (∑ p ∈ primesLE ⌊·⌋₊, 1 / (p : ℝ)) ~[atTop] fun x ↦ log (log x) := by
  simpa only [← prime_sum_inv_log_mul_eq] using prime.sum_div_log_asymp

theorem sum_prime_inv_asymp_nat :
    (∑ p ∈ primesLE ·, 1 / (p : ℝ)) ~[atTop] fun N ↦ log (log N) := by
  simpa only [← prime_sum_inv_log_mul_eq] using prime.sum_div_log_asymp_nat

end SecondTheorem

section ThirdTheorem

/-
## The third Mertens theorem

It will be convenient to express the third Mertens theorem in terms of an error term
`E₃ x = ∑ p ∈ primesLE ⌊x⌋₊, log (1 - 1 / (p : ℝ)) + log (log x) + eulerMascheroniConstant`.
-/

/-- The summand `-(1 / p + log (1 - 1 / p))` of the error term `E₃` is nonnegative. -/
private lemma neg_inv_sub_log_sub_inv_nonneg (p : Primes) : 0 ≤ - (1 / p + log (1 - 1 / p)) := by
  have : 1 < (p : ℝ) := mod_cast p.prop.one_lt
  grw [log_le_sub_one_of_pos] <;> field_simp <;> grind

/-- This summand is bounded by `1 / p ^ 2`, which yields summability of the `E₃` sum. -/
private lemma neg_inv_sub_log_sub_inv_le (p : Primes) : - (1 / p + log (1 - 1 / p))
    ≤ 1 / p ^ 2 := by
  rw [neg_inv_sub_log_sub_inv_eq p]
  have := tsum_inv_mul_pow_le (le_refl _) p
  norm_cast at this
  simpa using this

/-- The error term in Mertens' third theorem. -/
noncomputable def E₃ (x : ℝ) :=
  ∑ p ∈ primesLE ⌊x⌋₊, log (1 - 1 / (p : ℝ)) + log (log x) + eulerMascheroniConstant

theorem sum_prime_log_sub_inv_eq (x : ℝ) : ∑ p ∈ primesLE ⌊x⌋₊, log (1 - 1 / (p : ℝ))
    = - log (log x) - eulerMascheroniConstant + E₃ x := by grind [E₃]

theorem sum_prime_log_sub_inv_eq_nat (N : ℕ) : ∑ p ∈ primesLE N, log (1 - 1 / (p : ℝ))
    = - log (log N) - eulerMascheroniConstant + E₃ N := by
  simpa using sum_prime_log_sub_inv_eq N

theorem prod_prime_one_minus_inv_eq {x : ℝ} (hx : 1 < x) : ∏ p ∈ primesLE ⌊x⌋₊, (1 - (1 : ℝ) / p) =
    exp (-eulerMascheroniConstant) * exp (E₃ x) / log x := by
  have hlog := log_pos hx
  have hpos {p : ℕ} (hp : p.Prime) : (0 : ℝ) < 1 - 1 / p := by
    grind [one_div_le_one_div_of_le two_pos (mod_cast hp.two_le : (2 : ℝ) ≤ p)]
  simp_rw [E₃, exp_add, exp_sum, exp_log hlog, exp_neg]
  field_simp
  exact prod_congr rfl fun p hp ↦ (exp_log (hpos (mem_filter.mp hp).2)).symm

theorem prod_prime_one_minus_inv_eq_nat {N : ℕ} (hN : 1 < N) : ∏ p ∈ primesLE N, (1 - (1 : ℝ) / p)
    = exp (-eulerMascheroniConstant) * exp (E₃ N) / log N := by
  simpa using prod_prime_one_minus_inv_eq (x := N) (mod_cast hN)

/-- A completely explicit upper bound on the error term. -/
theorem E₃_bound {x : ℝ} (hx : 2 ≤ x) : |E₃ x| ≤ (log 4 + 3) / log x + 1 / ⌊x⌋₊ := by
  have hx' := floor_mono hx
  simp only [floor_ofNat] at hx'
  have := sum_prime_inv_sub_sub_bound hx
  rw [prime_M_eq, Primes.tsum_eq_tsum_ite fun p ↦ log (1 - 1 / p) + 1 / p,
      ← Summable.sum_add_tsum_nat_add (⌊x⌋₊ + 1)] at this
  · have h {a b c d : ℝ} (ha : |a| ≤ b) (hac : |a + c| ≤ d) : |c| ≤ b + d := by
      grw [abs_add' c a, ha, hac]
    apply h this
    rw [← sum_filter, ← primesLE_eq_filter_range, sum_add_distrib, E₃]
    ring_nf
    have (i : ℕ) : 0 ≤ - if (1 + i + ⌊x⌋₊).Prime then ((1 + i + ⌊x⌋₊ : ℕ) : ℝ)⁻¹
        + log (1 - ((1 + i + ⌊x⌋₊ : ℕ) : ℝ)⁻¹) else 0 := by
      split_ifs with hp
      · grind [neg_inv_sub_log_sub_inv_nonneg ⟨ _, hp ⟩]
      · simp
    grw [← tsum_neg, abs_of_nonneg (tsum_nonneg this)]
    apply tsum_le_of_sum_range_le this; intro N
    calc
      _ ≤ ∑ i ∈ range N, (((⌊x⌋₊ + i : ℕ): ℝ)⁻¹ - ((⌊x⌋₊ + (i + 1) : ℕ): ℝ)⁻¹) := by
        apply sum_le_sum; intro i _
        split_ifs with h
        · calc
            _ ≤ 1 / ((1 + i + ⌊x⌋₊ : ℕ) : ℝ) ^ 2 := by
              convert neg_inv_sub_log_sub_inv_le ⟨ _, h ⟩ <;> grind
            _ ≤ _ := by field_simp; push_cast; grind
        · field_simp; push_cast; grind
      _ ≤ _ := by rw [sum_range_sub']; field_simp; push_cast; simp [field]
  · rw [← Primes.summable_iff_summable_ite]
    apply ((summable_one_div_nat_rpow.mpr (by norm_num : 1 < (2 : ℝ))).subtype _).of_norm_bounded
    intro p
    have := neg_inv_sub_log_sub_inv_nonneg p
    have := neg_inv_sub_log_sub_inv_le p
    simp_all
    grind

theorem E₃_isBigO : E₃ =O[atTop] fun x ↦ (log x)⁻¹ := by
  trans fun x ↦ (log 4 + 3) / log x + 1 / ⌊x⌋₊
  · apply Eventually.isBigO
    filter_upwards [eventually_ge_atTop 2] with x hx
    simpa using E₃_bound hx
  · simp_rw [division_def]
    refine (isBigO_const_mul_self ..).add (.of_bound 2 ?_)
    filter_upwards [eventually_gt_atTop 2] with x hx
    have := log_pos (by linarith : 1 < x)
    simp [abs_of_pos this]
    have := lt_floor_add_one x
    have : 0 < (⌊x⌋₊ : ℝ) := by linarith
    field_simp
    grw [Real.log_le_self] <;> linarith

theorem E₃_isLittleO : E₃ =o[atTop] fun _ ↦ (1 : ℝ) :=
  E₃_isBigO.trans_isLittleO inv_log_isLittleO_one

theorem E₃_tendsto : Tendsto E₃ atTop (𝓝 0) := by simpa [isLittleO_one_iff] using E₃_isLittleO

theorem exp_E₃_sub_isBigO : (fun x ↦ exp (E₃ x) - 1) =O[atTop] fun x ↦ (log x)⁻¹ := by
  suffices (exp · - 1) =O[𝓝 0] (·) from this.comp_tendsto E₃_tendsto|>.trans E₃_isBigO
  simpa using differentiable_exp.differentiableAt.isBigO_sub (x₀ := 0)

theorem exp_E₃_sub_isLittleO : (fun x ↦ exp (E₃ x) - 1) =o[atTop] fun _ ↦ (1 : ℝ) :=
  exp_E₃_sub_isBigO.trans_isLittleO inv_log_isLittleO_one

theorem exp_E₃_tendsto : Tendsto (fun x ↦ exp (E₃ x)) atTop (𝓝 1) := by
  rw [← tendsto_sub_nhds_zero_iff, ← isLittleO_one_iff (F := ℝ)]
  exact exp_E₃_sub_isLittleO

theorem sum_primes_log_sub_add_isBigO :
    (fun x : ℝ ↦ ∑ p ∈ primesLE ⌊x⌋₊, log (1 - 1 / (p : ℝ)) + log (log x))
    =O[atTop] fun _ ↦ (1 : ℝ) := by
  suffices (E₃ · - eulerMascheroniConstant) =O[atTop] fun _ ↦ (1 : ℝ) from
    this.congr (by grind [sum_prime_log_sub_inv_eq]) (by simp)
  exact E₃_isLittleO.isBigO.sub (isBigO_const_one ..)

theorem sum_primes_log_sub_add_isBigO_nat :
    (fun N : ℕ ↦ ∑ p ∈ primesLE N, log (1 - 1 / (p : ℝ)) + log (log N))
    =O[atTop] fun _ ↦ (1 : ℝ) := by
  convert sum_primes_log_sub_add_isBigO.comp_tendsto tendsto_natCast_atTop_atTop
  <;> simp

theorem log_mul_prod_prime_one_minus_inv_tendsto :
    Tendsto (fun x ↦ log x * ∏ p ∈ primesLE ⌊x⌋₊, (1 - (1 : ℝ) / p)) atTop
    (𝓝 (exp (-eulerMascheroniConstant))) := by
  convert (exp_E₃_tendsto.const_mul (exp (-eulerMascheroniConstant))).congr' ?_
  · simp
  filter_upwards [eventually_gt_atTop 1]
  grind [prod_prime_one_minus_inv_eq, log_pos]

theorem log_mul_prod_prime_one_minus_inv_tendsto_nat :
    Tendsto (fun (N : ℕ) ↦ log N * ∏ p ∈ primesLE N, (1 - (1 : ℝ) / p)) atTop
    (𝓝 (exp (-eulerMascheroniConstant))) := by
  convert log_mul_prod_prime_one_minus_inv_tendsto.comp tendsto_natCast_atTop_atTop
  simp

theorem prod_prime_one_minus_inv_asymp :
    (∏ p ∈ primesLE ⌊·⌋₊, (1 - (1 : ℝ) / p)) ~[atTop] (exp (-eulerMascheroniConstant) / log ·) := by
  have := log_mul_prod_prime_one_minus_inv_tendsto.const_mul (exp eulerMascheroniConstant)
  simp [← exp_add] at this
  refine isEquivalent_of_tendsto_one (this.congr' ?_)
  filter_upwards [eventually_gt_atTop 1]
  grind [log_pos, exp_neg, Pi.div_apply]

theorem prod_prime_one_minus_inv_asymp_nat :
    (∏ p ∈ primesLE ·, (1 - (1 : ℝ) / p)) ~[atTop] (exp (-eulerMascheroniConstant) / log ·) := by
  convert! prod_prime_one_minus_inv_asymp.comp_tendsto tendsto_natCast_atTop_atTop
  simp

end ThirdTheorem


end Mertens
