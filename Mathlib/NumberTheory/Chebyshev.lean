/-
Copyright (c) 2025 Alastair Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Terry Tao, Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.Primorial
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Data.Nat.Prime.Int

/-!
# Chebyshev functions

This file defines the Chebyshev functions `theta` and `psi`.
These give logarithmically weighted sums of primes and prime powers.

## Main definitions

- `Chebyshev.psi` gives the sum of `ArithmeticFunction.vonMangoldt`
- `Chebyshev.theta` gives the sum of `log p` over primes

## Main results

- `Chebyshev.theta_eq_log_primorial` shows that `θ x` is the log of the product of primes up to x
- `Chebyshev.theta_le_log4_mul_x` gives Chebyshev's upper bound on `θ`
- `Chebyshev.psi_eq_sum_theta` and `Chebyshev.psi_eq_theta_add_sum_theta` relate `psi` to `theta`.
- `Chebyshev.psi_le_const_mul_self` gives Chebyshev's upper bound on `ψ`.
- `Chebyshev.primeCounting_eq_theta_div_log_add_integral` relates the prime counting function to `θ`
- `Chebyshev.eventually_primeCounting_le` gives an upper bound on the prime counting function.

## Notation

We introduce the scoped notations `θ` and `ψ` in the Chebyshev namespace for the Chebyshev
functions.

## References

Parts of this file were upstreamed from the PrimeNumberTheoremAnd project by Kontorovich et al, https://github.com/alexKontorovich/PrimeNumberTheoremAnd.

## TODOS

- Prove Chebyshev's lower bound.
-/
@[expose] public section

open Nat hiding log
open Finset Real
open ArithmeticFunction hiding log
open scoped Nat.Prime

namespace Chebyshev

/-- The sum of `ArithmeticFunction.vonMangoldt` over integers `n ≤ x`. -/
noncomputable def psi (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n

@[inherit_doc]
scoped notation "ψ" => Chebyshev.psi

/-- The sum of `log p` over primes `p ≤ x`. -/
noncomputable def theta (x : ℝ) : ℝ :=
  ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p

@[inherit_doc]
scoped notation "θ" => Chebyshev.theta

theorem psi_nonneg (x : ℝ) : 0 ≤ ψ x :=
  sum_nonneg fun _ _ ↦ (by simp)

theorem theta_nonneg (x : ℝ) : 0 ≤ θ x :=
  sum_nonneg fun n hn ↦ log_nonneg (by aesop)

theorem theta_pos {x : ℝ} (hy : 2 ≤ x) : 0 < θ x := by
  refine sum_pos (fun n hn ↦ log_pos ?_) ⟨2, ?_⟩
  · simp only [mem_filter] at hn; exact_mod_cast hn.2.one_lt
  · simpa using ⟨(le_floor_iff (by grind : 0 ≤ x)).2 hy, Nat.prime_two⟩

theorem psi_eq_sum_Icc (x : ℝ) :
    ψ x = ∑ n ∈ Icc 0 ⌊x⌋₊, Λ n := by
  rw [psi, ← add_sum_Ioc_eq_sum_Icc] <;> simp

theorem theta_eq_sum_Icc (x : ℝ) :
    θ x = ∑ p ∈ Icc 0 ⌊x⌋₊ with p.Prime, log p := by
  rw [theta, sum_filter, sum_filter, ← add_sum_Ioc_eq_sum_Icc] <;> simp

theorem psi_eq_zero_of_lt_two {x : ℝ} (hx : x < 2) : ψ x = 0 := by
  apply sum_eq_zero fun n hn ↦ ?_
  simp only [mem_Ioc] at hn
  convert vonMangoldt_apply_one
  have := lt_of_le_of_lt (le_floor_iff' hn.1.ne.symm |>.mp hn.2) hx
  norm_cast at this
  linarith

theorem theta_eq_zero_of_lt_two {x : ℝ} (hx : x < 2) : θ x = 0 := by
  apply sum_eq_zero fun n hn ↦ ?_
  convert log_one
  simp only [mem_filter, mem_Ioc] at hn
  have := lt_of_le_of_lt (le_floor_iff' hn.1.1.ne.symm |>.mp hn.1.2) hx
  norm_cast at ⊢ this
  linarith

theorem psi_eq_psi_coe_floor (x : ℝ) : ψ x = ψ ⌊x⌋₊ := by
  unfold psi
  rw [floor_natCast]

theorem theta_eq_theta_coe_floor (x : ℝ) : θ x = θ ⌊x⌋₊ := by
  unfold theta
  rw [floor_natCast]

theorem psi_mono : Monotone ψ := by
  intro x y hxy
  apply sum_le_sum_of_subset_of_nonneg
  · exact Ioc_subset_Ioc (by rfl) <| floor_le_floor hxy
  · simp

theorem theta_mono : Monotone θ := by
  intro x y hxy
  apply sum_le_sum_of_subset_of_nonneg
  · exact filter_subset_filter _ <| Ioc_subset_Ioc_right <| floor_mono hxy
  · simp only [mem_filter]
    exact fun p hp _ ↦ log_nonneg (mod_cast hp.2.one_le)

/-- `θ x` is the log of the product of the primes up to `x`. -/
theorem theta_eq_log_primorial (x : ℝ) : θ x = log (primorial ⌊x⌋₊) := by
  unfold theta primorial
  rw [cast_prod, log_prod (fun p hp ↦ mod_cast (mem_filter.mp hp).2.pos.ne')]
  congr 1 with p
  simp_all [Nat.Prime.pos]

/-- Chebyshev's upper bound: `θ x ≤ c x` with the constant `c = log 4`. -/
theorem theta_le_log4_mul_x {x : ℝ} (hx : 0 ≤ x) : θ x ≤ log 4 * x := by
  rw [theta_eq_log_primorial]
  trans log (4 ^ ⌊x⌋₊)
  · apply log_le_log <;> norm_cast
    exacts [primorial_pos _, primorial_le_4_pow _]
  rw [Real.log_pow, mul_comm]
  gcongr
  exact floor_le hx

/-!
## Relating `ψ` and `θ`

We isolate the contributions of different prime powers to `ψ` and use this to show that `ψ` and `θ`
are close.
-/

/-- A sum over prime powers may be written as a double sum over exponents and then primes. -/
theorem sum_PrimePow_eq_sum_sum {R : Type*} [AddCommMonoid R] (f : ℕ → R) {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊ with IsPrimePow n, f n
      = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime, f (p ^ k) := by
  trans ∑ ⟨k, p⟩ ∈ Icc 1 ⌊log x / log 2⌋₊ ×ˢ (Ioc 0 ⌊x⌋₊).filter Nat.Prime
    with p ≤ ⌊x ^ (k : ℝ)⁻¹⌋₊, f (p ^ k)
  · refine (sum_bij (i := fun ⟨k, p⟩ _ ↦ p ^ k) ?_ ?_ ?_ ?_).symm
    · simp +contextual [hx, rpow_nonneg, le_floor_iff, ← Nat.pos_iff_ne_zero, Prime.isPrimePow,
        one_le_iff_ne_zero, le_rpow_inv_iff_of_pos, isPrimePow_pow_iff, Nat.prime_iff]
    · simp +contextual only [hx, rpow_nonneg, le_floor_iff, mem_filter, mem_product, mem_Icc,
        one_le_iff_ne_zero, Nat.pos_iff_ne_zero, mem_Ioc, and_imp, Prod.forall, Prod.mk.injEq]
      intro k₁ p₁ hk₁ _ _ _ hp₁ _ k₂ p₂ hk₂ _ _ _ hp₂ _ H
      exact (Nat.Prime.pow_inj' hp₁ hp₂ hk₁ hk₂ H).symm
    · simp +contextual only [mem_filter, mem_Ioc, hx, le_floor_iff, and_assoc, rpow_nonneg,
        mem_product, mem_Icc, succ_le_iff, exists_prop, Prod.exists, exists_and_left, and_imp]
      rintro b hb₀ hbx ⟨p, k, hp, hk₀, rfl⟩
      rw [cast_pow] at hbx
      refine ⟨k, hk₀, le_floor ?_, p, hp.nat_prime.pos, ?_, hp.nat_prime, ?_, rfl⟩
      · rw [le_div_iff₀ (log_pos (by norm_num)), ← Real.log_pow]
        refine Real.log_le_log (by simp) (.trans ?_ hbx)
        exact pow_le_pow_left₀ (by norm_num) (mod_cast hp.nat_prime.two_le) _
      · exact (le_self_pow₀ (mod_cast hp.nat_prime.one_le) hk₀.ne').trans hbx
      · simp_all [le_rpow_inv_iff_of_pos]
    · simp
  · rw [sum_filter, sum_product]
    refine sum_congr rfl fun k hk ↦ ?_
    simp only [sum_ite, not_le, sum_const_zero, add_zero]
    congr 1
    ext p
    simp only [mem_filter, mem_Ioc]
    refine ⟨fun _ ↦ (by simp_all), fun h ↦ ?_⟩
    simp_all only [mem_Icc, one_div, true_and, and_true]
    grw [h.1.2, floor_le_floor]
    apply rpow_le_self_of_one_le _ (by bound)
    have := one_le_floor_iff _ |>.mp <| le_trans (one_le_cast.mp h.2.one_le) h.1.2
    contrapose! this
    apply rpow_lt_one hx this (by bound)

theorem psi_eq_sum_theta {x : ℝ} (hx : 0 ≤ x) :
    ψ x = ∑ n ∈ Icc 1 ⌊log x / log 2⌋₊, θ (x ^ ((1 : ℝ) / n)) := by
  simp_rw [psi, vonMangoldt_apply, ← sum_filter, sum_PrimePow_eq_sum_sum _ hx]
  apply sum_congr rfl fun _ hk ↦ sum_congr rfl fun _ _ ↦ ?_
  rw [Nat.Prime.pow_minFac _ (by linarith [mem_Icc.mp hk])]
  simp_all

theorem psi_eq_theta_add_sum_theta {x : ℝ} (hx : 2 ≤ x) :
    ψ x = θ x + ∑ n ∈ Icc 2 ⌊log x / log 2⌋₊, θ (x ^ ((1 : ℝ) / n)) := by
  rw [psi_eq_sum_theta (by linarith), ← add_sum_Ioc_eq_sum_Icc]
  · congr
    simp
  · rw [le_floor_iff' one_ne_zero, le_div_iff₀ (by positivity), cast_one, one_mul]
    gcongr

theorem theta_le_psi (x : ℝ) : θ x ≤ ψ x := by
  by_cases! h : x < 2
  · rw [theta_eq_zero_of_lt_two h, psi_eq_zero_of_lt_two h]
  rw [psi_eq_theta_add_sum_theta h]
  simp only [le_add_iff_nonneg_right]
  exact sum_nonneg fun _ _ ↦ theta_nonneg _

--Note that a more careful argument could remove the log x in the following with a worse constant.
/-- `|ψ x - θ x| ≤ c √ x log x` with an explicit constant c. -/
theorem abs_psi_sub_theta_le_sqrt_mul_log {x : ℝ} (hx : 1 ≤ x) :
    |ψ x - θ x| ≤ 2 * x.sqrt * x.log := by
  by_cases! hx : x < 2
  · rw [psi_eq_zero_of_lt_two hx, theta_eq_zero_of_lt_two hx, sub_zero, abs_zero]
    bound
  rw [psi_eq_theta_add_sum_theta hx, add_sub_cancel_left]
  apply le_trans <| abs_sum_le_sum_abs ..
  simp_rw [abs_of_nonneg <| theta_nonneg _]
  trans ∑ i ∈ Icc 2 ⌊log x / log 2⌋₊, log 4 * x.sqrt
  · apply sum_le_sum fun i hi ↦ ?_
    apply le_trans (theta_le_log4_mul_x (rpow_nonneg (by linarith) _))
    rw [sqrt_eq_rpow]
    gcongr <;> simp_all
  simp only [sum_const, card_Icc, reduceSubDiff, nsmul_eq_mul]
  calc
  _ ≤ (log x / log 2) * (log 4 * √x) := by
    gcongr
    rw [cast_sub]
    · trans ↑⌊log x / log 2⌋₊
      · linarith
      · exact floor_le (by bound)
    apply le_floor
    norm_cast
    apply one_le_div _ |>.mpr <;> bound
  _ = (log 4 / log 2) * x.sqrt * x.log := by field
  _ = _ := by
    congr
    rw [(by norm_num : (4 : ℝ) = 2 ^ 2), Real.log_pow]
    field

/-- Explicit upper bound on `ψ`. -/
theorem psi_le {x : ℝ} (hx : 1 ≤ x) :
    ψ x ≤ log 4 * x + 2 * x.sqrt * x.log := by
  calc
  _ = ψ x - θ x + θ x := by ring
  _ ≤ 2 * x.sqrt * x.log + log 4 * x := by
    gcongr
    · exact le_trans (le_abs_self _) (abs_psi_sub_theta_le_sqrt_mul_log hx)
    · exact theta_le_log4_mul_x (by linarith)
  _ = _ := by ring

/-- Chebyshev's bound `ψ x ≤ c x` with an explicit constant.
Note that `Chebyshev.psi_le` gives a sharper bound with a better main term. -/
theorem psi_le_const_mul_self {x : ℝ} (hx : 0 ≤ x) :
    ψ x ≤ (log 4 + 4) * x := by
  by_cases! hx : x < 1
  · rw [psi_eq_zero_of_lt_two (by linarith)]
    bound
  apply le_trans (psi_le hx)
  rw [add_mul]
  gcongr 1
  grw [sqrt_eq_rpow, log_le_rpow_div (ε := 1 / 2) (by linarith) (by linarith), ← mul_div_assoc,
    ← mul_one_div]
  nth_rw 2 [mul_assoc]
  rw [← rpow_add (by linarith)]
  norm_num
  linarith

/-- `ψ - θ` is the sum of `Λ` over non-primes. -/
theorem psi_sub_theta_eq_sum_not_prime (x : ℝ) :
    ψ x - θ x = ∑ n ∈ Ioc 0 ⌊x⌋₊ with ¬n.Prime, vonMangoldt n := by
  rw [psi, theta, sum_filter, sum_filter, ← sum_sub_distrib]
  refine sum_congr rfl fun n hn ↦ ?_
  split_ifs with h
  · simp [h, vonMangoldt_apply_prime]
  · simp

section PrimeCounting

/-! ## Relation to prime counting

We relate `θ` to the prime counting function `π`.-/

open Asymptotics Filter MeasureTheory

/-- Integrability for the integral in `Chebyshev.primeCounting_eq_theta_div_log_add_integral`. -/
theorem integrableOn_theta_div_id_mul_log_sq (x : ℝ) :
    IntegrableOn (fun t ↦ θ t / (t * log t ^ 2)) (Set.Icc 2 x) volume := by
  conv => arg 1; ext; rw [theta, div_eq_mul_one_div, mul_comm, sum_filter]
  refine integrableOn_mul_sum_Icc _ (by norm_num) <| ContinuousOn.integrableOn_Icc fun x hx ↦
    ContinuousAt.continuousWithinAt ?_
  have : x ≠ 0 := by linarith [hx.1]
  have : x * log x ^ 2 ≠ 0 := mul_ne_zero this <| by simp; grind
  fun_prop (disch := assumption)

/-- Expresses the prime counting function `π` in terms of `θ` by using Abel summation. -/
theorem primeCounting_eq_theta_div_log_add_integral {x : ℝ} (hx : 2 ≤ x) :
    π ⌊x⌋₊ = θ x / log x + ∫ t in 2..x, θ t / (t * log t ^ 2) := by
  -- Rewrite in a form to which Abel summation can be applied
  simp only [primeCounting, primeCounting', count_eq_card_filter_range]
  rw [card_eq_sum_ones, range_succ_eq_Icc_zero, sum_filter]
  push_cast
  let a : ℕ → ℝ := Set.indicator (setOf Nat.Prime) (fun n ↦ log n)
  trans ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * a n
  · refine sum_congr rfl fun n hn ↦ ?_
    split_ifs with h
    · have : log n ≠ 0 := log_ne_zero_of_pos_of_ne_one (mod_cast h.pos) (mod_cast h.ne_one)
      simp [a, h, field]
    · simp [a, h]
  rw [sum_mul_eq_sub_integral_mul₁ a (f := fun n ↦ (log n)⁻¹) (by simp [a]) (by simp [a]),
    ← intervalIntegral.integral_of_le hx]
  · -- Rewrite the derivative inside the intigral
    have int_deriv (f : ℝ → ℝ) :
        ∫ u in 2..x, deriv (fun x ↦ (log x)⁻¹) u * f u =
        ∫ u in 2..x, f u * -(u * log u ^ 2)⁻¹ :=
      intervalIntegral.integral_congr fun u _ ↦ by simp [deriv_inv_log, field]
    simp [int_deriv, a, Set.indicator_apply, sum_filter, theta_eq_sum_Icc]
    grind
  · -- Differentiability
    intro z ⟨hz, _⟩
    have : z ≠ 0 := by linarith
    have : log z ≠ 0 := by apply log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop (disch := assumption)
  · -- Integrability of the derivative
    refine ContinuousOn.integrableOn_Icc fun z ⟨hz, _⟩ ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ deriv_inv_log) deriv_inv_log
    have hz₀ : z ≠ 0 := by linarith
    have : log z ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 <| log_ne_zero_of_pos_of_ne_one ?_ ?_ <;> linarith
    exact ContinuousAt.continuousWithinAt <| by fun_prop (disch := assumption)

theorem intervalIntegrable_one_div_log_sq {a b : ℝ} (one_lt_a : 1 < a) (one_lt_b : 1 < b) :
    IntervalIntegrable (fun x ↦ 1 / log x ^ 2) MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable fun x hx ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.mem_uIcc] at hx
  have : x ≠ 0 := by grind
  have : log x ^ 2 ≠ 0 := pow_ne_zero _ (log_ne_zero.mpr (by grind))
  fun_prop (disch := assumption)

/- Simple bound on the integral from monotonicity.
We will bound the integral on 2..x by splitting into two intervals and using this result on both. -/
private theorem integral_1_div_log_sq_le {a b : ℝ} (hab : a ≤ b) (one_lt : 1 < a) :
    ∫ x in a..b, 1 / log x ^ 2 ≤ (b - a) / log a ^ 2 := by
  calc
  _ ≤ ∫ x in a..b, 1 / log a ^ 2 := by
      refine intervalIntegral.integral_mono_on hab ?_ (by simp) fun x ⟨hx, _⟩ ↦ by gcongr <;> bound
      apply intervalIntegrable_one_div_log_sq <;> linarith
  _ ≤ _ := by simp [field]

/- Explicit integral bound, we expose a BigO version below since the constants and lower order term
aren't very convenient. -/
private theorem integral_one_div_log_sq_le_explicit {x : ℝ} (hx : 4 ≤ x) :
    ∫ t in 2..x, 1 / log t ^ 2 ≤ 4 * x / (log x) ^ 2 + x.sqrt / log 2 ^ 2 := by
  have two_le_sqrt : 2 ≤ x.sqrt := Real.le_sqrt_of_sq_le <| by norm_num [hx]
  have sqrt_le_x : x.sqrt ≤ x := sqrt_le_left (by linarith) |>.mpr (by bound)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := x.sqrt)]
  · grw [integral_1_div_log_sq_le two_le_sqrt (by linarith),
      integral_1_div_log_sq_le sqrt_le_x (by linarith)]
    rw [log_sqrt (by linarith), add_comm, div_pow, ← div_mul, mul_comm, mul_div_assoc]
    norm_num
    gcongr <;> linarith
  all_goals apply intervalIntegrable_one_div_log_sq <;> linarith

-- Somewhat arbitrary bound which we use to estimate the second term.
private theorem sqrt_isLittleO :
    Real.sqrt =o[atTop] (fun x ↦ x / log x ^ 2) := by
  apply isLittleO_mul_iff_isLittleO_div _ |>.mp
  · conv => arg 2; ext; rw [mul_comm]
    apply isLittleO_mul_iff_isLittleO_div _ |>.mpr
    · simp_rw [div_sqrt, sqrt_eq_rpow, ← rpow_two]
      apply isLittleO_log_rpow_rpow_atTop _ (by norm_num)
    filter_upwards [eventually_gt_atTop 0] with x hx using sqrt_ne_zero'.mpr hx
  filter_upwards [eventually_gt_atTop 1] with x hx
  apply pow_ne_zero _ <| log_ne_zero.mpr ⟨_, _, _⟩ <;> linarith

theorem integral_one_div_log_sq_isBigO :
    (fun x ↦ ∫ t in 2..x, 1 / log t ^ 2) =O[atTop] (fun x ↦ x / log x ^ 2) := by
  trans (fun x ↦ 4 * x / log x ^ 2 + √x / log 2 ^ 2)
  · apply IsBigO.of_bound'
    filter_upwards [eventually_ge_atTop 4] with x hx
    apply le_trans <| intervalIntegral.abs_integral_le_integral_abs (by linarith)
    rw [intervalIntegral.integral_congr (g := (fun t ↦ 1 / log t ^ 2))]
    · grw [integral_one_div_log_sq_le_explicit hx, norm_of_nonneg]
      positivity
    intro t ht
    simp
  refine IsBigO.add ?_ ?_
  · simp_rw [mul_div_assoc]
    apply isBigO_const_mul_self
  conv => arg 2; ext; rw [← mul_one_div, mul_comm]
  apply IsBigO.const_mul_left sqrt_isLittleO.isBigO

/-- Bound on the integral in `Chebyshev.primeCounting_eq_theta_div_log_add_integral`. -/
theorem integral_theta_div_log_sq_isBigO :
    (fun x ↦ ∫ t in 2..x, θ t / (t * log t ^ 2)) =O[atTop] (fun x ↦ x / log x ^ 2) := by
  refine (IsBigO.of_bound (log 4) ?_).trans integral_one_div_log_sq_isBigO
  filter_upwards [eventually_ge_atTop 4] with x hx
  simp_rw [norm_eq_abs]
  calc |∫ (t : ℝ) in 2..x, θ t / (t * log t ^ 2)|
    _ ≤ ∫ (x : ℝ) in 2..x, |θ x / (x * log x ^ 2)| :=
        intervalIntegral.abs_integral_le_integral_abs (by linarith)
    _ ≤ ∫ (x : ℝ) in 2..x, log 4 * (1 / log x ^ 2) :=
        intervalIntegral.integral_mono_on (by linarith) ?hf ?hg fun t ⟨ht, _⟩ ↦ ?hh
    _ = log 4 * |∫ (t : ℝ) in 2..x, 1 / log t ^ 2| := by
        rw [intervalIntegral.integral_const_mul, abs_of_nonneg]
        exact intervalIntegral.integral_nonneg (by linarith) fun u _ ↦ by positivity
  case hf =>
    refine (intervalIntegrable_iff.mpr ?_).abs
    rw [Set.uIoc_of_le (by linarith), ← integrableOn_Icc_iff_integrableOn_Ioc]
    exact integrableOn_theta_div_id_mul_log_sq x
  case hg =>
    refine (intervalIntegrable_one_div_log_sq ?_ ?_).const_mul _ <;> linarith
  case hh =>
    calc |θ t / (t * log t ^ 2)|
    _ = θ t / (t * log t ^ 2) := abs_of_nonneg (by positivity [theta_nonneg t])
    _ ≤ log 4 * t / (t * log t ^ 2) := by grw [theta_le_log4_mul_x (by linarith)]
    _ = log 4 * (1 / log t ^ 2) := by field

theorem integral_theta_div_log_sq_isLittleO :
    (fun x ↦ ∫ t in 2..x, θ t / (t * log t ^ 2)) =o[atTop] (fun x ↦ x / log x) := by
  refine integral_theta_div_log_sq_isBigO.trans_isLittleO ?_
  refine isLittleO_iff_tendsto' (by simp) |>.mpr ?_
  refine Tendsto.congr' (f₁ := fun x ↦ (log x)⁻¹) ?_ tendsto_log_atTop.inv_tendsto_atTop
  filter_upwards [eventually_gt_atTop 0] with x hx
  field

theorem primeCounting_sub_theta_div_log_isBigO :
    (fun x ↦ π ⌊x⌋₊ - θ x / log x) =O[atTop] (fun x ↦ x / log x ^ 2) := by
  apply integral_theta_div_log_sq_isBigO.congr' _ (by rfl)
  filter_upwards [eventually_ge_atTop 2] with x hx
  rw [primeCounting_eq_theta_div_log_add_integral hx]
  simp

/-- Chebyshev's upper bound on the prime counting function -/
theorem eventually_primeCounting_le {ε : ℝ} (εpos : 0 < ε) :
    ∀ᶠ x in atTop, π ⌊x⌋₊ ≤ (log 4 + ε) * x / log x := by
  have := integral_theta_div_log_sq_isLittleO.bound εpos
  filter_upwards [eventually_ge_atTop 2, this] with x hx hx2
  rw [primeCounting_eq_theta_div_log_add_integral hx, add_mul, add_div]
  have hl : 0 ≤ log x := by bound
  rw [norm_of_nonneg (show 0 ≤ x / log x by bound), ← mul_div_assoc] at hx2
  grw [theta_le_log4_mul_x (by linarith), ← hx2]
  grind [le_norm_self]

end PrimeCounting
end Chebyshev
