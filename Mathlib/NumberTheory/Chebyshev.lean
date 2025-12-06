/-
Copyright (c) 2025 Alastair Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.Primorial
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

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

## Notation

We introduce the scoped notations `θ` and `ψ` in the Chebyshev namespace for the Chebyshev
functions.

## References

Parts of this file were upstreamed from the PrimeNumberTheoremAnd project by Kontorovich et al, https://github.com/alexKontorovich/PrimeNumberTheoremAnd.

## TODOS

- Upstream the results relating `theta` and `psi` to each other and to the prime counting function.
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
  simp_all [Nat.Prime.pos, Nat.lt_add_one_iff]

/-- Chebyshev's upper bound: `θ x ≤ c x` with the constant `c = log 4`. -/
theorem theta_le_log4_mul_x {x : ℝ} (hx : 0 ≤ x) : θ x ≤ log 4 * x := by
  rw [theta_eq_log_primorial]
  trans log (4 ^ ⌊x⌋₊)
  · apply log_le_log <;> norm_cast
    exacts [primorial_pos _, primorial_le_4_pow _]
  rw [Real.log_pow, mul_comm]
  gcongr
  exact floor_le hx

section PrimeCounting

/-! ## Relation to prime counting

We relate `θ` to the prime counting function `π`.-/

lemma deriv_log_inv {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) (h2 : x ≠ -1) :
    deriv (fun x => (log x)⁻¹) x = -x⁻¹ / (log x ^ 2) := by
  rw [deriv_fun_inv'', deriv_log]
  · fun_prop (disch := assumption)
  exact log_ne_zero.mpr ⟨h0, h1, h2⟩

open Asymptotics Filter MeasureTheory

theorem integrable_theta_div (x : ℝ) :
    IntegrableOn (fun t ↦ (θ t) / (t * log t ^ 2)) (Set.Icc 2 x) volume := by
  conv => arg 1; ext; rw [theta, div_eq_mul_one_div, mul_comm, sum_filter]
  apply integrableOn_mul_sum_Icc _ (by norm_num)
  apply ContinuousOn.integrableOn_Icc
  intro x hx
  apply ContinuousAt.continuousWithinAt
  have : x ≠ 0 := by linarith [hx.1]
  have : x * log x ^ 2 ≠ 0 := by
    apply mul_ne_zero this
    apply pow_ne_zero _ <| log_ne_zero_of_pos_of_ne_one _ _ <;> linarith [hx.1]
  fun_prop (disch := assumption)

theorem primeCounting_eq {x : ℝ} (hx : 2 ≤ x) :
    π ⌊x⌋₊ = θ x / log x + ∫ t in Set.Icc 2 x, θ t / (t * log t ^ 2) := by
  simp only [primeCounting, primeCounting', count_eq_card_filter_range]
  rw [card_eq_sum_ones, range_succ_eq_Icc_zero]
  rw [← add_sum_erase (a := 2) _ _ (by simp [prime_two, le_floor hx])]
  trans 1 + ∑ x ∈ Ioc 2 ⌊x⌋₊ with x.Prime, 1
  · norm_cast
    congr
    ext p
    constructor <;> intro h
    · simp_all only [mem_erase, mem_filter, mem_Icc, _root_.zero_le, true_and, mem_Ioc,
      and_true]
      exact lt_of_le_of_ne h.2.2.two_le h.1.symm
    · simp_all only [mem_filter, mem_Ioc, mem_erase, mem_Icc, _root_.zero_le, and_self,
      and_true]
      exact h.1.1.ne.symm
  rw [sum_filter]
  let a : ℕ → ℝ := Set.indicator (setOf Nat.Prime) (fun n => log n)
  trans 1 + ∑ n ∈ Ioc 2 ⌊x⌋₊, (1 / log n) * a n
  · congr 1
    apply sum_congr rfl fun n hn ↦ ?_
    unfold a
    split_ifs with h
    · simp only [one_div, Set.mem_setOf_eq, h, Set.indicator_of_mem]
      have : log n ≠ 0 := by
        apply log_ne_zero_of_pos_of_ne_one <;> norm_cast
        exacts [h.pos, h.ne_one]
      field
    · simp [h]
  rw [(by simp : 2 = ⌊(2 : ℝ)⌋₊)]
  rw [sum_mul_eq_sub_sub_integral_mul a (f := fun n ↦ 1 / log n) (by linarith) (by linarith)]
  · have int_deriv (f : ℝ → ℝ) :
      ∫ (u : ℝ) in Set.Ioc 2 x, deriv (fun x ↦ 1 / log x) u * f u =
      ∫ (u : ℝ) in Set.Icc 2 x, f u * -(u * log u ^ 2)⁻¹ := by
      rw [← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_ae measurableSet_Icc
      refine Filter.Eventually.of_forall (fun u hu => ?_)
      simp only [one_div, mul_inv_rev, mul_neg]
      rw [deriv_log_inv]
      · ring
      all_goals linarith [hu.1]
    rw [int_deriv]
    have : log 2 ≠ 0 := by simp; linarith
    simp [a, Set.indicator_apply, sum_filter, show Icc 0 2 = {0, 1, 2} by ext; simp; omega,
      prime_two, theta_eq_sum_Icc, this, MeasureTheory.integral_neg]
    ring_nf!
    congr
    ext
    ring
  · intro z hz
    have : z ≠ 0 := by linarith [hz.1]
    have : log z ≠ 0 := by
      apply log_ne_zero_of_pos_of_ne_one <;> linarith [hz.1]
    fun_prop (disch := assumption)
  · simp only [one_div]
    have : ∀ y ∈ Set.Icc 2 x, deriv (fun x ↦ (log x)⁻¹) y = -(y * log y ^ 2)⁻¹:= by
      intro y hy
      rw [deriv_log_inv, mul_inv, ← div_eq_mul_inv, neg_div]
      all_goals linarith [hy.1]
    apply ContinuousOn.integrableOn_Icc
    intro z hz
    apply ContinuousWithinAt.congr (f := fun x => - (x * log x ^ 2)⁻¹)
    · apply ContinuousWithinAt.neg
      apply ContinuousAt.continuousWithinAt
      have : z ≠ 0 := by linarith [hz.1]
      have : z * (log z) ^ 2 ≠ 0 := by
        apply mul_ne_zero this <| pow_ne_zero _ <| log_ne_zero.mpr ⟨_, _, _⟩
        all_goals linarith [hz.1]
      fun_prop (disch := assumption)
    · apply this
    · apply this z hz

theorem intervalIntegrable_one_div_log_sq {a b : ℝ} (one_lt_a : 1 < a) (one_lt_b : 1 < b) :
    IntervalIntegrable (fun x ↦ 1 / log x ^ 2) MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable fun x hx ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.mem_uIcc] at hx
  have : x ≠ 0 := by bound
  have : log x ^ 2 ≠ 0 := by simp; bound
  fun_prop (disch := assumption)

theorem integral_1_div_log_sq_le {a b : ℝ} (hab : a ≤ b) (one_lt : 1 < a) :
    ∫ x in a..b, 1 / log x  ^ 2 ≤ (b - a) / log a ^2 := by
  trans ∫ x in a..b, 1 / log a ^ 2
  · apply intervalIntegral.integral_mono_on hab
    · apply intervalIntegrable_one_div_log_sq <;> linarith
    · apply intervalIntegrable_const
      simp
    · intro x hx
      gcongr
      · bound
      · bound
      · linarith [hx.1]
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one_div]

theorem integral_one_div_log_sq_le_one_div_log_sq {x : ℝ} (hx : 4 ≤ x) :
    ∫ t in 2..x, 1 / log t ^ 2 ≤ 4 * x / (log x) ^ 2 + x.sqrt / log 2 ^ 2 := by
  have two_le_sqrt : 2 ≤ x.sqrt := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have sqrt_le_x : x.sqrt ≤ x := by
    apply sqrt_le_left (by linarith) |>.mpr
    bound
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := x.sqrt)]
  · grw [integral_1_div_log_sq_le two_le_sqrt (by linarith),
      integral_1_div_log_sq_le sqrt_le_x (by linarith)]
    rw [log_sqrt (by linarith), add_comm, div_pow, ← div_mul, mul_comm, mul_div_assoc]
    norm_num
    gcongr <;> linarith
  all_goals apply intervalIntegrable_one_div_log_sq <;> linarith

theorem integral_theta_div_log_sq_le {x : ℝ} (hx : 4 ≤ x) :
    ∫ t in 2..x, θ t / (t * log t ^ 2) ≤ log 4 * (4 * x / log x ^ 2 + √x / log 2 ^ 2) := by
  trans ∫ t in 2..x, log 4 * (1 / log t ^ 2)
  · apply intervalIntegral.integral_mono_on (by linarith)
    · apply intervalIntegrable_iff.mpr
      rw [Set.uIoc_of_le (by linarith), ← integrableOn_Icc_iff_integrableOn_Ioc]
      apply integrable_theta_div
    · apply IntervalIntegrable.const_mul
      apply intervalIntegrable_one_div_log_sq <;> linarith
    · intro x hx
      grw [theta_le_log4_mul_x (by linarith [hx.1])]
      · field_simp [(by linarith [hx.1] : x ≠ 0)]
        rfl
      · have : 1 < x := by linarith [hx.1]
        positivity
  grw [intervalIntegral.integral_const_mul, integral_one_div_log_sq_le_one_div_log_sq hx]

theorem sqrt_isBigO :
    Real.sqrt =O[atTop] (fun x ↦ x / log x ^2) := by
  apply isBigO_mul_iff_isBigO_div _|>.mp
  · conv => arg 2; ext; rw [mul_comm]
    apply isBigO_mul_iff_isBigO_div _|>.mpr
    · simp_rw [div_sqrt, sqrt_eq_rpow]
      apply IsLittleO.isBigO
      simp_rw [← rpow_two]
      apply isLittleO_log_rpow_rpow_atTop _ (by norm_num)
    filter_upwards [eventually_gt_atTop 0] with x hx using sqrt_ne_zero'.mpr hx
  filter_upwards [eventually_gt_atTop 1] with x hx
  apply pow_ne_zero _ <| log_ne_zero.mpr ⟨_, _, _⟩ <;> linarith

theorem integral_theta_div_log_sq_isBigO :
    (fun x ↦ ∫ t in 2..x, θ t / (t * log t ^ 2)) =O[atTop] (fun x ↦ x / log x ^ 2) := by
  trans (fun x ↦ log 4 * (4 * x / log x ^ 2 + √x / log 2 ^ 2))
  · rw [isBigO_iff]
    use 1
    filter_upwards [eventually_ge_atTop 4] with x hx
    apply le_trans <| intervalIntegral.abs_integral_le_integral_abs (by linarith)
    rw [intervalIntegral.integral_congr (g := (fun t ↦ θ t / (t * log t ^2)))]
    · grw [integral_theta_div_log_sq_le hx, norm_of_nonneg, one_mul]
      positivity
    intro t ht
    simp only [abs_eq_self]
    apply div_nonneg <| theta_nonneg _
    rw [Set.uIcc_of_le (by linarith)] at ht
    have : 1 < t := by linarith [ht.1]
    positivity
  apply IsBigO.const_mul_left
  apply IsBigO.add
  · simp_rw [mul_div_assoc]
    apply IsBigO.const_mul_left
    apply isBigO_refl
  conv => arg 2; ext; rw [← mul_one_div, mul_comm]
  apply IsBigO.const_mul_left sqrt_isBigO

theorem integral_theta_div_log_sq_isLittleO :
    (fun x ↦ ∫ t in 2..x, θ t / (t * log t ^ 2)) =o[atTop] (fun x ↦ x / log x) := by
  apply integral_theta_div_log_sq_isBigO.trans_isLittleO
  apply isLittleO_iff_tendsto' _|>.mpr
  · apply Tendsto.congr' (f₁ := (fun x ↦ 1 / log x))
    · filter_upwards [eventually_gt_atTop 0] with x hx
      field
    simp_rw [one_div]
    apply Tendsto.inv_tendsto_atTop tendsto_log_atTop
  filter_upwards with x
  simp

theorem primeCounting_sub_theta_div_log_isBigO :
    (fun x ↦ π ⌊x⌋₊ - θ x / log x) =O[atTop] (fun x ↦ x / log x ^ 2) := by
  apply integral_theta_div_log_sq_isBigO.congr' _ (by rfl)
  filter_upwards [eventually_ge_atTop 2] with x hx
  rw [primeCounting_eq hx, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hx]
  simp

theorem eventually_primeCounting_le {c : ℝ} (hc : log 4 < c) :
    ∀ᶠ x in atTop, π ⌊x⌋₊ ≤ c * x / log x := by
  have := integral_theta_div_log_sq_isLittleO
  replace this := this.bound
  specialize this (by linarith :  0 < c - log 4)
  filter_upwards [eventually_ge_atTop 2, this] with x hx hx2
  rw [primeCounting_eq hx, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx,
    (by ring : c * x / log x = log 4 * x / log x + (c - log 4) * x / log x)]
  grw [theta_le_log4_mul_x (by linarith)]
  · gcongr
    rw [norm_eq_abs, norm_eq_abs] at hx2
    nth_rewrite 2 [abs_of_nonneg] at hx2
    · rw [← mul_div_assoc] at hx2
      apply le_trans (le_abs_self _) hx2
    · bound
  · bound

end PrimeCounting
end Chebyshev
