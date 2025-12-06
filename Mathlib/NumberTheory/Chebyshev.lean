/-
Copyright (c) 2025 Alastair Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Terry Tao, Ruben Van de Velde
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Primorial
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

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
- `Chevyshev.psi_le_const_mul_self` gives Chebyshev's upper bound on `ψ`.

## Notation

We introduce the scoped notations `θ` and `ψ` in the Chebyshev namespace for the Chebyshev
functions.

## References

Parts of this file were upstreamed from the PrimeNumberTheoremAnd project by Kontorovich et al, https://github.com/alexKontorovich/PrimeNumberTheoremAnd.

## TODOS

- Upstream the results relating `theta` and `psi` to the prime counting function.
- Prove Chebyshev's lower bound.
-/
@[expose] public section

open Nat hiding log
open Finset Real
open ArithmeticFunction hiding log

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

/-!
# Relating `ψ` and `θ`

We isolate the contributions of different prime powers to `ψ` and use this to show that `ψ` and `θ`
are close.
-/

theorem psi_eq_sum_theta {x : ℝ} (hx : 0 ≤ x) :
    ψ x = ∑ n ∈ Icc 1 ⌊log x / log 2⌋₊, θ (x ^ ((1 : ℝ) / n)) := by
  unfold psi
  simp_rw [vonMangoldt_apply, ← sum_filter]
  trans ∑ ⟨k, p⟩ ∈ Icc 1 ⌊log x / log 2⌋₊ ×ˢ (Ioc 0 ⌊x⌋₊).filter Nat.Prime
    with p ≤ ⌊x ^ (k : ℝ)⁻¹⌋₊, log p
  · symm
    apply sum_bij (i := fun ⟨k, p⟩ _ ↦ p ^ k )
    · intro ⟨k, p⟩ h
      simp only [mem_filter, mem_Ioc]
      simp only [mem_filter, mem_product, mem_Icc, mem_Ioc] at h
      have k_ne : k ≠ 0 := by linarith
      refine ⟨⟨pow_pos h.1.2.1.1 _, le_floor ?_⟩, ?_⟩
      · push_cast
        trans (x ^ ((k : ℝ)⁻¹)) ^ k
        · gcongr
          trans ↑⌊x ^ (k : ℝ)⁻¹⌋₊
          · exact mod_cast h.2
          · exact floor_le <| rpow_nonneg hx _
        · exact rpow_inv_natCast_pow hx k_ne |>.le
      · exact isPrimePow_def _ |>.mpr ⟨p, k, h.1.2.2.prime, zero_lt_of_ne_zero k_ne, rfl⟩
    · intro ⟨k1, p1⟩ h1 ⟨k2, p2⟩ h2
      simp only [Prod.mk.injEq]
      simp only [mem_filter, mem_product, mem_Icc, mem_Ioc] at *
      intro h
      symm
      rw [← Nat.sub_add_cancel (by linarith : 1 ≤ k1),
        ← Nat.sub_add_cancel (by linarith : 1 ≤ k2)] at h
      convert Nat.Prime.pow_inj h1.1.2.2 h2.1.2.2 h using 1
      lia
    · intro n hn
      simp only [mem_filter, mem_Ioc] at hn
      simp only [mem_filter, mem_product, mem_Icc, mem_Ioc, exists_prop, Prod.exists]
      obtain ⟨p, k, hp, hk, hpk⟩ := isPrimePow_def _ |>.mp hn.2
      refine ⟨k, p, ⟨⟨⟨(by linarith), ?_⟩, ?_, hp.nat_prime⟩, ?_⟩, hpk⟩
      · have : log (p ^ k) = log n := by rw_mod_cast [hpk]
        rw [Real.log_pow] at this
        have log_ne : log p ≠ 0 := by
          apply Real.log_pos _ |>.ne.symm
          norm_cast
          apply hp.nat_prime.one_lt
        apply le_floor
        rw [eq_div_of_mul_eq log_ne this]
        gcongr
        · apply log_nonneg
          trans (n : ℝ)
          · rw_mod_cast [← hpk]
            exact one_le_pow _ _ hp.nat_prime.pos
          · apply le_floor_iff hx |>.mp hn.1.2
        · rw_mod_cast [← hpk]
          apply pow_pos <| hp.nat_prime.pos
        · apply le_floor_iff hx |>.mp hn.1.2
        · norm_cast
          apply hp.nat_prime.two_le
      · refine ⟨hp.nat_prime.pos, ?_⟩
        grw [← hn.1.2, ← hpk]
        exact le_pow hk
      · apply le_floor
        rw [← rpow_rpow_inv (cast_nonneg p) (cast_ne_zero.mpr hk.ne.symm)]
        apply rpow_le_rpow (by bound) _ (by bound)
        rw_mod_cast [hpk]
        exact le_floor_iff hx |>.mp hn.1.2
    · simp only [mem_filter, mem_product, mem_Icc, mem_Ioc, and_imp, Prod.forall]
      intro _ _ _ _ _ _ p_prime _
      rw [p_prime.pow_minFac (by linarith)]
  rw [sum_filter, sum_product]
  refine sum_congr rfl fun k hk ↦ ?_
  simp only [sum_ite, not_le, sum_const_zero, add_zero]
  congr 1
  ext p
  simp only [mem_filter, mem_Ioc]
  refine ⟨fun _ ↦ (by simp_all), fun h ↦ ?_⟩
  simp_all only [mem_Icc, one_div, true_and, and_true]
  grw [h.1.2, floor_le_floor]
  apply rpow_le_self_of_one_le _ (by bound)
  have := one_le_floor_iff _|>.mp <| le_trans (one_le_cast.mp h.2.one_le) h.1.2
  contrapose! this
  apply rpow_lt_one hx this (by bound)

theorem psi_eq_theta_add_sum_theta {x : ℝ} (hx : 2 ≤ x) :
    ψ x = θ x + ∑ n ∈ Icc 2 ⌊log x / log 2⌋₊, θ (x ^ ((1 : ℝ) / n)) := by
  rw [psi_eq_sum_theta (by linarith), ← add_sum_Ioc_eq_sum_Icc]
  · congr
    simp
  · apply le_floor
    apply le_div_iff₀ (by positivity)|>.mpr
    simp
    gcongr

theorem theta_le_psi (x : ℝ) : θ x ≤ ψ x := by
  by_cases h : x < 2
  · rw [theta_eq_zero_of_lt_two h, psi_eq_zero_of_lt_two h]
  push_neg at h
  rw [psi_eq_theta_add_sum_theta h]
  simp only [le_add_iff_nonneg_right]
  exact sum_nonneg fun _ _ ↦ theta_nonneg _

--Note that a more careful argument could remove the log x in the following with a worse constant.
/-- `|ψ x - θ x| ≤ c x √ x` with an explicit constant c. -/
theorem abs_psi_sub_theta_le_sqrt_mul_log {x : ℝ} (hx : 1 ≤ x) :
    |ψ x - θ x| ≤ 2 * x.sqrt * x.log := by
  by_cases hx : x < 2
  · rw [psi_eq_zero_of_lt_two hx, theta_eq_zero_of_lt_two hx, sub_zero, abs_zero]
    bound
  push_neg at hx
  rw [psi_eq_theta_add_sum_theta hx, add_sub_cancel_left]
  apply le_trans <| abs_sum_le_sum_abs ..
  simp_rw [abs_of_nonneg <| theta_nonneg _]
  trans ∑ i ∈ Icc 2 ⌊log x / log 2⌋₊, log 4 * x.sqrt
  · apply sum_le_sum fun i hi ↦ ?_
    apply le_trans (theta_le_log4_mul_x (rpow_nonneg (by linarith) _))
    rw [sqrt_eq_rpow]
    gcongr
    · linarith
    · simp only [mem_Icc] at hi
      exact_mod_cast hi.1
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
    apply one_le_div _|>.mpr <;> bound
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
    · apply le_trans _ <| abs_psi_sub_theta_le_sqrt_mul_log hx
      apply le_abs.mpr
      left
      rfl
    · exact theta_le_log4_mul_x (by linarith)
  _ = _ := by ring

/- Chebyshev's bound `ψ x ≤ c x` with an explicit constnat.
Note that `Chebyshev.psi_le` gives a sharper bound with a better main term. -/
theorem psi_le_const_mul_self {x : ℝ} (hx : 0 ≤ x) :
    ψ x ≤ (log 4 + 4) * x := by
  by_cases hx : x < 1
  · rw [psi_eq_zero_of_lt_two (by linarith)]
    bound
  push_neg at hx
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

end Chebyshev
