/-
Copyright (c) 2023 Gareth Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gareth Ma
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Funny docstring placeholder blablabla
-/

/- An alternative is to use n.choose k everywhere. Otherwise, this imports `Finset.choose` -/
open Finset hiding choose
open Nat BigOperators Polynomial

namespace Choose

variable {n k p : ℕ} [hp : Fact p.Prime]

theorem lucas : choose n k ≡ choose (n % p) (k % p) * choose (n / p) (k / p) [ZMOD p] := by
  have decompose : ((X : (ZMod p)[X]) + 1) ^ n = (X + 1) ^ (n % p) * (X ^ p + 1) ^ (n / p) := by
    nth_rw 1 [← mod_add_div n p, pow_add, pow_mul, add_pow_char (ZMod p)[X] (p := p), one_pow]
  simp only [← ZMod.intCast_eq_intCast_iff, Int.cast_mul, Int.cast_ofNat,
    ← coeff_X_add_one_pow _ n k, ← eq_intCast (Int.castRingHom (ZMod p)), ← coeff_map,
    Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, map_X, decompose]
  simp only [add_pow, one_pow, mul_one, ← pow_mul, sum_mul_sum]
  conv_lhs =>
    arg 1; arg 2; ext k; arg 2; ext k'
    rw [← mul_assoc, mul_right_comm _ _ (X ^ (p * k')), ← pow_add, mul_assoc, ← cast_mul]
  simp only [finset_sum_coeff, coeff_mul_natCast, coeff_X_pow, ite_mul, zero_mul, ← cast_mul]
  rw [← sum_product', sum_ite_eq_iff (range (n % p + 1) ×ˢ range (n / p + 1)) (k % p, k / p)]
  · simp_rw [mem_product, mem_range]
    split_ifs with h
    · simp
    · rw [not_and_or, lt_succ, not_le, not_lt] at h
      cases h with | _ h => simp [choose_eq_zero_of_lt h]
  · intro ⟨x₁, x₂⟩ hx
    rw [Prod.mk.injEq]
    constructor <;> intro h
    · simp only [mem_product, mem_range] at hx
      have h' : x₁ < p := lt_of_lt_of_le hx.left $ mod_lt _ Fin.size_pos'
      rw [h, add_mul_mod_self_left, add_mul_div_left _ _ Fin.size_pos', eq_comm (b := x₂)]
      exact ⟨mod_eq_of_lt h', self_eq_add_left.mpr (div_eq_of_lt h')⟩
    · rw [← h.left, ← h.right, mod_add_div]

/- TODO: Finish proof -/
theorem lucas' {a : ℕ} (ha₁ : n ≤ p ^ a) (ha₂ : k ≤ p ^ a) :
    (choose n k) ≡ ∏ i in range a.succ, choose (n / p ^ i % p) (k / p ^ i % p) [ZMOD p] := by
  sorry
