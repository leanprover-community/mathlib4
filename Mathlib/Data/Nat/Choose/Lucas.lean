/-
Copyright (c) 2023 Gareth Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gareth Ma
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.ZMod.Basic
import Mathlib.Init
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Lucas's theorem

This file contains a proof of [Lucas's theorem](https://en.wikipedia.org/wiki/Lucas's_theorem) about
binomial coefficients, which says that for primes `p`, `n` choose `k` is congruent to product of
`n_i` choose `k_i` modulo `p`, where `n_i` and `k_i` are the base-`p` digits of `n` and `k`,
respectively.

## Main statements

* `lucas_theorem`: the binomial coefficient `n choose k` is congruent to the product of `n_i choose
  k_i` modulo `p`, where `n_i` and `k_i` are the base-`p` digits of `n` and `k`, respectively.
-/

public section

open Finset hiding choose

open Nat Polynomial

namespace Choose

variable {n k a b p : ℕ} [Fact p.Prime]

/-- For primes `p`, `choose n k` is congruent to `choose (n % p) (k % p) * choose (n / p) (k / p)`
modulo `p`. Also see `choose_modEq_choose_mod_mul_choose_div_nat` for the version with `MOD`. -/
theorem choose_modEq_choose_mod_mul_choose_div :
    choose n k ≡ choose (n % p) (k % p) * choose (n / p) (k / p) [ZMOD p] := by
  have decompose : ((X : (ZMod p)[X]) + 1) ^ n = (X + 1) ^ (n % p) * (X ^ p + 1) ^ (n / p) := by
    simpa using add_pow_eq_mul_pow_add_pow_div_char (X : (ZMod p)[X]) 1 p _
  simp only [← ZMod.intCast_eq_intCast_iff,
    ← coeff_X_add_one_pow _ n k, ← eq_intCast (Int.castRingHom (ZMod p)), ← coeff_map,
    Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, map_X, decompose]
  simp only [add_pow, one_pow, mul_one, ← pow_mul, sum_mul_sum]
  conv_lhs =>
    enter [1, 2, k, 2, k']
    rw [← mul_assoc, mul_right_comm _ _ (X ^ (p * k')), ← pow_add, mul_assoc, ← cast_mul]
  have h_iff : ∀ x ∈ range (n % p + 1) ×ˢ range (n / p + 1),
      k = x.1 + p * x.2 ↔ (k % p, k / p) = x := by
    intro ⟨x₁, x₂⟩ hx
    rw [Prod.mk.injEq]
    constructor <;> intro h
    · simp only [mem_product, mem_range] at hx
      have h' : x₁ < p := lt_of_lt_of_le hx.left <| mod_lt _ Fin.pos'
      rw [h, add_mul_mod_self_left, add_mul_div_left _ _ Fin.pos', eq_comm (b := x₂)]
      exact ⟨mod_eq_of_lt h', right_eq_add.mpr (div_eq_of_lt h')⟩
    · rw [← h.left, ← h.right, mod_add_div]
  simp only [finset_sum_coeff, coeff_mul_natCast, coeff_X_pow, ite_mul, zero_mul, ← cast_mul]
  rw [← sum_product', sum_congr rfl (fun a ha ↦ if_congr (h_iff a ha) rfl rfl), sum_ite_eq]
  split_ifs with h
  · simp
  · rw [mem_product, mem_range, mem_range, not_and_or, Nat.lt_succ_iff, not_le, not_lt] at h
    cases h <;> simp [choose_eq_zero_of_lt (by tauto)]

/-- For primes `p`, `choose n k` is congruent to `choose (n % p) (k % p) * choose (n / p) (k / p)`
modulo `p`. Also see `choose_modEq_choose_mod_mul_choose_div` for the version with `ZMOD`. -/
theorem choose_modEq_choose_mod_mul_choose_div_nat :
    choose n k ≡ choose (n % p) (k % p) * choose (n / p) (k / p) [MOD p] := by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_modEq_choose_mod_mul_choose_div

/-- For primes `p`, `choose n k` is congruent to the product of `choose (⌊n / p ^ i⌋ % p)
(⌊k / p ^ i⌋ % p)` over i < a, multiplied by `choose (⌊n / p ^ a⌋) (⌊k / p ^ a⌋)`, modulo `p`. -/
theorem choose_modEq_choose_mul_prod_range_choose (a : ℕ) :
    choose n k ≡ choose (n / p ^ a) (k / p ^ a) *
      ∏ i ∈ range a, choose (n / p ^ i % p) (k / p ^ i % p) [ZMOD p] :=
  match a with
  | Nat.zero => by simp
  | Nat.succ a => (choose_modEq_choose_mul_prod_range_choose a).trans <| by
    rw [prod_range_succ, cast_mul, ← mul_assoc, mul_right_comm]
    gcongr
    apply choose_modEq_choose_mod_mul_choose_div.trans
    simp_rw [pow_succ, Nat.div_div_eq_div_mul, mul_comm, Int.ModEq.refl]

/-- **Lucas's Theorem**: For primes `p`, `choose n k` is congruent to the product of
`choose (⌊n / p ^ i⌋ % p) (⌊k / p ^ i⌋ % p)` over `i` modulo `p`. -/
theorem choose_modEq_prod_range_choose {a : ℕ} (ha₁ : n < p ^ a) (ha₂ : k < p ^ a) :
    choose n k ≡ ∏ i ∈ range a, choose (n / p ^ i % p) (k / p ^ i % p) [ZMOD p] := by
  apply (choose_modEq_choose_mul_prod_range_choose a).trans
  simp_rw [Nat.div_eq_of_lt ha₁, Nat.div_eq_of_lt ha₂, choose, cast_one, one_mul, cast_prod,
    Int.ModEq.refl]

/-- **Lucas's Theorem**: For primes `p`, `choose n k` is congruent to the product of
`choose (⌊n / p ^ i⌋ % p) (⌊k / p ^ i⌋ % p)` over `i` modulo `p`. -/
theorem choose_modEq_prod_range_choose_nat {a : ℕ} (ha₁ : n < p ^ a) (ha₂ : k < p ^ a) :
    choose n k ≡ ∏ i ∈ range a, choose (n / p ^ i % p) (k / p ^ i % p) [MOD p] := by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_modEq_prod_range_choose ha₁ ha₂

alias lucas_theorem := choose_modEq_prod_range_choose
alias lucas_theorem_nat := choose_modEq_prod_range_choose_nat

/-- For primes `p`, `choose (p * a) (p * b)` is congruent to `choose a b` modulo `p`.
Also see `choose_mul_mul_modEq_choose_nat` for the version with `MOD`. -/
theorem choose_mul_mul_modEq_choose :
    choose (p * a) (p * b) ≡ choose a b [ZMOD p] := by
  grw [choose_modEq_choose_mod_mul_choose_div]
  simp [NeZero.pos, Int.ModEq.refl]

/-- For primes `p`, `choose (p * a) (p * b)` is congruent to `choose a b` modulo `p`.
Also see `choose_mul_mul_modEq_choose` for the version with `ZMOD`. -/
theorem choose_mul_mul_modEq_choose_nat :
    choose (p * a) (p * b) ≡ choose a b [MOD p] := by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_mul_mul_modEq_choose

/-- For primes `p`, `choose (p ^ k * a) (p ^ k * b)` is congruent to `choose a b` modulo `p`.
Also see `choose_pow_mul_pow_mul_modEq_choose_nat` for the version with `MOD`. -/
theorem choose_pow_mul_pow_mul_modEq_choose :
    choose (p ^ k * a) (p ^ k * b) ≡ choose a b [ZMOD p] := by
  induction k with
  | zero => simp [Int.ModEq.refl]
  | succ k ih =>
    grw [Nat.pow_succ', mul_assoc, mul_assoc, choose_mul_mul_modEq_choose, ih]

/-- For primes `p`, `choose (p ^ k * a) (p ^ k * b)` is congruent to `choose a b` modulo `p`.
Also see `choose_pow_mul_pow_mul_modEq_choose` for the version with `ZMOD`. -/
theorem choose_pow_mul_pow_mul_modEq_choose_nat :
    choose (p ^ k * a) (p ^ k * b) ≡ choose a b [MOD p] := by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_pow_mul_pow_mul_modEq_choose

end Choose
