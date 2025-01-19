/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Binomial coefficents and factorial variants

This file proves asymptotic theorems for binomial coefficents and factorial variants.

## Main definitions

* `isEquivalent_descFactorial` is the proof that `n.descFactorial k ~ n^k` as `n → ∞`.

* `isEquivalent_choose` is the proof that `n.choose k ~ n^k / k!` as `n → ∞`.

* `isTheta_choose` is the proof that `n.choose k = Θ(n^k)` as `n → ∞`.
-/


open Asymptotics Topology

/-- `n.descFactorial k` is asymptotically equivalent to `n^k`. -/
lemma isEquivalent_descFactorial (k : ℕ) :
    (fun (n : ℕ) ↦ (n.descFactorial k : ℝ))
      ~[Filter.atTop] (fun (n : ℕ) ↦ (n^k : ℝ)) := by
  induction k with
  | zero => simpa using IsEquivalent.refl
  | succ k h =>
    simp_rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ']
    apply IsEquivalent.mul _ h
    have hz : ∀ᶠ (x : ℕ) in Filter.atTop, (x : ℝ) ≠ 0 := by
      rw [Filter.eventually_atTop]
      use 1; intro n hn
      exact ne_of_gt (mod_cast hn)
    rw [isEquivalent_iff_tendsto_one hz, ← Filter.tendsto_add_atTop_iff_nat k]
    simpa using tendsto_natCast_div_add_atTop (k : ℝ)

/-- `n.choose k` is asymptotically equivalent to `n^k / k!`. -/
theorem isEquivalent_choose (k : ℕ) :
    (fun (n : ℕ) ↦ (n.choose k : ℝ))
      ~[Filter.atTop] (fun (n : ℕ) ↦ (n^k / k.factorial : ℝ)) := by
  conv_lhs =>
    intro n
    rw [Nat.choose_eq_descFactorial_div_factorial,
      Nat.cast_div (n.factorial_dvd_descFactorial k) (mod_cast k.factorial_ne_zero)]
  exact (isEquivalent_descFactorial k).div IsEquivalent.refl

/-- `n.choose k` is big-theta `n^k`. -/
theorem isTheta_choose (k : ℕ) :
    (fun (n : ℕ) ↦ (n.choose k : ℝ))
      =Θ[Filter.atTop] (fun (n : ℕ) ↦ (n^k : ℝ)) := by
  apply (isEquivalent_choose k).trans_isTheta
  conv_lhs =>
    intro n
    rw [div_eq_mul_inv, mul_comm]
  apply IsTheta.const_mul_left _ isTheta_rfl
  exact inv_ne_zero (mod_cast k.factorial_ne_zero)
