/-
Copyright (c) 2025 Roman Skovron. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roman Skovron
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

/-!
# Square Roots of Quadratic Residues

In this file we prove how to extract square roots of quadratic residues modulo
primes of the form `4*k + 3` and `8*k + 5`.

## Main results

- `exists_sqrt_of_residue_mod4_eq3` : For `p = 4*k + 3` prime and `legendreSym p a = 1`,
there are explicit square roots `± a^(k+1)`.
- `exists_sqrt_of_residue_mod8_eq5` : For `p = 8*k + 5` prime and `legendreSym p a = 1`,
there are explicit square roots `± a^(k+1) * 2^(2k+1)`.
-/

namespace QuadraticResidueRoots

private lemma two_mul_two_eq_four : 2 * 2 = 4 := rfl
private lemma succ_double_add_one_eq (n : ℕ) : 2 * n + 2 = (2 * n + 1) + 1 := rfl

/--
If `p = 4*k + 3` is prime, `a ≠ 0 (mod p)` and `legendreSym p a = 1`,
then there are two square roots of `a` in `ZMod p`, namely `a^(k+1)` and `-a^(k+1)`.
-/
theorem exists_sqrt_of_residue_mod4_eq3 {p : ℕ} [hp : Fact p.Prime] (hpne2 : p ≠ 2)
  {a : ℤ} (ha : (a : ZMod p) ≠ 0)
  (hleg : legendreSym p a = 1)
  (hk : ∃ k : ℕ, p = 4 * k + 3) :
  ∃ k : ℕ, ∃ x₁ x₂ : ZMod p,
    p = 4 * k + 3 ∧
    x₁ = ( (a : ZMod p) ^ (k + 1) : ZMod p) ∧
    x₂ = (-(a : ZMod p) ^ (k + 1) : ZMod p) ∧
    x₁ ^ 2 = (a : ZMod p) ∧
    x₂ ^ 2 = (a : ZMod p) := by
  obtain ⟨k, hk⟩ := hk
  have half : (p - 1) / 2 = 2 * k + 1 := by
    rw [hk]
    norm_num
    rw [←two_mul_two_eq_four, Nat.mul_assoc, Nat.mul_comm, Nat.mul_div_cancel]
    decide

  have a_pow := by simpa [half] using (legendreSym.euler_criterion_traditional hpne2 ha).mp hleg
  have a_pow_succ : (↑a : ZMod p) ^ (2 * k + 2) = ↑a := by
    rw [succ_double_add_one_eq, pow_add, a_pow, one_mul, pow_one]

  let x₁ := (a : ZMod p) ^ (k + 1)
  let x₂ := -x₁

  use k, x₁, x₂
  constructor
  · exact hk
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · -- x₁ ^ 2 = ↑a
    rw [←pow_mul, Nat.mul_comm]
    exact a_pow_succ
  · -- x₁ ^ 2 = ↑a
    rw [neg_sq, ←pow_mul, Nat.mul_comm]
    exact a_pow_succ

/--
If `p = 8*k + 5` is prime, `a ≠ 0 (mod p)`, and `legendreSym p a = 1`, then there are
two square roots of `a` in `ZMod p`:
  1. If `a^(2*k+1) = 1`, then `x₁₂ = ± a^(k+1)` are square roots
  2. If `a^(2*k+1) = -1`, then `x₁₂ = ± a^(k+1) * 2^(2k+1)` are square roots
-/
theorem exists_sqrt_of_residue_mod8_eq5 {p : ℕ} [hp : Fact p.Prime] (hpne2 : p ≠ 2)
  {a : ℤ} (ha : (a : ZMod p) ≠ 0)
  (hleg : legendreSym p a = 1)
  (hk : ∃ k : ℕ, p = 8 * k + 5) :
  ∃ k : ℕ, ∃ x₁ x₂ : ZMod p,
    p = 8 * k + 5 ∧ ((
        (a : ZMod p) ^ (2*k + 1) = (1 : ZMod p) ∧
        x₁ = ( (a : ZMod p) ^ (k + 1) : ZMod p) ∧
        x₂ = (-(a : ZMod p) ^ (k + 1) : ZMod p) ∧
        x₁ ^ 2 = (a : ZMod p) ∧
        x₂ ^ 2 = (a : ZMod p)
      ) ∨ (
        (a : ZMod p) ^ (2*k + 1) = (-1 : ZMod p) ∧
        x₁ = ( (a : ZMod p) ^ (k + 1) * 2 ^ (2*k + 1) : ZMod p) ∧
        x₂ = (-(a : ZMod p) ^ (k + 1) * 2 ^ (2*k + 1) : ZMod p) ∧
        x₁ ^ 2 = (a : ZMod p) ∧
        x₂ ^ 2 = (a : ZMod p)
      )) := by
  obtain ⟨k, hk⟩ := hk
  have half : (p - 1) / 2 = 4 * k + 2 := by
    have : 2 * 4 = 8 := rfl
    rw [hk]
    norm_num
    rw [←this, ←two_mul_two_eq_four, Nat.mul_assoc, ←Nat.left_distrib,
        Nat.mul_comm, Nat.mul_div_cancel]
    decide

  have a_pow := by simpa [half] using (legendreSym.euler_criterion_traditional hpne2 ha).mp hleg

  let r := (a : ZMod p) ^ (2 * k + 1)
  have r_sq : r ^ 2 = 1 := by
    rw [←pow_mul, Nat.right_distrib, Nat.mul_comm, ←Nat.mul_assoc]
    norm_num
    exact a_pow

  have r_cases : r = 1 ∨ r = -1 := by
    apply sq_eq_one_iff.mp
    exact r_sq

  have h₂ {p : ℕ} [hp : Fact p.Prime] (hpne2 : p ≠ 2) : p / 2 = (p - 1) / 2 := by
    rcases Nat.Prime.odd_of_ne_two hp.out hpne2 with ⟨k, rfl⟩
    have h₁ : (2 * k) / 2 = k := by norm_num
    have h₂ : (1 : ℕ) / 2 = 0 := rfl
    rw [Nat.add_div, h₁, h₂]
    · simp only [Nat.mul_mod_right, Nat.mod_one, zero_add]
      have : (if 2 ≤ 1 % 2 then 1 else 0) = 0 := by decide
      rw [this]
      simp
    · decide

  have hleg2 : (legendreSym p 2 : ZMod p) = (2 : ZMod p) ^ ((p - 1) / 2) := by
    rw [legendreSym.eq_pow, h₂ hpne2]
    norm_cast

  have two_pow_non_quadratic_residual : (2 ^ (4 * k + 2) : ZMod p) = (-1 : ZMod p) := by
    rw [half] at hleg2
    rw [←hleg2, legendreSym.two_mod8_eq_5 hk]
    norm_cast

  cases r_cases with
  | inl r_eq_one =>
    have a_pow_succ : (↑a : ZMod p) ^ (2 * k + 2) = ↑a := by
      have h₁ : (↑a : ZMod p) ^ (2 * k + 1) = 1 := by rw [←r_eq_one]
      rw [succ_double_add_one_eq, pow_add, h₁, one_mul, pow_one]

    let x₁ := (a : ZMod p) ^ (k + 1)
    let x₂ := -x₁

    use k, x₁, x₂
    constructor
    · exact hk
    left
    constructor
    · exact r_eq_one
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · rw [←pow_mul, Nat.mul_comm, Nat.left_distrib, a_pow_succ]
    · rw [neg_sq, ←pow_mul, Nat.mul_comm, Nat.left_distrib, a_pow_succ]
  | inr r_eq_neg_one =>
    have a_pow_succ : (↑a : ZMod p) ^ (2 * k + 2) = -↑a := by
      have h₁ : (↑a : ZMod p) ^ (2 * k + 1) = -1 := by rw [←r_eq_neg_one]
      rw [succ_double_add_one_eq, pow_add, h₁, pow_one, neg_one_mul]

    let x₁ := (a : ZMod p) ^ (k + 1) * (2 : ZMod p) ^ (2 * k + 1)
    let x₂ := -((a : ZMod p) ^ (k + 1)) * (2 : ZMod p) ^ (2 * k + 1)

    use k, x₁, x₂
    constructor
    · exact hk
    right
    constructor
    · exact r_eq_neg_one
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · -- x₁ ^ 2 = ↑a
      rw [mul_pow, ←pow_mul, Nat.mul_comm, left_distrib, mul_one, a_pow_succ, ←pow_mul,
      Nat.mul_comm, left_distrib, mul_one, ←mul_assoc, two_mul_two_eq_four, neg_eq_neg_one_mul,
      mul_assoc, mul_comm, mul_assoc, two_pow_non_quadratic_residual, neg_mul_neg, mul_one, mul_one]
    · -- x₂ ^ 2 = ↑a
      rw [mul_pow, neg_sq, ←pow_mul, Nat.mul_comm, left_distrib, mul_one, a_pow_succ, ←pow_mul,
      Nat.mul_comm, left_distrib, mul_one, ←mul_assoc, two_mul_two_eq_four, neg_eq_neg_one_mul,
      mul_assoc, mul_comm, mul_assoc, two_pow_non_quadratic_residual, neg_mul_neg, mul_one, mul_one]

end QuadraticResidueRoots
