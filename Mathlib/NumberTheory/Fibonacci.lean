/-
Copyright (c) 2026 Wei-Ting Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei-Ting Li
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.LinearCombination

/-!
# Fibonacci numbers modulo a prime

For a prime `p ≠ 2` we prove the congruence `F_p ≡ (5 / p) (mod p)`, where `(5 / p)` is the
Legendre symbol, together with its consequences `p ∣ F_{p - 1}` when `(5 / p) = 1` and
`p ∣ F_{p + 1}` when `(5 / p) = -1`. By quadratic reciprocity this reads: `p ∣ F_{p - 1}` for
`p ≡ ±1 (mod 5)` and `p ∣ F_{p + 1}` for `p ≡ ±2 (mod 5)`.

## Main results

* `pow_succ_eq_fib_mul_add_fib`: in a commutative ring, `a ^ 2 = a + 1` implies
  `a ^ (n + 1) = F_{n + 1} * a + F_n`.
* `Nat.fib_cast_eq_legendreSym`: `(F_p : ZMod p) = (5 / p)` for every prime `p ≠ 2`.
* `Nat.dvd_fib_sub_one_of_legendreSym_eq_one`, `Nat.dvd_fib_add_one_of_legendreSym_eq_neg_one`:
  `p ∣ F_{p - (5 / p)}`.
* `Nat.Prime.dvd_fib_sub_one_of_mod_five`, `Nat.Prime.dvd_fib_add_one_of_mod_five`: the same,
  with the Legendre symbol evaluated through quadratic reciprocity.

## Implementation notes

Let `A := (ZMod p)[X] ⧸ (X ^ 2 - X - 1)` and let `α` be the class of `X`, so that
`α ^ 2 = α + 1` and hence `α ^ p = F_p α + F_{p - 1}`. Put `s := 2 α - 1`; then `s ^ 2 = 5`, so
`s ^ p = 5 ^ (p / 2) * s` for odd `p`, while the Frobenius endomorphism of `A` gives
`s ^ p = 2 α ^ p - 1`. Since `1, α` are linearly independent over `ZMod p` (whether or not
`X ^ 2 - X - 1` splits), comparing coefficients yields `F_p = 5 ^ (p / 2)` and
`2 F_{p - 1} = 1 - 5 ^ (p / 2)` in `ZMod p`, and Euler's criterion identifies `5 ^ (p / 2)` with
`(5 / p)`.

The converse of the divisibility statements fails: `323 = 17 * 19` divides `F_{324}`.

## Tags

Fibonacci numbers, Legendre symbol, Frobenius endomorphism, Lucas sequences
-/

public section

open Polynomial

/-- If `a ^ 2 = a + 1` in a commutative ring, then the powers of `a` are given by Fibonacci
numbers: `a ^ (n + 1) = F_{n + 1} * a + F_n`. -/
theorem pow_succ_eq_fib_mul_add_fib {R : Type*} [CommRing R] {a : R} (ha : a ^ 2 = a + 1)
    (n : ℕ) : a ^ (n + 1) = (Nat.fib (n + 1) : R) * a + Nat.fib n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : a ^ (n + 2) = a * a ^ (n + 1) := by ring
    rw [h, ih]
    push_cast [Nat.fib_add_two]
    linear_combination (Nat.fib (n + 1) : R) * ha

namespace Nat

variable (p : ℕ) [hp : Fact p.Prime]

/-- `F_p ≡ 5 ^ (p / 2)` and `2 F_{p - 1} ≡ 1 - 5 ^ (p / 2) (mod p)` for a prime `p ≠ 2`, by
the argument in the implementation notes. -/
private theorem fib_cast_aux (hp2 : p ≠ 2) :
    (fib p : ZMod p) = 5 ^ (p / 2) ∧ 2 * (fib (p - 1) : ZMod p) = 1 - 5 ^ (p / 2) := by
  obtain ⟨f, hf⟩ : ∃ f : (ZMod p)[X], f = X ^ 2 - X - 1 := ⟨_, rfl⟩
  have hdeg : f.degree = 2 := by rw [hf]; compute_degree!
  have hnat : f.natDegree = 2 := by rw [hf]; compute_degree!
  have : Nontrivial (AdjoinRoot f) := AdjoinRoot.nontrivial _ (by rw [hdeg]; decide)
  have : CharP (AdjoinRoot f) p := (Algebra.charP_iff (ZMod p) _ p).mp inferInstance
  set α := AdjoinRoot.root f
  have hα : α ^ 2 = α + 1 := by
    have h : AdjoinRoot.mk f (X ^ 2 - X - 1) = 0 := by rw [← hf]; exact AdjoinRoot.mk_self
    simp only [map_sub, map_pow, AdjoinRoot.mk_X, map_one] at h
    linear_combination h
  -- `α ^ p` in terms of Fibonacci numbers
  have h₁ : α ^ p = fib p * α + fib (p - 1) := by
    have h := pow_succ_eq_fib_mul_add_fib hα (p - 1)
    rwa [Nat.sub_add_cancel hp.out.pos] at h
  -- `s ^ p` from `s ^ 2 = 5`
  have h₂ : (2 * α - 1) ^ p = 5 ^ (p / 2) * (2 * α - 1) := by
    have hp1 : 2 * (p / 2) + 1 = p := by obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp2; omega
    calc (2 * α - 1) ^ p = (2 * α - 1) ^ (2 * (p / 2) + 1) := by rw [hp1]
      _ = ((2 * α - 1) ^ 2) ^ (p / 2) * (2 * α - 1) := by rw [pow_succ, pow_mul]
      _ = 5 ^ (p / 2) * (2 * α - 1) := by
        rw [show (2 * α - 1) ^ 2 = 5 by linear_combination 4 * hα]
  -- `s ^ p` from the Frobenius endomorphism
  have h₃ : (2 * α - 1) ^ p = 2 * α ^ p - 1 := by
    have h2p : (2 : AdjoinRoot f) ^ p = 2 := by
      rw [← map_ofNat (algebraMap (ZMod p) (AdjoinRoot f)) 2, ← map_pow, ZMod.pow_card]
    rw [sub_pow_char, one_pow, mul_pow, h2p]
  -- compare coefficients in the basis `1, α`
  have hlin (c₁ c₀ : ZMod p)
      (h : algebraMap (ZMod p) _ c₁ * α + algebraMap (ZMod p) _ c₀ = 0) : c₁ = 0 ∧ c₀ = 0 := by
    have hg : AdjoinRoot.mk f (C c₁ * X + C c₀) = 0 := by
      rwa [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
        ← AdjoinRoot.algebraMap_eq]
    rw [AdjoinRoot.mk_eq_zero] at hg
    have hle : (C c₁ * X + C c₀).natDegree ≤ 1 := by compute_degree
    have hz : (C c₁ * X + C c₀ : (ZMod p)[X]) = 0 :=
      eq_zero_of_dvd_of_natDegree_lt hg (by omega)
    exact ⟨by simpa using congrArg (coeff · 1) hz, by simpa using congrArg (coeff · 0) hz⟩
  obtain ⟨e₁, e₀⟩ := hlin (2 * fib p - 2 * 5 ^ (p / 2)) (2 * fib (p - 1) - 1 + 5 ^ (p / 2)) (by
    simp only [map_sub, map_add, map_mul, map_one, map_pow, map_ofNat, map_natCast]
    linear_combination h₃.symm.trans h₂ - 2 * h₁)
  have h2ne : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  exact ⟨mul_left_cancel₀ h2ne (by linear_combination e₁), by linear_combination e₀⟩

/-- **Fibonacci numbers modulo a prime**: `F_p ≡ (5 / p) (mod p)` for every prime `p ≠ 2`. -/
theorem fib_cast_eq_legendreSym (hp2 : p ≠ 2) : (fib p : ZMod p) = legendreSym p 5 := by
  rw [(fib_cast_aux p hp2).1, legendreSym.eq_pow]
  norm_num

/-- `2 F_{p - 1} ≡ 1 - (5 / p) (mod p)` for every prime `p ≠ 2`. -/
theorem two_mul_fib_sub_one_cast (hp2 : p ≠ 2) :
    2 * (fib (p - 1) : ZMod p) = 1 - legendreSym p 5 := by
  rw [(fib_cast_aux p hp2).2, legendreSym.eq_pow]
  norm_num

/-- If `(5 / p) = 1` (i.e. `p ≡ ±1 (mod 5)`), then `p ∣ F_{p - 1}`. -/
theorem dvd_fib_sub_one_of_legendreSym_eq_one (hp2 : p ≠ 2) (h : legendreSym p 5 = 1) :
    p ∣ fib (p - 1) := by
  have h2 := two_mul_fib_sub_one_cast p hp2
  rw [h] at h2
  have h2ne : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  refine (ZMod.natCast_eq_zero_iff _ _).mp (mul_left_cancel₀ h2ne ?_)
  rw [h2]; push_cast; ring

/-- If `(5 / p) = -1` (i.e. `p ≡ ±2 (mod 5)`), then `p ∣ F_{p + 1}`. -/
theorem dvd_fib_add_one_of_legendreSym_eq_neg_one (hp2 : p ≠ 2) (h : legendreSym p 5 = -1) :
    p ∣ fib (p + 1) := by
  have h1 := fib_cast_eq_legendreSym p hp2
  have h2 := two_mul_fib_sub_one_cast p hp2
  rw [h] at h1 h2
  have h2ne : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  -- avoid the literal `-1` in `ZMod p`: rewrite everything as `_ + 1 = 0`.
  have hfp : (fib p : ZMod p) + 1 = 0 := by rw [h1]; push_cast; exact neg_add_cancel 1
  have hfp1 : (fib (p - 1) : ZMod p) = 1 := by
    have hz : (2 : ZMod p) * ((fib (p - 1) : ZMod p) - 1) = 2 * 0 := by
      rw [mul_sub, h2]; push_cast; ring
    exact sub_eq_zero.mp (mul_left_cancel₀ h2ne hz)
  have : (fib (p + 1) : ZMod p) = 0 := by
    rw [fib_add_one hp.out.ne_zero]; push_cast
    linear_combination hfp1 + hfp
  exact (ZMod.natCast_eq_zero_iff _ _).mp this

/-- If `p ≡ ±1 (mod 5)` is prime, then `p ∣ F_{p - 1}`. -/
theorem Prime.dvd_fib_sub_one_of_mod_five {p : ℕ} (hp : p.Prime) (h : p % 5 = 1 ∨ p % 5 = 4) :
    p ∣ fib (p - 1) := by
  have hsq : IsSquare ((p % 5 : ℕ) : ZMod 5) ∧ ((p % 5 : ℕ) : ZMod 5) ≠ 0 := by
    rcases h with h | h <;> rw [h] <;> decide
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have := Fact.mk hp
  have : Fact (Nat.Prime 5) := ⟨prime_five⟩
  refine dvd_fib_sub_one_of_legendreSym_eq_one p hp2 ?_
  change legendreSym p ((5 : ℕ) : ℤ) = 1
  rw [legendreSym.quadratic_reciprocity_one_mod_four (by norm_num) hp2, legendreSym.mod,
    show (p : ℤ) % ((5 : ℕ) : ℤ) = ((p % 5 : ℕ) : ℤ) by norm_cast]
  exact (legendreSym.eq_one_iff' 5 hsq.2).mpr hsq.1

/-- If `p ≡ ±2 (mod 5)` is prime, then `p ∣ F_{p + 1}`. -/
theorem Prime.dvd_fib_add_one_of_mod_five {p : ℕ} (hp : p.Prime) (h : p % 5 = 2 ∨ p % 5 = 3) :
    p ∣ fib (p + 1) := by
  rcases eq_or_ne p 2 with rfl | hp2
  · decide
  have hsq : ¬ IsSquare ((p % 5 : ℕ) : ZMod 5) := by
    rcases h with h | h <;> rw [h] <;> decide
  have := Fact.mk hp
  have : Fact (Nat.Prime 5) := ⟨prime_five⟩
  refine dvd_fib_add_one_of_legendreSym_eq_neg_one p hp2 ?_
  change legendreSym p ((5 : ℕ) : ℤ) = -1
  rw [legendreSym.quadratic_reciprocity_one_mod_four (by norm_num) hp2, legendreSym.mod,
    show (p : ℤ) % ((5 : ℕ) : ℤ) = ((p % 5 : ℕ) : ℤ) by norm_cast]
  exact (legendreSym.eq_neg_one_iff' 5).mpr hsq

end Nat

end
