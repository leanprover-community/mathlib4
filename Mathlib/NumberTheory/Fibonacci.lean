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

For a prime `p ≠ 2` we prove the classical congruence `F_p ≡ (5 / p) (mod p)`, where
`(5 / p)` is the Legendre symbol, together with its consequences `p ∣ F_{p - 1}` when
`(5 / p) = 1` and `p ∣ F_{p + 1}` when `(5 / p) = -1` (Lucas, 1878). By quadratic reciprocity
this reads: `p ∣ F_{p - 1}` for `p ≡ ±1 (mod 5)` and `p ∣ F_{p + 1}` for `p ≡ ±2 (mod 5)`.

## Main results

* `pow_succ_eq_fib_mul_add_fib`: in a commutative ring, `a ^ 2 = a + 1` implies
  `a ^ (n + 1) = F_{n + 1} * a + F_n`.
* `Nat.fib_cast_eq_legendreSym`: `(F_p : ZMod p) = (5 / p)` for every prime `p ≠ 2`.
* `Nat.dvd_fib_sub_one_of_legendreSym_eq_one`, `Nat.dvd_fib_add_one_of_legendreSym_eq_neg_one`:
  `p ∣ F_{p - (5 / p)}`.
* `Nat.Prime.dvd_fib_sub_one_of_mod_five`, `Nat.Prime.dvd_fib_add_one_of_mod_five`: the same,
  with the Legendre symbol evaluated through quadratic reciprocity.

## Proof outline

Let `A := (ZMod p)[X] ⧸ (X ^ 2 - X - 1)` and let `α` be the class of `X`, so that
`α ^ 2 = α + 1` and hence `α ^ (n + 1) = F_{n + 1} α + F_n`. Put `s := 2 α - 1`; then
`s ^ 2 = 5`. For odd `p` this gives `s ^ p = 5 ^ (p / 2) * s`, while the Frobenius in
characteristic `p` gives `s ^ p = 2 α ^ p - 1`. Since `A` is free of rank two over `ZMod p`
with basis `1, α` (whether or not `X ^ 2 - X - 1` splits), comparing coefficients yields
`F_p = 5 ^ (p / 2)` and `2 F_{p - 1} = 1 - 5 ^ (p / 2)` in `ZMod p`; Euler's criterion
identifies `5 ^ (p / 2)` with `(5 / p)`. No case distinction on `(5 / p)` is needed.

The converse of the divisibility statements fails: `323 = 17 * 19` divides `F_{324}`
(such composites are the Fibonacci pseudoprimes).

## Tags

fibonacci, legendre symbol, frobenius, lucas sequence
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

noncomputable section Aux

variable (p : ℕ) [hp : Fact p.Prime]

/-- The quadratic `X ^ 2 - X - 1` over `ZMod p`. -/
private abbrev fibPoly : (ZMod p)[X] := X ^ 2 - X - 1

private lemma fibPoly_degree : (fibPoly p).degree = 2 := by
  unfold fibPoly; compute_degree!

private lemma fibPoly_ne_zero : fibPoly p ≠ 0 := by
  intro h
  have := fibPoly_degree p
  rw [h, degree_zero] at this
  exact absurd this (by decide)

/-- The ring `(ZMod p)[X] ⧸ (X ^ 2 - X - 1)`. -/
private abbrev FibRing := AdjoinRoot (fibPoly p)

/-- The class of `X` in `FibRing p`; it satisfies `α ^ 2 = α + 1`. -/
private abbrev fibRoot : FibRing p := AdjoinRoot.root (fibPoly p)

private lemma nontrivial_fibRing : Nontrivial (FibRing p) :=
  AdjoinRoot.nontrivial _ (by rw [fibPoly_degree]; decide)

private lemma charP_fibRing : CharP (FibRing p) p := by
  have := nontrivial_fibRing p
  exact (Algebra.charP_iff (ZMod p) (FibRing p) p).mp inferInstance

private lemma fibRoot_sq : fibRoot p ^ 2 = fibRoot p + 1 := by
  have h : fibRoot p ^ 2 - fibRoot p - 1 = 0 := by
    have hr := AdjoinRoot.eval₂_root (fibPoly p)
    simpa using hr
  linear_combination h

private lemma fibS_sq : (2 * fibRoot p - 1) ^ 2 = 5 := by
  linear_combination 4 * fibRoot_sq p

private lemma fibS_pow_odd (hodd : Odd p) :
    (2 * fibRoot p - 1) ^ p = (5 : FibRing p) ^ (p / 2) * (2 * fibRoot p - 1) := by
  have hp1 : 2 * (p / 2) + 1 = p := by obtain ⟨k, hk⟩ := hodd; omega
  calc (2 * fibRoot p - 1) ^ p
      = (2 * fibRoot p - 1) ^ (2 * (p / 2) + 1) := by rw [hp1]
    _ = ((2 * fibRoot p - 1) ^ 2) ^ (p / 2) * (2 * fibRoot p - 1) := by rw [pow_succ, pow_mul]
    _ = (5 : FibRing p) ^ (p / 2) * (2 * fibRoot p - 1) := by rw [fibS_sq]

private lemma two_pow_card_fibRing : (2 : FibRing p) ^ p = 2 := by
  have := charP_fibRing p
  have h : (1 + 1 : FibRing p) ^ p = 1 ^ p + 1 ^ p := add_pow_char _ _ p
  rw [show (2 : FibRing p) = 1 + 1 by norm_num]
  simpa using h

private lemma fibS_pow_frobenius (hodd : Odd p) :
    (2 * fibRoot p - 1) ^ p = 2 * fibRoot p ^ p - 1 := by
  have := charP_fibRing p
  have hrw : (2 * fibRoot p - 1 : FibRing p) = 2 * fibRoot p + (-1) := by ring
  rw [hrw, add_pow_char _ _ p, Odd.neg_one_pow hodd, mul_pow, two_pow_card_fibRing]
  ring

private lemma fibRoot_pow_card (hp0 : 0 < p) :
    fibRoot p ^ p = (Nat.fib p : FibRing p) * fibRoot p + Nat.fib (p - 1) := by
  have h := pow_succ_eq_fib_mul_add_fib (fibRoot_sq p) (p - 1)
  rwa [Nat.sub_add_cancel hp0] at h

/-- Compare the two expressions for `s ^ p`: an identity `c₁ α + c₀ = d₁ α + d₀`. -/
private lemma fib_coeff_eq (hodd : Odd p) (hp0 : 0 < p) :
    (2 * (Nat.fib p : FibRing p)) * fibRoot p + (2 * (Nat.fib (p - 1) : FibRing p) - 1)
      = (2 * (5 : FibRing p) ^ (p / 2)) * fibRoot p + (-((5 : FibRing p) ^ (p / 2))) := by
  have h := (fibS_pow_frobenius p hodd).symm.trans (fibS_pow_odd p hodd)
  rw [fibRoot_pow_card p hp0] at h
  linear_combination h

/-- `1, α` are linearly independent over `ZMod p`: coefficients are unique. -/
private lemma coeff_ext (c₁ c₀ : ZMod p)
    (h : algebraMap (ZMod p) (FibRing p) c₁ * fibRoot p
      + algebraMap (ZMod p) (FibRing p) c₀ = 0) :
    c₁ = 0 ∧ c₀ = 0 := by
  have hg : AdjoinRoot.mk (fibPoly p) (C c₁ * X + C c₀) = 0 := by
    rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
      ← AdjoinRoot.algebraMap_eq]
    exact h
  rw [AdjoinRoot.mk_eq_zero] at hg
  have h1 : (C c₁ * X + C c₀).natDegree ≤ 1 := by compute_degree
  have h2 : (fibPoly p).natDegree = 2 := by unfold fibPoly; compute_degree!
  have hz : (C c₁ * X + C c₀ : (ZMod p)[X]) = 0 :=
    eq_zero_of_dvd_of_natDegree_lt hg (by omega)
  constructor
  · simpa using congrArg (fun q => Polynomial.coeff q 1) hz
  · simpa using congrArg (fun q => Polynomial.coeff q 0) hz

private lemma two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  have hc : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hd)
  simpa using hc


/-- Cancel a factor `2` in `ZMod p` for `p ≠ 2`. -/
private lemma eq_zero_of_two_mul_eq_zero (hp2 : p ≠ 2) {x : ZMod p} (h : 2 * x = 0) : x = 0 := by
  have h2 := two_ne_zero_zmod p hp2
  calc x = (2⁻¹ * 2) * x := by rw [inv_mul_cancel₀ h2, one_mul]
    _ = 2⁻¹ * (2 * x) := by rw [mul_assoc]
    _ = 0 := by rw [h, mul_zero]

/-- The two congruences in terms of `5 ^ (p / 2)`. -/
private lemma fib_card_congr_aux (hp2 : p ≠ 2) :
    (Nat.fib p : ZMod p) = 5 ^ (p / 2) ∧ 2 * (Nat.fib (p - 1) : ZMod p) = 1 - 5 ^ (p / 2) := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hco := fib_coeff_eq p hodd hp.out.pos
  have hmapf : ∀ n : ℕ, (n : FibRing p) = algebraMap (ZMod p) (FibRing p) (n : ZMod p) := by
    intro n; rw [map_natCast]
  rw [hmapf (Nat.fib p), hmapf (Nat.fib (p - 1))] at hco
  have hzero : algebraMap (ZMod p) (FibRing p) (2 * (Nat.fib p : ZMod p) - 2 * 5 ^ (p / 2))
        * fibRoot p
      + algebraMap (ZMod p) (FibRing p) (2 * (Nat.fib (p - 1) : ZMod p) - 1 + 5 ^ (p / 2)) = 0 := by
    simp only [map_sub, map_add, map_mul, map_one, map_pow, map_ofNat]
    linear_combination hco
  obtain ⟨e1, e0⟩ := coeff_ext p _ _ hzero
  refine ⟨?_, by linear_combination e0⟩
  have hfac : (2 : ZMod p) * ((Nat.fib p : ZMod p) - 5 ^ (p / 2)) = 0 := by linear_combination e1
  exact sub_eq_zero.mp (eq_zero_of_two_mul_eq_zero p hp2 hfac)

end Aux

section Main

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Fibonacci numbers modulo a prime**: `F_p ≡ (5 / p) (mod p)` for every prime `p ≠ 2`. -/
theorem fib_cast_eq_legendreSym (hp2 : p ≠ 2) : (Nat.fib p : ZMod p) = legendreSym p 5 := by
  rw [(fib_card_congr_aux p hp2).1, legendreSym.eq_pow]
  norm_num

/-- `2 F_{p - 1} ≡ 1 - (5 / p) (mod p)` for every prime `p ≠ 2`. -/
theorem two_mul_fib_sub_one_cast (hp2 : p ≠ 2) :
    2 * (Nat.fib (p - 1) : ZMod p) = 1 - legendreSym p 5 := by
  rw [(fib_card_congr_aux p hp2).2, legendreSym.eq_pow]
  norm_num

/-- If `(5 / p) = 1` (i.e. `p ≡ ±1 (mod 5)`), then `p ∣ F_{p - 1}`. -/
theorem dvd_fib_sub_one_of_legendreSym_eq_one (hp2 : p ≠ 2) (h : legendreSym p 5 = 1) :
    p ∣ Nat.fib (p - 1) := by
  have h2 := two_mul_fib_sub_one_cast p hp2
  rw [h] at h2
  have hz : (2 : ZMod p) * (Nat.fib (p - 1) : ZMod p) = 0 := by
    rw [h2]; push_cast; ring
  exact (ZMod.natCast_eq_zero_iff _ _).mp (eq_zero_of_two_mul_eq_zero p hp2 hz)

/-- If `(5 / p) = -1` (i.e. `p ≡ ±2 (mod 5)`), then `p ∣ F_{p + 1}`. -/
theorem dvd_fib_add_one_of_legendreSym_eq_neg_one (hp2 : p ≠ 2) (h : legendreSym p 5 = -1) :
    p ∣ Nat.fib (p + 1) := by
  have h1 := fib_cast_eq_legendreSym p hp2
  have h2 := two_mul_fib_sub_one_cast p hp2
  rw [h] at h1 h2
  -- avoid the literal `-1` in `ZMod p`: rewrite everything as `_ + 1 = 0`.
  have hfp : (Nat.fib p : ZMod p) + 1 = 0 := by rw [h1]; push_cast; exact neg_add_cancel 1
  have hfp1 : (Nat.fib (p - 1) : ZMod p) = 1 := by
    have hz : (2 : ZMod p) * ((Nat.fib (p - 1) : ZMod p) - 1) = 0 := by
      rw [mul_sub, h2]; push_cast; ring
    exact sub_eq_zero.mp (eq_zero_of_two_mul_eq_zero p hp2 hz)
  have hsum : Nat.fib (p + 1) = Nat.fib (p - 1) + Nat.fib p := by
    have hp1 := hp.out.one_lt
    have ha : p - 1 + 2 = p + 1 := by omega
    have hb : p - 1 + 1 = p := by omega
    rw [← ha, Nat.fib_add_two, hb]
  have : (Nat.fib (p + 1) : ZMod p) = 0 := by
    rw [hsum]; push_cast
    linear_combination hfp1 + hfp
  exact (ZMod.natCast_eq_zero_iff _ _).mp this

end Main

section ModFive

/-- `5` is prime (as a `Fact`, for use with `legendreSym`). -/
instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private lemma legendreSym_five_eq_one_of_mod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h : p % 5 = 1 ∨ p % 5 = 4) : legendreSym p 5 = 1 := by
  change legendreSym p ((5 : ℕ) : ℤ) = 1
  rw [legendreSym.quadratic_reciprocity_one_mod_four (by norm_num) hp2, legendreSym.mod]
  have hmod : ((p : ℤ) % ((5 : ℕ) : ℤ)) = ((p % 5 : ℕ) : ℤ) := by norm_cast
  rw [hmod]
  rcases h with h | h <;> rw [h] <;> decide

private lemma legendreSym_five_eq_neg_one_of_mod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h : p % 5 = 2 ∨ p % 5 = 3) : legendreSym p 5 = -1 := by
  change legendreSym p ((5 : ℕ) : ℤ) = -1
  rw [legendreSym.quadratic_reciprocity_one_mod_four (by norm_num) hp2, legendreSym.mod]
  have hmod : ((p : ℤ) % ((5 : ℕ) : ℤ)) = ((p % 5 : ℕ) : ℤ) := by norm_cast
  rw [hmod]
  rcases h with h | h <;> rw [h] <;> decide

/-- If `p ≡ ±1 (mod 5)` is prime, then `p ∣ F_{p - 1}`. -/
theorem Prime.dvd_fib_sub_one_of_mod_five {p : ℕ} (hp : p.Prime) (h : p % 5 = 1 ∨ p % 5 = 4) :
    p ∣ Nat.fib (p - 1) := by
  have := Fact.mk hp
  have hp2 : p ≠ 2 := by rintro rfl; rcases h with h | h <;> norm_num at h
  exact dvd_fib_sub_one_of_legendreSym_eq_one p hp2 (legendreSym_five_eq_one_of_mod hp2 h)

/-- If `p ≡ ±2 (mod 5)` is prime, then `p ∣ F_{p + 1}`. -/
theorem Prime.dvd_fib_add_one_of_mod_five {p : ℕ} (hp : p.Prime) (h : p % 5 = 2 ∨ p % 5 = 3) :
    p ∣ Nat.fib (p + 1) := by
  have := Fact.mk hp
  by_cases hp2 : p = 2
  · subst hp2; decide
  exact dvd_fib_add_one_of_legendreSym_eq_neg_one p hp2 (legendreSym_five_eq_neg_one_of_mod hp2 h)

end ModFive

end Nat

end
