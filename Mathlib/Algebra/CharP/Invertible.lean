/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Cast.Commute

/-!
# Invertibility of elements given a characteristic

This file includes some instances of `Invertible` for specific numbers in
characteristic zero. Some more cases are given as a `def`, to be included only
when needed. To construct instances for concrete numbers,
`invertibleOfNonzero` is a useful definition.
-/


variable {R K : Type*}

section Ring
variable [Ring R] {p : ℕ} [CharP R p]

theorem CharP.intCast_mul_natCast_gcdA {n : ℕ} (hp : p.Prime) (not_dvd : ¬p ∣ n) :
    (n * n.gcdA p : R) = 1 := by
  suffices ↑(n * n.gcdA p + p * n.gcdB p : ℤ) = (1 : R) by simpa using this
  rw [← Nat.Prime.coprime_iff_not_dvd hp, Nat.coprime_comm] at not_dvd
  rw [← Nat.gcd_eq_gcd_ab, not_dvd, Nat.cast_one, Int.cast_one]

theorem CharP.natCast_gcdA_mul_intCast {n : ℕ} (hp : p.Prime) (not_dvd : ¬p ∣ n) :
    (n.gcdA p * n : R) = 1 :=
  Nat.commute_cast _ _ |>.eq.trans <| CharP.intCast_mul_natCast_gcdA hp not_dvd

/-- In a ring of characteristic `p` where `p` is prime, `(n : R)` is invertible when `n` is not
a multiple of `p`, with inverse `n.gcdA p`. -/
def invertibleOfPrimeCharPNotDvd {n : ℕ} (hp : p.Prime) (not_dvd : ¬p ∣ n) :
    Invertible (n : R) where
  invOf := n.gcdA p
  invOf_mul_self := CharP.natCast_gcdA_mul_intCast hp not_dvd
  mul_invOf_self := CharP.intCast_mul_natCast_gcdA hp not_dvd

theorem CharP.isUnit_natCast_iff {n : ℕ} (hp : p.Prime) : IsUnit (n : R) ↔ ¬p ∣ n where
  mp h := by
    have := CharP.nontrivial_of_char_ne_one (R := R) hp.ne_one
    rw [← CharP.cast_eq_zero_iff (R := R)]
    exact h.ne_zero
  mpr not_dvd := letI := invertibleOfPrimeCharPNotDvd (R := R) hp not_dvd; isUnit_of_invertible _

theorem CharP.isUnit_ofNat_iff {n : ℕ} [n.AtLeastTwo] (hp : p.Prime) :
    IsUnit (ofNat(n) : R) ↔ ¬p ∣ ofNat(n) :=
  CharP.isUnit_natCast_iff hp

theorem CharP.isUnit_intCast_iff {z : ℤ} (hp : p.Prime) : IsUnit (z : R) ↔ ¬↑p ∣ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simp [CharP.isUnit_natCast_iff hp, Int.ofNat_dvd]
  · simp [CharP.isUnit_natCast_iff hp, Int.dvd_neg, Int.ofNat_dvd]

end Ring

section Field

variable [Field K]

/-- A natural number `t` is invertible in a field `K` if the characteristic of `K` does not divide
`t`. -/
def invertibleOfRingCharNotDvd {t : ℕ} (not_dvd : ¬ringChar K ∣ t) : Invertible (t : K) :=
  invertibleOfNonzero fun h => not_dvd ((ringChar.spec K t).mp h)

theorem not_ringChar_dvd_of_invertible {t : ℕ} [Invertible (t : K)] : ¬ringChar K ∣ t := by
  rw [← ringChar.spec, ← Ne]
  exact Invertible.ne_zero (t : K)

/-- A natural number `t` is invertible in a field `K` of characteristic `p` if `p` does not divide
`t`. -/
def invertibleOfCharPNotDvd {p : ℕ} [CharP K p] {t : ℕ} (not_dvd : ¬p ∣ t) : Invertible (t : K) :=
  invertibleOfNonzero fun h => not_dvd ((CharP.cast_eq_zero_iff K p t).mp h)

-- warning: this could potentially loop with `Invertible.ne_zero` - if there is weird type-class
-- loops, watch out for that.
instance invertibleOfPos [CharZero K] (n : ℕ) [NeZero n] : Invertible (n : K) :=
  invertibleOfNonzero <| NeZero.out

end Field

section DivisionRing

variable [DivisionRing K] [CharZero K]

instance invertibleSucc (n : ℕ) : Invertible (n.succ : K) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))

/-!
A few `Invertible n` instances for small numerals `n`. Feel free to add your own
number when you need its inverse.
-/


instance invertibleTwo : Invertible (2 : K) :=
  invertibleOfNonzero (mod_cast (by decide : 2 ≠ 0))

instance invertibleThree : Invertible (3 : K) :=
  invertibleOfNonzero (mod_cast (by decide : 3 ≠ 0))

end DivisionRing
