/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.CharP.Defs

/-!
# Invertibility of elements given a characteristic

This file includes some instances of `Invertible` for specific numbers in
characteristic zero. Some more cases are given as a `def`, to be included only
when needed. To construct instances for concrete numbers,
`invertibleOfNonzero` is a useful definition.
-/


variable {K : Type*}

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
