/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Data.Int.Dvd.Basic

/-!
# Characteristic of semirings

This file contains the definition of `CharP` expressing the characteristic of a
(semi)ring.

See also: `Mathlib.Algebra.CharZero.Defs`.

*Warning*: for a semiring `R`, `CharP R 0` and `CharZero R` need not coincide.
* `CharP R 0` asks that only `0 : ℕ` maps to `0 : R` under the map `ℕ → R`;
* `CharZero R` requires an injection `ℕ ↪ R`.
-/


universe u v

variable (R : Type*)

/-- The generator of the kernel of the unique homomorphism ℕ → R for a semiring R.

*Warning*: for a semiring `R`, `CharP R 0` and `CharZero R` need not coincide.
* `CharP R 0` asks that only `0 : ℕ` maps to `0 : R` under the map `ℕ → R`;
* `CharZero R` requires an injection `ℕ ↪ R`.

For instance, endowing `{0, 1}` with addition given by `max` (i.e. `1` is absorbing), shows that
`CharZero {0, 1}` does not hold and yet `CharP {0, 1} 0` does.
This example is formalized in `Counterexamples/CharPZeroNeCharZero.lean`.
-/
@[mk_iff]
class CharP [AddMonoidWithOne R] (p : ℕ) : Prop where
  cast_eq_zero_iff' : ∀ x : ℕ, (x : R) = 0 ↔ p ∣ x
#align char_p CharP
#align char_p_iff charP_iff

-- porting note: the field of the structure had implicit arguments where they were
-- explicit in Lean 3
theorem CharP.cast_eq_zero_iff (R : Type u) [AddMonoidWithOne R] (p : ℕ) [CharP R p] (x : ℕ) :
    (x : R) = 0 ↔ p ∣ x :=
CharP.cast_eq_zero_iff' (R := R) (p := p) x

@[simp]
theorem CharP.cast_eq_zero [AddMonoidWithOne R] (p : ℕ) [CharP R p] : (p : R) = 0 :=
  (CharP.cast_eq_zero_iff R p p).2 (dvd_refl p)
#align char_p.cast_eq_zero CharP.cast_eq_zero

theorem CharP.int_cast_eq_zero_iff [AddGroupWithOne R] (p : ℕ) [CharP R p] (a : ℤ) :
    (a : R) = 0 ↔ (p : ℤ) ∣ a := by
  rcases lt_trichotomy a 0 with (h | rfl | h)
  · rw [← neg_eq_zero, ← Int.cast_neg, ← dvd_neg]
    lift -a to ℕ using neg_nonneg.mpr (le_of_lt h) with b
    rw [Int.cast_ofNat, CharP.cast_eq_zero_iff R p, Int.coe_nat_dvd]
  · simp only [Int.cast_zero, eq_self_iff_true, dvd_zero]
  · lift a to ℕ using le_of_lt h with b
    rw [Int.cast_ofNat, CharP.cast_eq_zero_iff R p, Int.coe_nat_dvd]
#align char_p.int_cast_eq_zero_iff CharP.int_cast_eq_zero_iff

theorem CharP.intCast_eq_intCast_mod [AddGroupWithOne R] (p : ℕ) [CharP R p] {a : ℤ} :
    (a : R) = a % (p : ℤ) := by
  rw [← sub_eq_zero, ← Int.cast_sub, CharP.int_cast_eq_zero_iff R p]
  exact Int.dvd_sub_of_emod_eq rfl

theorem CharP.natCast_eq_natCast_mod [AddMonoidWithOne R] (p : ℕ) [CharP R p] {a : ℕ} :
    (a : R) = a % p := by
  conv_lhs => rw [← Nat.add_sub_cancel' (Nat.mod_le a p), Nat.cast_add,
    (CharP.cast_eq_zero_iff R p _).mpr (Nat.dvd_sub_mod _), add_zero]

-- This file will be used in the implementation of the `ring` tactic,
-- so we assert it has not been imported to avoid circular dependencies.
assert_not_exists Mathlib.Tactic.Ring.proveEq
