/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Int.Defs
import Mathlib.Tactic.Common

#align_import algebra.group_power.basic from "leanprover-community/mathlib"@"9b2660e1b25419042c8da10bf411aa3c67f14383"

/-!
# Power operations on monoids and groups

The power operation on monoids and groups.
We separate this from group, because it depends on `ℕ`,
which in turn depends on other parts of algebra.

This module contains lemmas about `a ^ n` and `n • a`, where `n : ℕ` or `n : ℤ`.
Further lemmas can be found in `Algebra.GroupPower.Ring`.

The analogous results for groups with zero can be found in `Algebra.GroupWithZero.Power`.

## Notation

- `a ^ n` is used as notation for `Pow.pow a n`; in this file `n : ℕ` or `n : ℤ`.
- `n • a` is used as notation for `SMul.smul n a`; in this file `n : ℕ` or `n : ℤ`.

## Implementation details

We adopt the convention that `0^0 = 1`.
-/

open scoped Int

universe u v w x y z u₁ u₂

variable {α : Type*} {M : Type u} {N : Type v} {G : Type w} {H : Type x} {A : Type y} {B : Type z}
  {R : Type u₁} {S : Type u₂}

/-!
### Commutativity

First we prove some facts about `SemiconjBy` and `Commute`. They do not require any theory about
`pow` and/or `nsmul` and will be useful later in this file.
-/

/-!
### Monoids
-/

section Monoid

variable [Monoid M] [AddMonoid A]

@[to_additive]
theorem Commute.mul_pow {a b : M} (h : Commute a b) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction' n with n ih
  · rw [pow_zero, pow_zero, pow_zero, one_mul]
  · simp only [pow_succ', ih, ← mul_assoc, (h.pow_left n).right_comm]
#align commute.mul_pow Commute.mul_pow
#align add_commute.add_nsmul AddCommute.add_nsmul

section Bit

set_option linter.deprecated false

@[to_additive bit0_nsmul]
theorem pow_bit0 (a : M) (n : ℕ) : a ^ bit0 n = a ^ n * a ^ n :=
  pow_add _ _ _
#align pow_bit0 pow_bit0
#align bit0_nsmul bit0_nsmul

@[to_additive bit1_nsmul]
theorem pow_bit1 (a : M) (n : ℕ) : a ^ bit1 n = a ^ n * a ^ n * a := by
  rw [bit1, pow_succ, pow_bit0]
#align pow_bit1 pow_bit1
#align bit1_nsmul bit1_nsmul

@[to_additive bit0_nsmul']
theorem pow_bit0' (a : M) (n : ℕ) : a ^ bit0 n = (a * a) ^ n := by
  rw [pow_bit0, (Commute.refl a).mul_pow]
#align pow_bit0' pow_bit0'
#align bit0_nsmul' bit0_nsmul'

@[to_additive bit1_nsmul']
theorem pow_bit1' (a : M) (n : ℕ) : a ^ bit1 n = (a * a) ^ n * a := by
  rw [bit1, pow_succ, pow_bit0']
#align pow_bit1' pow_bit1'
#align bit1_nsmul' bit1_nsmul'

end Bit
end Monoid

lemma eq_zero_or_one_of_sq_eq_self [CancelMonoidWithZero M] {x : M} (hx : x ^ 2 = x) :
    x = 0 ∨ x = 1 :=
  or_iff_not_imp_left.mpr (mul_left_injective₀ · <| by simpa [sq] using hx)

/-!
### Commutative (additive) monoid
-/

section DivisionMonoid

variable [DivisionMonoid α] {a b : α}

@[to_additive AddCommute.zsmul_add]
protected theorem Commute.mul_zpow (h : Commute a b) : ∀ i : ℤ, (a * b) ^ i = a ^ i * b ^ i
  | (n : ℕ)    => by simp [zpow_natCast, h.mul_pow n]
  | .negSucc n => by simp [h.mul_pow, (h.pow_pow _ _).eq, mul_inv_rev]
#align commute.mul_zpow Commute.mul_zpow
#align add_commute.zsmul_add AddCommute.zsmul_add

set_option linter.deprecated false

@[to_additive bit0_zsmul]
lemma zpow_bit0 (a : α) (n : ℤ) : a ^ bit0 n = a ^ n * a ^ n := by
  rw [bit0, ← Int.two_mul, zpow_mul', ← pow_two, ← zpow_natCast]; norm_cast
#align zpow_bit0 zpow_bit0
#align bit0_zsmul bit0_zsmul

@[to_additive bit0_zsmul']
theorem zpow_bit0' (a : α) (n : ℤ) : a ^ bit0 n = (a * a) ^ n :=
  (zpow_bit0 a n).trans ((Commute.refl a).mul_zpow n).symm
#align zpow_bit0' zpow_bit0'
#align bit0_zsmul' bit0_zsmul'

end DivisionMonoid

section Group

variable [Group G] [Group H] [AddGroup A] [AddGroup B]

@[to_additive]
theorem pow_inv_comm (a : G) (m n : ℕ) : a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m :=
  (Commute.refl a).inv_left.pow_pow _ _
#align pow_inv_comm pow_inv_comm
#align nsmul_neg_comm nsmul_neg_comm

section bit1

set_option linter.deprecated false

@[to_additive bit1_zsmul]
lemma zpow_bit1 (a : G) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a := by
  rw [bit1, zpow_add, zpow_bit0, zpow_one]
#align zpow_bit1 zpow_bit1
#align bit1_zsmul bit1_zsmul

end bit1

end Group

@[to_additive (attr := simp)]
theorem SemiconjBy.zpow_right [Group G] {a x y : G} (h : SemiconjBy a x y) :
    ∀ m : ℤ, SemiconjBy a (x ^ m) (y ^ m)
  | (n : ℕ)    => by simp [zpow_natCast, h.pow_right n]
  | .negSucc n => by
    simp only [zpow_negSucc, inv_right_iff]
    apply pow_right h
#align semiconj_by.zpow_right SemiconjBy.zpow_right
#align add_semiconj_by.zsmul_right AddSemiconjBy.zsmul_right

namespace Commute

variable [Group G] {a b : G}

@[to_additive (attr := simp)]
theorem zpow_right (h : Commute a b) (m : ℤ) : Commute a (b ^ m) :=
  SemiconjBy.zpow_right h m
#align commute.zpow_right Commute.zpow_right
#align add_commute.zsmul_right AddCommute.zsmul_right

@[to_additive (attr := simp)]
theorem zpow_left (h : Commute a b) (m : ℤ) : Commute (a ^ m) b :=
  (h.symm.zpow_right m).symm
#align commute.zpow_left Commute.zpow_left
#align add_commute.zsmul_left AddCommute.zsmul_left

@[to_additive]
theorem zpow_zpow (h : Commute a b) (m n : ℤ) : Commute (a ^ m) (b ^ n) :=
  (h.zpow_left m).zpow_right n
#align commute.zpow_zpow Commute.zpow_zpow
#align add_commute.zsmul_zsmul AddCommute.zsmul_zsmul

variable (a) (m n : ℤ)

@[to_additive]
theorem self_zpow : Commute a (a ^ n) :=
  (Commute.refl a).zpow_right n
#align commute.self_zpow Commute.self_zpow
#align add_commute.self_zsmul AddCommute.self_zsmul

@[to_additive]
theorem zpow_self : Commute (a ^ n) a :=
  (Commute.refl a).zpow_left n
#align commute.zpow_self Commute.zpow_self
#align add_commute.zsmul_self AddCommute.zsmul_self

@[to_additive]
theorem zpow_zpow_self : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).zpow_zpow m n
#align commute.zpow_zpow_self Commute.zpow_zpow_self
#align add_commute.zsmul_zsmul_self AddCommute.zsmul_zsmul_self

end Commute
