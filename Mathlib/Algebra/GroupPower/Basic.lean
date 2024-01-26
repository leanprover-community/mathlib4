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

open Int

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

theorem nsmul_zero (n : ℕ) : n • (0 : A) = 0 := by
  induction' n with n ih
  · exact zero_nsmul _
  · rw [succ_nsmul, ih, add_zero]
#align nsmul_zero nsmul_zero

@[simp]
theorem one_nsmul (a : A) : 1 • a = a := by rw [succ_nsmul, zero_nsmul, add_zero]
#align one_nsmul one_nsmul

theorem add_nsmul (a : A) (m n : ℕ) : (m + n) • a = m • a + n • a := by
  induction m with
  | zero => rw [Nat.zero_add, zero_nsmul, zero_add]
  | succ m ih => rw [Nat.succ_add, Nat.succ_eq_add_one, succ_nsmul, ih, succ_nsmul, add_assoc]
#align add_nsmul add_nsmul

-- the attributes are intentionally out of order.
@[to_additive existing nsmul_zero, simp]
theorem one_pow (n : ℕ) : (1 : M) ^ n = 1 := by
  induction' n with n ih
  · exact pow_zero _
  · rw [pow_succ, ih, one_mul]
#align one_pow one_pow

@[to_additive existing (attr := simp) one_nsmul]
theorem pow_one (a : M) : a ^ 1 = a := by rw [pow_succ, pow_zero, mul_one]
#align pow_one pow_one

/-- Note that most of the lemmas about powers of two refer to it as `sq`. -/
@[to_additive two_nsmul ""]
theorem pow_two (a : M) : a ^ 2 = a * a := by rw [pow_succ, pow_one]
#align pow_two pow_two
#align two_nsmul two_nsmul

alias sq := pow_two
#align sq sq

@[to_additive three'_nsmul]
theorem pow_three' (a : M) : a ^ 3 = a * a * a := by rw [pow_succ', pow_two]
#align pow_three' pow_three'

@[to_additive three_nsmul]
theorem pow_three (a : M) : a ^ 3 = a * (a * a) := by rw [pow_succ, pow_two]
#align pow_three pow_three

@[to_additive existing add_nsmul]
theorem pow_add (a : M) (m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction' n with n ih
  · rw [Nat.add_zero, pow_zero, mul_one]
  · rw [pow_succ', ← mul_assoc, ← ih, ← pow_succ', Nat.add_assoc]
#align pow_add pow_add

@[to_additive mul_nsmul]
theorem pow_mul (a : M) (m n : ℕ) : a ^ (m * n) = (a ^ m) ^ n := by
  induction' n with n ih
  · rw [Nat.mul_zero, pow_zero, pow_zero]
  · rw [Nat.mul_succ, pow_add, pow_succ', ih]
-- Porting note: we are taking the opportunity to swap the names `mul_nsmul` and `mul_nsmul'`
-- using #align, so that in mathlib4 they will match the multiplicative ones.
#align pow_mul pow_mul
#align mul_nsmul' mul_nsmul

@[to_additive mul_nsmul']
theorem pow_mul' (a : M) (m n : ℕ) : a ^ (m * n) = (a ^ n) ^ m := by rw [Nat.mul_comm, pow_mul]
#align pow_mul' pow_mul'
#align mul_nsmul mul_nsmul'

@[to_additive]
theorem Commute.mul_pow {a b : M} (h : Commute a b) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction' n with n ih
  · rw [pow_zero, pow_zero, pow_zero, one_mul]
  · simp only [pow_succ, ih, ← mul_assoc, (h.pow_left n).right_comm]
#align commute.mul_pow Commute.mul_pow
#align add_commute.add_nsmul AddCommute.add_nsmul

@[to_additive]
theorem pow_mul_comm' (a : M) (n : ℕ) : a ^ n * a = a * a ^ n :=
  Commute.pow_self a n
#align pow_mul_comm' pow_mul_comm'
#align nsmul_add_comm' nsmul_add_comm'

@[to_additive boole_nsmul]
theorem pow_boole (P : Prop) [Decidable P] (a : M) :
    (a ^ if P then 1 else 0) = if P then a else 1 := by simp
#align pow_boole pow_boole

@[to_additive nsmul_left_comm]
theorem pow_right_comm (a : M) (m n : ℕ) : (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
#align pow_right_comm pow_right_comm
#align nsmul_left_comm nsmul_left_comm

@[to_additive nsmul_add_sub_nsmul]
theorem pow_mul_pow_sub (a : M) {m n : ℕ} (h : m ≤ n) : a ^ m * a ^ (n - m) = a ^ n := by
  rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h]
#align pow_mul_pow_sub pow_mul_pow_sub
#align nsmul_add_sub_nsmul nsmul_add_sub_nsmul

@[to_additive sub_nsmul_nsmul_add]
theorem pow_sub_mul_pow (a : M) {m n : ℕ} (h : m ≤ n) : a ^ (n - m) * a ^ m = a ^ n := by
  rw [← pow_add, Nat.sub_add_cancel h]
#align pow_sub_mul_pow pow_sub_mul_pow
#align sub_nsmul_nsmul_add sub_nsmul_nsmul_add

/-- If `x ^ n = 1`, then `x ^ m` is the same as `x ^ (m % n)` -/
@[to_additive nsmul_eq_mod_nsmul "If `n • x = 0`, then `m • x` is the same as `(m % n) • x`"]
theorem pow_eq_pow_mod {M : Type*} [Monoid M] {x : M} (m : ℕ) {n : ℕ} (h : x ^ n = 1) :
    x ^ m = x ^ (m % n) := by
  have t : x ^ m = x ^ (n * (m / n) + m % n) :=
    congr_arg (fun a => x ^ a) ((Nat.add_comm _ _).trans (Nat.mod_add_div _ _)).symm
  rw [t, pow_add, pow_mul, h, one_pow, one_mul]
#align pow_eq_pow_mod pow_eq_pow_mod
#align nsmul_eq_mod_nsmul nsmul_eq_mod_nsmul

@[to_additive]
theorem pow_mul_comm (a : M) (m n : ℕ) : a ^ m * a ^ n = a ^ n * a ^ m :=
  Commute.pow_pow_self a m n
#align pow_mul_comm pow_mul_comm
#align nsmul_add_comm nsmul_add_comm

section Bit

set_option linter.deprecated false

@[to_additive bit0_nsmul]
theorem pow_bit0 (a : M) (n : ℕ) : a ^ bit0 n = a ^ n * a ^ n :=
  pow_add _ _ _
#align pow_bit0 pow_bit0
#align bit0_nsmul bit0_nsmul

@[to_additive bit1_nsmul]
theorem pow_bit1 (a : M) (n : ℕ) : a ^ bit1 n = a ^ n * a ^ n * a := by
  rw [bit1, pow_succ', pow_bit0]
#align pow_bit1 pow_bit1
#align bit1_nsmul bit1_nsmul

@[to_additive bit0_nsmul']
theorem pow_bit0' (a : M) (n : ℕ) : a ^ bit0 n = (a * a) ^ n := by
  rw [pow_bit0, (Commute.refl a).mul_pow]
#align pow_bit0' pow_bit0'
#align bit0_nsmul' bit0_nsmul'

@[to_additive bit1_nsmul']
theorem pow_bit1' (a : M) (n : ℕ) : a ^ bit1 n = (a * a) ^ n * a := by
  rw [bit1, pow_succ', pow_bit0']
#align pow_bit1' pow_bit1'
#align bit1_nsmul' bit1_nsmul'

end Bit

@[to_additive]
theorem pow_mul_pow_eq_one {a b : M} (n : ℕ) (h : a * b = 1) : a ^ n * b ^ n = 1 := by
  induction' n with n hn
  · simp
  · calc
      a ^ n.succ * b ^ n.succ = a ^ n * a * (b * b ^ n) := by rw [pow_succ', pow_succ]
      _ = a ^ n * (a * b) * b ^ n := by simp only [mul_assoc]
      _ = 1 := by simp [h, hn]
#align pow_mul_pow_eq_one pow_mul_pow_eq_one
#align nsmul_add_nsmul_eq_zero nsmul_add_nsmul_eq_zero

end Monoid

lemma eq_zero_or_one_of_sq_eq_self [CancelMonoidWithZero M] {x : M} (hx : x ^ 2 = x) :
    x = 0 ∨ x = 1 :=
  or_iff_not_imp_left.mpr (mul_left_injective₀ · <| by simpa [sq] using hx)

/-!
### Commutative (additive) monoid
-/

section CommMonoid
variable [CommMonoid M]

@[to_additive nsmul_add]
theorem mul_pow (a b : M) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n :=
  (Commute.all a b).mul_pow n
#align mul_pow mul_pow
#align nsmul_add nsmul_add

end CommMonoid

section DivInvMonoid

variable [DivInvMonoid G]

open Int

@[to_additive (attr := simp) one_zsmul]
theorem zpow_one (a : G) : a ^ (1 : ℤ) = a := by
  convert pow_one a using 1
  exact zpow_ofNat a 1
#align zpow_one zpow_one
#align one_zsmul one_zsmul

@[to_additive two_zsmul]
theorem zpow_two (a : G) : a ^ (2 : ℤ) = a * a := by
  convert pow_two a using 1
  exact zpow_ofNat a 2
#align zpow_two zpow_two
#align two_zsmul two_zsmul

@[to_additive neg_one_zsmul]
theorem zpow_neg_one (x : G) : x ^ (-1 : ℤ) = x⁻¹ :=
  (zpow_negSucc x 0).trans <| congr_arg Inv.inv (pow_one x)
#align zpow_neg_one zpow_neg_one
#align neg_one_zsmul neg_one_zsmul

@[to_additive]
theorem zpow_neg_coe_of_pos (a : G) : ∀ {n : ℕ}, 0 < n → a ^ (-(n : ℤ)) = (a ^ n)⁻¹
  | _ + 1, _ => zpow_negSucc _ _
#align zpow_neg_coe_of_pos zpow_neg_coe_of_pos
#align zsmul_neg_coe_of_pos zsmul_neg_coe_of_pos

end DivInvMonoid

section DivisionMonoid

variable [DivisionMonoid α] {a b : α}

@[to_additive (attr := simp)]
theorem inv_pow (a : α) : ∀ n : ℕ, a⁻¹ ^ n = (a ^ n)⁻¹
  | 0 => by rw [pow_zero, pow_zero, inv_one]
  | n + 1 => by rw [pow_succ', pow_succ, inv_pow _ n, mul_inv_rev]
#align inv_pow inv_pow
#align neg_nsmul neg_nsmul

-- the attributes are intentionally out of order. `smul_zero` proves `zsmul_zero`.
@[to_additive zsmul_zero, simp]
theorem one_zpow : ∀ n : ℤ, (1 : α) ^ n = 1
  | (n : ℕ)       => by rw [zpow_ofNat, one_pow]
  | .negSucc n => by rw [zpow_negSucc, one_pow, inv_one]
#align one_zpow one_zpow
#align zsmul_zero zsmul_zero

@[to_additive (attr := simp) neg_zsmul]
theorem zpow_neg (a : α) : ∀ n : ℤ, a ^ (-n) = (a ^ n)⁻¹
  | (n + 1 : ℕ) => DivInvMonoid.zpow_neg' _ _
  | 0 => by
    change a ^ (0 : ℤ) = (a ^ (0 : ℤ))⁻¹
    simp
  | Int.negSucc n => by
    rw [zpow_negSucc, inv_inv, ← zpow_ofNat]
    rfl
#align zpow_neg zpow_neg
#align neg_zsmul neg_zsmul

@[to_additive neg_one_zsmul_add]
theorem mul_zpow_neg_one (a b : α) : (a * b) ^ (-1 : ℤ) = b ^ (-1 : ℤ) * a ^ (-1 : ℤ) := by
  simp only [zpow_neg, zpow_one, mul_inv_rev]
#align mul_zpow_neg_one mul_zpow_neg_one
#align neg_one_zsmul_add neg_one_zsmul_add

@[to_additive zsmul_neg]
theorem inv_zpow (a : α) : ∀ n : ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
  | (n : ℕ)    => by rw [zpow_ofNat, zpow_ofNat, inv_pow]
  | .negSucc n => by rw [zpow_negSucc, zpow_negSucc, inv_pow]
#align inv_zpow inv_zpow
#align zsmul_neg zsmul_neg

@[to_additive (attr := simp) zsmul_neg']
theorem inv_zpow' (a : α) (n : ℤ) : a⁻¹ ^ n = a ^ (-n) := by rw [inv_zpow, zpow_neg]
#align inv_zpow' inv_zpow'
#align zsmul_neg' zsmul_neg'

@[to_additive nsmul_zero_sub]
theorem one_div_pow (a : α) (n : ℕ) : (1 / a) ^ n = 1 / a ^ n := by simp only [one_div, inv_pow]
#align one_div_pow one_div_pow
#align nsmul_zero_sub nsmul_zero_sub

@[to_additive zsmul_zero_sub]
theorem one_div_zpow (a : α) (n : ℤ) : (1 / a) ^ n = 1 / a ^ n := by simp only [one_div, inv_zpow]
#align one_div_zpow one_div_zpow
#align zsmul_zero_sub zsmul_zero_sub

@[to_additive AddCommute.zsmul_add]
protected theorem Commute.mul_zpow (h : Commute a b) : ∀ i : ℤ, (a * b) ^ i = a ^ i * b ^ i
  | (n : ℕ)    => by simp [zpow_ofNat, h.mul_pow n]
  | .negSucc n => by simp [h.mul_pow, (h.pow_pow _ _).eq, mul_inv_rev]
#align commute.mul_zpow Commute.mul_zpow
#align add_commute.zsmul_add AddCommute.zsmul_add

-- Note that `mul_zsmul` and `zpow_mul` have the primes swapped
-- when additivised since their argument order,
-- and therefore the more "natural" choice of lemma, is reversed.
@[to_additive mul_zsmul'] lemma zpow_mul (a : α) : ∀ m n : ℤ, a ^ (m * n) = (a ^ m) ^ n
  | (m : ℕ), (n : ℕ) => by
    rw [zpow_ofNat, zpow_ofNat, ← pow_mul, ← zpow_ofNat]
    rfl
  | (m : ℕ), -[n+1] => by
    rw [zpow_ofNat, zpow_negSucc, ← pow_mul, ofNat_mul_negSucc, zpow_neg, inv_inj, ← zpow_ofNat]
  | -[m+1], (n : ℕ) => by
    rw [zpow_ofNat, zpow_negSucc, ← inv_pow, ← pow_mul, negSucc_mul_ofNat, zpow_neg, inv_pow,
      inv_inj, ← zpow_ofNat]
  | -[m+1], -[n+1] => by
    rw [zpow_negSucc, zpow_negSucc, negSucc_mul_negSucc, inv_pow, inv_inv, ← pow_mul, ←
      zpow_ofNat]
    rfl
#align zpow_mul zpow_mul
#align mul_zsmul' mul_zsmul'

@[to_additive mul_zsmul]
lemma zpow_mul' (a : α) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m := by rw [Int.mul_comm, zpow_mul]
#align zpow_mul' zpow_mul'
#align mul_zsmul mul_zsmul

set_option linter.deprecated false

@[to_additive bit0_zsmul]
lemma zpow_bit0 (a : α) (n : ℤ) : a ^ bit0 n = a ^ n * a ^ n := by
  rw [bit0, ← Int.two_mul, zpow_mul', ← pow_two, ← zpow_coe_nat]; norm_cast
#align zpow_bit0 zpow_bit0
#align bit0_zsmul bit0_zsmul

@[to_additive bit0_zsmul']
theorem zpow_bit0' (a : α) (n : ℤ) : a ^ bit0 n = (a * a) ^ n :=
  (zpow_bit0 a n).trans ((Commute.refl a).mul_zpow n).symm
#align zpow_bit0' zpow_bit0'
#align bit0_zsmul' bit0_zsmul'

end DivisionMonoid

section DivisionCommMonoid

variable [DivisionCommMonoid α]

@[to_additive zsmul_add]
theorem mul_zpow (a b : α) : ∀ n : ℤ, (a * b) ^ n = a ^ n * b ^ n :=
  (Commute.all a b).mul_zpow
#align mul_zpow mul_zpow
#align zsmul_add zsmul_add

@[to_additive (attr := simp) nsmul_sub]
theorem div_pow (a b : α) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n := by
  simp only [div_eq_mul_inv, mul_pow, inv_pow]
#align div_pow div_pow
#align nsmul_sub nsmul_sub

@[to_additive (attr := simp) zsmul_sub]
theorem div_zpow (a b : α) (n : ℤ) : (a / b) ^ n = a ^ n / b ^ n := by
  simp only [div_eq_mul_inv, mul_zpow, inv_zpow]
#align div_zpow div_zpow
#align zsmul_sub zsmul_sub

end DivisionCommMonoid

section Group

variable [Group G] [Group H] [AddGroup A] [AddGroup B]

@[to_additive sub_nsmul]
theorem pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ :=
  eq_mul_inv_of_mul_eq <| by rw [← pow_add, Nat.sub_add_cancel h]
#align pow_sub pow_sub
#align sub_nsmul sub_nsmul

@[to_additive]
theorem pow_inv_comm (a : G) (m n : ℕ) : a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m :=
  (Commute.refl a).inv_left.pow_pow _ _
#align pow_inv_comm pow_inv_comm
#align nsmul_neg_comm nsmul_neg_comm

@[to_additive sub_nsmul_neg]
theorem inv_pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub a⁻¹ h, inv_pow, inv_pow, inv_inv]
#align inv_pow_sub inv_pow_sub
#align sub_nsmul_neg sub_nsmul_neg

@[to_additive add_one_zsmul]
lemma zpow_add_one (a : G) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
  | (n : ℕ) => by simp only [← Int.ofNat_succ, zpow_ofNat, pow_succ']
  | -[0+1] => by erw [zpow_zero, zpow_negSucc, pow_one, mul_left_inv]
  | -[n + 1+1] => by
    rw [zpow_negSucc, pow_succ, mul_inv_rev, inv_mul_cancel_right]
    rw [Int.negSucc_eq, Int.neg_add, Int.neg_add_cancel_right]
    exact zpow_negSucc _ _
#align zpow_add_one zpow_add_one
#align add_one_zsmul add_one_zsmul

@[to_additive sub_one_zsmul]
lemma zpow_sub_one (a : G) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
  calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := (mul_inv_cancel_right _ _).symm
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one, Int.sub_add_cancel]
#align zpow_sub_one zpow_sub_one
#align sub_one_zsmul sub_one_zsmul

@[to_additive add_zsmul]
lemma zpow_add (a : G) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n using Int.induction_on with
  | hz => simp
  | hp n ihn => simp only [← Int.add_assoc, zpow_add_one, ihn, mul_assoc]
  | hn n ihn => rw [zpow_sub_one, ← mul_assoc, ← ihn, ← zpow_sub_one, Int.add_sub_assoc]
#align zpow_add zpow_add
#align add_zsmul add_zsmul

@[to_additive one_add_zsmul]
lemma zpow_one_add (a : G) (n : ℤ) : a ^ (1 + n) = a * a ^ n := by rw [zpow_add, zpow_one]
#align zpow_one_add zpow_one_add
#align one_add_zsmul one_add_zsmul

@[to_additive add_zsmul_self]
lemma mul_self_zpow (a : G) (n : ℤ) : a * a ^ n = a ^ (n + 1) := by
  rw [Int.add_comm, zpow_add, zpow_one]
#align mul_self_zpow mul_self_zpow
#align add_zsmul_self add_zsmul_self

@[to_additive add_self_zsmul]
lemma mul_zpow_self (a : G) (n : ℤ) : a ^ n * a = a ^ (n + 1) := (zpow_add_one ..).symm
#align mul_zpow_self mul_zpow_self
#align add_self_zsmul add_self_zsmul

@[to_additive sub_zsmul] lemma zpow_sub (a : G) (m n : ℤ) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  rw [Int.sub_eq_add_neg, zpow_add, zpow_neg]
#align zpow_sub zpow_sub
#align sub_zsmul sub_zsmul

@[to_additive] lemma zpow_mul_comm (a : G) (m n : ℤ) : a ^ m * a ^ n = a ^ n * a ^ m := by
  rw [← zpow_add, Int.add_comm, zpow_add]
#align zpow_mul_comm zpow_mul_comm
#align zsmul_add_comm zsmul_add_comm

@[to_additive (attr := simp) abs_zsmul_eq_zero_iff]
theorem zpow_abs_eq_one_iff (a : G) (i : ℤ) : a ^ |i| = 1 ↔ a ^ i = 1 := by
  cases abs_cases i with
  | inl h => rw [h.1]
  | inr h => rw [h.1, zpow_neg, inv_eq_one]

@[to_additive (attr := simp) natAbs_nsmul_eq_zero_iff]
theorem pow_natAbs_eq_one_iff (a : G) (i : ℤ) : a ^ Int.natAbs i = 1 ↔ a ^ i = 1 := by
  rw [← zpow_ofNat, Int.coe_natAbs, zpow_abs_eq_one_iff]

section bit1

set_option linter.deprecated false

@[to_additive bit1_zsmul]
lemma zpow_bit1 (a : G) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a := by
  rw [bit1, zpow_add, zpow_bit0, zpow_one]
#align zpow_bit1 zpow_bit1
#align bit1_zsmul bit1_zsmul

end bit1

/-- To show a property of all powers of `g` it suffices to show it is closed under multiplication
by `g` and `g⁻¹` on the left. For subgroups generated by more than one element, see
`Subgroup.closure_induction_left`. -/
@[to_additive "To show a property of all multiples of `g` it suffices to show it is closed under
addition by `g` and `-g` on the left. For additive subgroups generated by more than one element, see
`AddSubgroup.closure_induction_left`."]
lemma zpow_induction_left {g : G} {P : G → Prop} (h_one : P (1 : G))
    (h_mul : ∀ a, P a → P (g * a)) (h_inv : ∀ a, P a → P (g⁻¹ * a)) (n : ℤ) : P (g ^ n) := by
  induction' n using Int.induction_on with n ih n ih
  · rwa [zpow_zero]
  · rw [Int.add_comm, zpow_add, zpow_one]
    exact h_mul _ ih
  · rw [Int.sub_eq_add_neg, Int.add_comm, zpow_add, zpow_neg_one]
    exact h_inv _ ih
#align zpow_induction_left zpow_induction_left
#align zsmul_induction_left zsmul_induction_left

/-- To show a property of all powers of `g` it suffices to show it is closed under multiplication
by `g` and `g⁻¹` on the right. For subgroups generated by more than one element, see
`Subgroup.closure_induction_right`. -/
@[to_additive "To show a property of all multiples of `g` it suffices to show it is closed under
addition by `g` and `-g` on the right. For additive subgroups generated by more than one element,
see `AddSubgroup.closure_induction_right`."]
lemma zpow_induction_right {g : G} {P : G → Prop} (h_one : P (1 : G))
    (h_mul : ∀ a, P a → P (a * g)) (h_inv : ∀ a, P a → P (a * g⁻¹)) (n : ℤ) : P (g ^ n) := by
  induction' n using Int.induction_on with n ih n ih
  · rwa [zpow_zero]
  · rw [zpow_add_one]
    exact h_mul _ ih
  · rw [zpow_sub_one]
    exact h_inv _ ih
#align zpow_induction_right zpow_induction_right
#align zsmul_induction_right zsmul_induction_right

end Group

@[to_additive (attr := simp)]
theorem SemiconjBy.zpow_right [Group G] {a x y : G} (h : SemiconjBy a x y) :
    ∀ m : ℤ, SemiconjBy a (x ^ m) (y ^ m)
  | (n : ℕ)    => by simp [zpow_ofNat, h.pow_right n]
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
