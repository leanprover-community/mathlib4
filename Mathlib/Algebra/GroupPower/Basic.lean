/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Commute
import Mathlib.Algebra.Group.TypeTags

#align_import algebra.group_power.basic from "leanprover-community/mathlib"@"9b2660e1b25419042c8da10bf411aa3c67f14383"

/-!
# Power operations on monoids and groups

The power operation on monoids and groups.
We separate this from group, because it depends on `ℕ`,
which in turn depends on other parts of algebra.

This module contains lemmas about `a ^ n` and `n • a`, where `n : ℕ` or `n : ℤ`.
Further lemmas can be found in `Algebra.GroupPower.Lemmas`.

The analogous results for groups with zero can be found in `Algebra.GroupWithZero.Power`.

## Notation

- `a ^ n` is used as notation for `Pow.pow a n`; in this file `n : ℕ` or `n : ℤ`.
- `n • a` is used as notation for `SMul.smul n a`; in this file `n : ℕ` or `n : ℤ`.

## Implementation details

We adopt the convention that `0^0 = 1`.
-/

universe u v w x y z u₁ u₂

variable {α : Type*} {M : Type u} {N : Type v} {G : Type w} {H : Type x} {A : Type y} {B : Type z}
  {R : Type u₁} {S : Type u₂}

/-!
### Commutativity

First we prove some facts about `SemiconjBy` and `Commute`. They do not require any theory about
`pow` and/or `nsmul` and will be useful later in this file.
-/


section Pow

variable [Pow M ℕ]

@[to_additive (attr := simp) ite_nsmul]
theorem pow_ite (P : Prop) [Decidable P] (a : M) (b c : ℕ) :
    (a ^ if P then b else c) = if P then a ^ b else a ^ c := by split_ifs <;> rfl
                                                                -- ⊢ a ^ b = a ^ b
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
#align pow_ite pow_ite

@[to_additive (attr := simp) nsmul_ite]
theorem ite_pow (P : Prop) [Decidable P] (a b : M) (c : ℕ) :
    (if P then a else b) ^ c = if P then a ^ c else b ^ c := by split_ifs <;> rfl
                                                                -- ⊢ a ^ c = a ^ c
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
#align ite_pow ite_pow

end Pow


/-!
### Monoids
-/

section Monoid

variable [Monoid M] [AddMonoid A]

theorem nsmul_zero (n : ℕ) : n • (0 : A) = 0 := by
  induction' n with n ih
  -- ⊢ Nat.zero • 0 = 0
  · exact zero_nsmul _
    -- 🎉 no goals
  · rw [succ_nsmul, ih, add_zero]
    -- 🎉 no goals
#align nsmul_zero nsmul_zero

@[simp]
theorem one_nsmul (a : A) : 1 • a = a := by rw [succ_nsmul, zero_nsmul, add_zero]
                                            -- 🎉 no goals
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
  -- ⊢ 1 ^ Nat.zero = 1
  · exact pow_zero _
    -- 🎉 no goals
  · rw [pow_succ, ih, one_mul]
    -- 🎉 no goals
#align one_pow one_pow

@[to_additive existing (attr := simp) one_nsmul]
theorem pow_one (a : M) : a ^ 1 = a := by rw [pow_succ, pow_zero, mul_one]
                                          -- 🎉 no goals
#align pow_one pow_one

/-- Note that most of the lemmas about powers of two refer to it as `sq`. -/
@[to_additive two_nsmul ""]
theorem pow_two (a : M) : a ^ 2 = a * a := by rw [pow_succ, pow_one]
                                              -- 🎉 no goals
#align pow_two pow_two
#align two_nsmul two_nsmul

alias sq := pow_two
#align sq sq

@[to_additive three'_nsmul]
theorem pow_three' (a : M) : a ^ 3 = a * a * a := by rw [pow_succ', pow_two]
                                                     -- 🎉 no goals
#align pow_three' pow_three'

@[to_additive three_nsmul]
theorem pow_three (a : M) : a ^ 3 = a * (a * a) := by rw [pow_succ, pow_two]
                                                      -- 🎉 no goals
#align pow_three pow_three

@[to_additive existing add_nsmul]
theorem pow_add (a : M) (m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction' n with n ih
  -- ⊢ a ^ (m + Nat.zero) = a ^ m * a ^ Nat.zero
  · rw [Nat.add_zero, pow_zero, mul_one]
    -- 🎉 no goals
  · rw [pow_succ', ← mul_assoc, ← ih, ← pow_succ', Nat.add_assoc]
    -- 🎉 no goals
#align pow_add pow_add

@[to_additive mul_nsmul]
theorem pow_mul (a : M) (m n : ℕ) : a ^ (m * n) = (a ^ m) ^ n := by
  induction' n with n ih
  -- ⊢ a ^ (m * Nat.zero) = (a ^ m) ^ Nat.zero
  · rw [Nat.mul_zero, pow_zero, pow_zero]
    -- 🎉 no goals
  · rw [Nat.mul_succ, pow_add, pow_succ', ih]
    -- 🎉 no goals
-- Porting note: we are taking the opportunity to swap the names `mul_nsmul` and `mul_nsmul'`
-- using #align, so that in mathlib4 they will match the multiplicative ones.
#align pow_mul pow_mul
#align mul_nsmul' mul_nsmul

@[to_additive mul_nsmul']
theorem pow_mul' (a : M) (m n : ℕ) : a ^ (m * n) = (a ^ n) ^ m := by rw [Nat.mul_comm, pow_mul]
                                                                     -- 🎉 no goals
#align pow_mul' pow_mul'
#align mul_nsmul mul_nsmul'

@[to_additive]
theorem Commute.mul_pow {a b : M} (h : Commute a b) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction' n with n ih
  -- ⊢ (a * b) ^ Nat.zero = a ^ Nat.zero * b ^ Nat.zero
  · rw [pow_zero, pow_zero, pow_zero, one_mul]
    -- 🎉 no goals
  · simp only [pow_succ, ih, ← mul_assoc, (h.pow_left n).right_comm]
    -- 🎉 no goals
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
                                                        -- 🎉 no goals
#align pow_boole pow_boole

@[to_additive nsmul_left_comm]
theorem pow_right_comm (a : M) (m n : ℕ) : (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  -- 🎉 no goals
#align pow_right_comm pow_right_comm
#align nsmul_left_comm nsmul_left_comm

@[to_additive nsmul_add_sub_nsmul]
theorem pow_mul_pow_sub (a : M) {m n : ℕ} (h : m ≤ n) : a ^ m * a ^ (n - m) = a ^ n := by
  rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h]
  -- 🎉 no goals
#align pow_mul_pow_sub pow_mul_pow_sub
#align nsmul_add_sub_nsmul nsmul_add_sub_nsmul

@[to_additive sub_nsmul_nsmul_add]
theorem pow_sub_mul_pow (a : M) {m n : ℕ} (h : m ≤ n) : a ^ (n - m) * a ^ m = a ^ n := by
  rw [← pow_add, Nat.sub_add_cancel h]
  -- 🎉 no goals
#align pow_sub_mul_pow pow_sub_mul_pow
#align sub_nsmul_nsmul_add sub_nsmul_nsmul_add

/-- If `x ^ n = 1`, then `x ^ m` is the same as `x ^ (m % n)` -/
@[to_additive nsmul_eq_mod_nsmul "If `n • x = 0`, then `m • x` is the same as `(m % n) • x`"]
theorem pow_eq_pow_mod {M : Type*} [Monoid M] {x : M} (m : ℕ) {n : ℕ} (h : x ^ n = 1) :
    x ^ m = x ^ (m % n) := by
  have t : x ^ m = x ^ (n * (m / n) + m % n) :=
    congr_arg (fun a => x ^ a) ((Nat.add_comm _ _).trans (Nat.mod_add_div _ _)).symm
  rw [t, pow_add, pow_mul, h, one_pow, one_mul]
  -- 🎉 no goals
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
  -- 🎉 no goals
#align pow_bit1 pow_bit1
#align bit1_nsmul bit1_nsmul

@[to_additive bit0_nsmul']
theorem pow_bit0' (a : M) (n : ℕ) : a ^ bit0 n = (a * a) ^ n := by
  rw [pow_bit0, (Commute.refl a).mul_pow]
  -- 🎉 no goals
#align pow_bit0' pow_bit0'
#align bit0_nsmul' bit0_nsmul'

@[to_additive bit1_nsmul']
theorem pow_bit1' (a : M) (n : ℕ) : a ^ bit1 n = (a * a) ^ n * a := by
  rw [bit1, pow_succ', pow_bit0']
  -- 🎉 no goals
#align pow_bit1' pow_bit1'
#align bit1_nsmul' bit1_nsmul'

end Bit

@[to_additive]
theorem pow_mul_pow_eq_one {a b : M} (n : ℕ) (h : a * b = 1) : a ^ n * b ^ n = 1 := by
  induction' n with n hn
  -- ⊢ a ^ Nat.zero * b ^ Nat.zero = 1
  · simp
    -- 🎉 no goals
  · calc
      a ^ n.succ * b ^ n.succ = a ^ n * a * (b * b ^ n) := by rw [pow_succ', pow_succ]
      _ = a ^ n * (a * b) * b ^ n := by simp only [mul_assoc]
      _ = 1 := by simp [h, hn]
#align pow_mul_pow_eq_one pow_mul_pow_eq_one
#align nsmul_add_nsmul_eq_zero nsmul_add_nsmul_eq_zero

theorem dvd_pow {x y : M} (hxy : x ∣ y) : ∀ {n : ℕ} (_ : n ≠ 0), x ∣ y ^ n
  | 0,     hn => (hn rfl).elim
  | n + 1, _  => by
    rw [pow_succ]
    -- ⊢ x ∣ y * y ^ n
    exact hxy.mul_right _
    -- 🎉 no goals
#align dvd_pow dvd_pow

alias Dvd.dvd.pow := dvd_pow

theorem dvd_pow_self (a : M) {n : ℕ} (hn : n ≠ 0) : a ∣ a ^ n :=
  dvd_rfl.pow hn
#align dvd_pow_self dvd_pow_self

end Monoid

/-!
### Commutative (additive) monoid
-/

section CommMonoid

variable [CommMonoid M] [AddCommMonoid A]

@[to_additive nsmul_add]
theorem mul_pow (a b : M) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n :=
  (Commute.all a b).mul_pow n
#align mul_pow mul_pow
#align nsmul_add nsmul_add

/-- The `n`th power map on a commutative monoid for a natural `n`, considered as a morphism of
monoids. -/
@[to_additive (attr := simps)
      "Multiplication by a natural `n` on a commutative additive
       monoid, considered as a morphism of additive monoids."]
def powMonoidHom (n : ℕ) : M →* M where
  toFun := (· ^ n)
  map_one' := one_pow _
  map_mul' a b := mul_pow a b n
#align pow_monoid_hom powMonoidHom
#align nsmul_add_monoid_hom nsmulAddMonoidHom
#align pow_monoid_hom_apply powMonoidHom_apply
#align nsmul_add_monoid_hom_apply nsmulAddMonoidHom_apply

end CommMonoid

section DivInvMonoid

variable [DivInvMonoid G]

open Int

@[to_additive (attr := simp) one_zsmul]
theorem zpow_one (a : G) : a ^ (1 : ℤ) = a := by
  convert pow_one a using 1
  -- ⊢ a ^ 1 = a ^ 1
  exact zpow_ofNat a 1
  -- 🎉 no goals
#align zpow_one zpow_one
#align one_zsmul one_zsmul

@[to_additive two_zsmul]
theorem zpow_two (a : G) : a ^ (2 : ℤ) = a * a := by
  convert pow_two a using 1
  -- ⊢ a ^ 2 = a ^ 2
  exact zpow_ofNat a 2
  -- 🎉 no goals
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
            -- 🎉 no goals
  | n + 1 => by rw [pow_succ', pow_succ, inv_pow _ n, mul_inv_rev]
                -- 🎉 no goals
#align inv_pow inv_pow
#align neg_nsmul neg_nsmul

-- the attributes are intentionally out of order. `smul_zero` proves `zsmul_zero`.
@[to_additive zsmul_zero, simp]
theorem one_zpow : ∀ n : ℤ, (1 : α) ^ n = 1
  | (n : ℕ)       => by rw [zpow_ofNat, one_pow]
                        -- 🎉 no goals
  | .negSucc n => by rw [zpow_negSucc, one_pow, inv_one]
                     -- 🎉 no goals
#align one_zpow one_zpow
#align zsmul_zero zsmul_zero

@[to_additive (attr := simp) neg_zsmul]
theorem zpow_neg (a : α) : ∀ n : ℤ, a ^ (-n) = (a ^ n)⁻¹
  | (n + 1 : ℕ) => DivInvMonoid.zpow_neg' _ _
  | 0 => by
    change a ^ (0 : ℤ) = (a ^ (0 : ℤ))⁻¹
    -- ⊢ a ^ 0 = (a ^ 0)⁻¹
    simp
    -- 🎉 no goals
  | Int.negSucc n => by
    rw [zpow_negSucc, inv_inv, ← zpow_ofNat]
    -- ⊢ a ^ (-Int.negSucc n) = a ^ ↑(n + 1)
    rfl
    -- 🎉 no goals
#align zpow_neg zpow_neg
#align neg_zsmul neg_zsmul

@[to_additive neg_one_zsmul_add]
theorem mul_zpow_neg_one (a b : α) : (a * b) ^ (-1 : ℤ) = b ^ (-1 : ℤ) * a ^ (-1 : ℤ) := by
  simp only [zpow_neg, zpow_one, mul_inv_rev]
  -- 🎉 no goals
#align mul_zpow_neg_one mul_zpow_neg_one
#align neg_one_zsmul_add neg_one_zsmul_add

@[to_additive zsmul_neg]
theorem inv_zpow (a : α) : ∀ n : ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
  | (n : ℕ)    => by rw [zpow_ofNat, zpow_ofNat, inv_pow]
                     -- 🎉 no goals
  | .negSucc n => by rw [zpow_negSucc, zpow_negSucc, inv_pow]
                     -- 🎉 no goals
#align inv_zpow inv_zpow
#align zsmul_neg zsmul_neg

@[to_additive (attr := simp) zsmul_neg']
theorem inv_zpow' (a : α) (n : ℤ) : a⁻¹ ^ n = a ^ (-n) := by rw [inv_zpow, zpow_neg]
                                                             -- 🎉 no goals
#align inv_zpow' inv_zpow'
#align zsmul_neg' zsmul_neg'

@[to_additive nsmul_zero_sub]
theorem one_div_pow (a : α) (n : ℕ) : (1 / a) ^ n = 1 / a ^ n := by simp only [one_div, inv_pow]
                                                                    -- 🎉 no goals
#align one_div_pow one_div_pow
#align nsmul_zero_sub nsmul_zero_sub

@[to_additive zsmul_zero_sub]
theorem one_div_zpow (a : α) (n : ℤ) : (1 / a) ^ n = 1 / a ^ n := by simp only [one_div, inv_zpow]
                                                                     -- 🎉 no goals
#align one_div_zpow one_div_zpow
#align zsmul_zero_sub zsmul_zero_sub

@[to_additive AddCommute.zsmul_add]
protected theorem Commute.mul_zpow (h : Commute a b) : ∀ i : ℤ, (a * b) ^ i = a ^ i * b ^ i
  | (n : ℕ)    => by simp [zpow_ofNat, h.mul_pow n]
                     -- 🎉 no goals
  | .negSucc n => by simp [h.mul_pow, (h.pow_pow _ _).eq, mul_inv_rev]
                     -- 🎉 no goals
#align commute.mul_zpow Commute.mul_zpow
#align add_commute.zsmul_add AddCommute.zsmul_add

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
  -- 🎉 no goals
#align div_pow div_pow
#align nsmul_sub nsmul_sub

@[to_additive (attr := simp) zsmul_sub]
theorem div_zpow (a b : α) (n : ℤ) : (a / b) ^ n = a ^ n / b ^ n := by
  simp only [div_eq_mul_inv, mul_zpow, inv_zpow]
  -- 🎉 no goals
#align div_zpow div_zpow
#align zsmul_sub zsmul_sub

/-- The `n`-th power map (for an integer `n`) on a commutative group, considered as a group
homomorphism. -/
@[to_additive (attr := simps)
      "Multiplication by an integer `n` on a commutative additive group, considered as an
       additive group homomorphism."]
def zpowGroupHom (n : ℤ) : α →* α where
  toFun := (· ^ n)
  map_one' := one_zpow n
  map_mul' a b := mul_zpow a b n
#align zpow_group_hom zpowGroupHom
#align zsmul_add_group_hom zsmulAddGroupHom
#align zpow_group_hom_apply zpowGroupHom_apply
#align zsmul_add_group_hom_apply zsmulAddGroupHom_apply

end DivisionCommMonoid

section Group

variable [Group G] [Group H] [AddGroup A] [AddGroup B]

@[to_additive sub_nsmul]
theorem pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ :=
  eq_mul_inv_of_mul_eq <| by rw [← pow_add, Nat.sub_add_cancel h]
                             -- 🎉 no goals
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
  -- 🎉 no goals
#align inv_pow_sub inv_pow_sub
#align sub_nsmul_neg sub_nsmul_neg

end Group

theorem pow_dvd_pow [Monoid R] (a : R) {m n : ℕ} (h : m ≤ n) : a ^ m ∣ a ^ n :=
  ⟨a ^ (n - m), by rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h]⟩
                   -- 🎉 no goals
#align pow_dvd_pow pow_dvd_pow

theorem ofAdd_nsmul [AddMonoid A] (x : A) (n : ℕ) :
    Multiplicative.ofAdd (n • x) = Multiplicative.ofAdd x ^ n :=
  rfl
#align of_add_nsmul ofAdd_nsmul

theorem ofAdd_zsmul [SubNegMonoid A] (x : A) (n : ℤ) :
    Multiplicative.ofAdd (n • x) = Multiplicative.ofAdd x ^ n :=
  rfl
#align of_add_zsmul ofAdd_zsmul

theorem ofMul_pow [Monoid A] (x : A) (n : ℕ) : Additive.ofMul (x ^ n) = n • Additive.ofMul x :=
  rfl
#align of_mul_pow ofMul_pow

theorem ofMul_zpow [DivInvMonoid G] (x : G) (n : ℤ) :
    Additive.ofMul (x ^ n) = n • Additive.ofMul x :=
  rfl
#align of_mul_zpow ofMul_zpow

@[to_additive (attr := simp)]
theorem SemiconjBy.zpow_right [Group G] {a x y : G} (h : SemiconjBy a x y) :
    ∀ m : ℤ, SemiconjBy a (x ^ m) (y ^ m)
  | (n : ℕ)    => by simp [zpow_ofNat, h.pow_right n]
                     -- 🎉 no goals
  | .negSucc n => by
    simp only [zpow_negSucc, inv_right_iff]
    -- ⊢ SemiconjBy a (x ^ (n + 1)) (y ^ (n + 1))
    apply pow_right h
    -- 🎉 no goals
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
