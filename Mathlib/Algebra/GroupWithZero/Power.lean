/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.GroupPower.Lemmas
import Mathlib.Data.Int.Bitwise

#align_import algebra.group_with_zero.power from "leanprover-community/mathlib"@"46a64b5b4268c594af770c44d9e502afc6a515cb"

/-!
# Powers of elements of groups with an adjoined zero element

In this file we define integer power functions for groups with an adjoined zero element.
This generalises the integer power function on a division ring.
-/


section GroupWithZero

variable {G₀ : Type*} [GroupWithZero G₀] {a : G₀} {m n : ℕ}

section NatPow

theorem pow_sub₀ (a : G₀) {m n : ℕ} (ha : a ≠ 0) (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  have h1 : m - n + n = m := tsub_add_cancel_of_le h
  -- ⊢ a ^ (m - n) = a ^ m * (a ^ n)⁻¹
  have h2 : a ^ (m - n) * a ^ n = a ^ m := by rw [← pow_add, h1]
  -- ⊢ a ^ (m - n) = a ^ m * (a ^ n)⁻¹
  simpa only [div_eq_mul_inv] using eq_div_of_mul_eq (pow_ne_zero _ ha) h2
  -- 🎉 no goals
#align pow_sub₀ pow_sub₀

theorem pow_sub_of_lt (a : G₀) {m n : ℕ} (h : n < m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  -- ⊢ 0 ^ (m - n) = 0 ^ m * (0 ^ n)⁻¹
  · rw [zero_pow (tsub_pos_of_lt h), zero_pow (n.zero_le.trans_lt h), zero_mul]
    -- 🎉 no goals
  · exact pow_sub₀ _ ha h.le
    -- 🎉 no goals
#align pow_sub_of_lt pow_sub_of_lt

theorem pow_inv_comm₀ (a : G₀) (m n : ℕ) : a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m :=
  (Commute.refl a).inv_left₀.pow_pow m n
#align pow_inv_comm₀ pow_inv_comm₀

theorem inv_pow_sub₀ (ha : a ≠ 0) (h : n ≤ m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub₀ _ (inv_ne_zero ha) h, inv_pow, inv_pow, inv_inv]
  -- 🎉 no goals
#align inv_pow_sub₀ inv_pow_sub₀

theorem inv_pow_sub_of_lt (a : G₀) (h : n < m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub_of_lt a⁻¹ h, inv_pow, inv_pow, inv_inv]
  -- 🎉 no goals
#align inv_pow_sub_of_lt inv_pow_sub_of_lt

end NatPow

end GroupWithZero

section ZPow

open Int

variable {G₀ : Type*} [GroupWithZero G₀]

-- Porting note: removed `attribute [local ematch] le_of_lt`

theorem zero_zpow : ∀ z : ℤ, z ≠ 0 → (0 : G₀) ^ z = 0
  | (n : ℕ), h => by
    rw [zpow_ofNat, zero_pow']
    -- ⊢ n ≠ 0
    simpa using h
    -- 🎉 no goals
  | -[n+1], _ => by simp
                    -- 🎉 no goals
#align zero_zpow zero_zpow

theorem zero_zpow_eq (n : ℤ) : (0 : G₀) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  -- ⊢ 0 ^ n = 1
  · rw [h, zpow_zero]
    -- 🎉 no goals
  · rw [zero_zpow _ h]
    -- 🎉 no goals
#align zero_zpow_eq zero_zpow_eq

theorem zpow_add_one₀ {a : G₀} (ha : a ≠ 0) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
  | (n : ℕ) => by simp only [← Int.ofNat_succ, zpow_ofNat, pow_succ']
                  -- 🎉 no goals
  | -[0+1] => by erw [zpow_zero, zpow_negSucc, pow_one, inv_mul_cancel ha]
                 -- 🎉 no goals
  | -[n + 1+1] => by
    rw [Int.negSucc_eq, zpow_neg, neg_add, neg_add_cancel_right, zpow_neg, ← Int.ofNat_succ,
      zpow_ofNat, zpow_ofNat, pow_succ _ (n + 1), mul_inv_rev, mul_assoc, inv_mul_cancel ha,
      mul_one]
#align zpow_add_one₀ zpow_add_one₀

theorem zpow_sub_one₀ {a : G₀} (ha : a ≠ 0) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
  calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := by rw [mul_assoc, mul_inv_cancel ha, mul_one]
                                              -- 🎉 no goals
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one₀ ha, sub_add_cancel]
                          -- 🎉 no goals
#align zpow_sub_one₀ zpow_sub_one₀

theorem zpow_add₀ {a : G₀} (ha : a ≠ 0) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction' n using Int.induction_on with n ihn n ihn
  · simp
    -- 🎉 no goals
  · simp only [← add_assoc, zpow_add_one₀ ha, ihn, mul_assoc]
    -- 🎉 no goals
  · rw [zpow_sub_one₀ ha, ← mul_assoc, ← ihn, ← zpow_sub_one₀ ha, add_sub_assoc]
    -- 🎉 no goals
#align zpow_add₀ zpow_add₀

theorem zpow_add' {a : G₀} {m n : ℤ} (h : a ≠ 0 ∨ m + n ≠ 0 ∨ m = 0 ∧ n = 0) :
    a ^ (m + n) = a ^ m * a ^ n := by
  by_cases hm : m = 0
  -- ⊢ a ^ (m + n) = a ^ m * a ^ n
  · simp [hm]
    -- 🎉 no goals
  by_cases hn : n = 0
  -- ⊢ a ^ (m + n) = a ^ m * a ^ n
  · simp [hn]
    -- 🎉 no goals
  by_cases ha : a = 0
  -- ⊢ a ^ (m + n) = a ^ m * a ^ n
  · subst a
    -- ⊢ 0 ^ (m + n) = 0 ^ m * 0 ^ n
    simp only [false_or_iff, eq_self_iff_true, not_true, Ne.def, hm, hn, false_and_iff,
      or_false_iff] at h
    rw [zero_zpow _ h, zero_zpow _ hm, zero_mul]
    -- 🎉 no goals
  · exact zpow_add₀ ha m n
    -- 🎉 no goals
#align zpow_add' zpow_add'

theorem zpow_one_add₀ {a : G₀} (h : a ≠ 0) (i : ℤ) : a ^ (1 + i) = a * a ^ i := by
  rw [zpow_add₀ h, zpow_one]
  -- 🎉 no goals
#align zpow_one_add₀ zpow_one_add₀

theorem SemiconjBy.zpow_right₀ {a x y : G₀} (h : SemiconjBy a x y) :
    ∀ m : ℤ, SemiconjBy a (x ^ m) (y ^ m)
  | (n : ℕ) => by simp [h.pow_right n]
                  -- 🎉 no goals
  | -[n+1] => by simp only [zpow_negSucc, (h.pow_right (n + 1)).inv_right₀]
                 -- 🎉 no goals
#align semiconj_by.zpow_right₀ SemiconjBy.zpow_right₀

theorem Commute.zpow_right₀ {a b : G₀} (h : Commute a b) : ∀ m : ℤ, Commute a (b ^ m) :=
  SemiconjBy.zpow_right₀ h
#align commute.zpow_right₀ Commute.zpow_right₀

theorem Commute.zpow_left₀ {a b : G₀} (h : Commute a b) (m : ℤ) : Commute (a ^ m) b :=
  (h.symm.zpow_right₀ m).symm
#align commute.zpow_left₀ Commute.zpow_left₀

theorem Commute.zpow_zpow₀ {a b : G₀} (h : Commute a b) (m n : ℤ) : Commute (a ^ m) (b ^ n) :=
  (h.zpow_left₀ m).zpow_right₀ n
#align commute.zpow_zpow₀ Commute.zpow_zpow₀

theorem Commute.zpow_self₀ (a : G₀) (n : ℤ) : Commute (a ^ n) a :=
  (Commute.refl a).zpow_left₀ n
#align commute.zpow_self₀ Commute.zpow_self₀

theorem Commute.self_zpow₀ (a : G₀) (n : ℤ) : Commute a (a ^ n) :=
  (Commute.refl a).zpow_right₀ n
#align commute.self_zpow₀ Commute.self_zpow₀

theorem Commute.zpow_zpow_self₀ (a : G₀) (m n : ℤ) : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).zpow_zpow₀ m n
#align commute.zpow_zpow_self₀ Commute.zpow_zpow_self₀

set_option linter.deprecated false in
theorem zpow_bit1₀ (a : G₀) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a := by
  rw [← zpow_bit0, bit1, zpow_add', zpow_one]
  -- ⊢ a ≠ 0 ∨ bit0 n + 1 ≠ 0 ∨ bit0 n = 0 ∧ 1 = 0
  right; left
  -- ⊢ bit0 n + 1 ≠ 0 ∨ bit0 n = 0 ∧ 1 = 0
         -- ⊢ bit0 n + 1 ≠ 0
  apply bit1_ne_zero
  -- 🎉 no goals
#align zpow_bit1₀ zpow_bit1₀

theorem zpow_ne_zero_of_ne_zero {a : G₀} (ha : a ≠ 0) : ∀ z : ℤ, a ^ z ≠ 0
  | (_ : ℕ) => by
    rw [zpow_ofNat]
    -- ⊢ a ^ a✝ ≠ 0
    exact pow_ne_zero _ ha
    -- 🎉 no goals
  | -[_+1] => by
    rw [zpow_negSucc]
    -- ⊢ (a ^ (a✝ + 1))⁻¹ ≠ 0
    exact inv_ne_zero (pow_ne_zero _ ha)
    -- 🎉 no goals
#align zpow_ne_zero_of_ne_zero zpow_ne_zero_of_ne_zero

theorem zpow_sub₀ {a : G₀} (ha : a ≠ 0) (z1 z2 : ℤ) : a ^ (z1 - z2) = a ^ z1 / a ^ z2 := by
  rw [sub_eq_add_neg, zpow_add₀ ha, zpow_neg, div_eq_mul_inv]
  -- 🎉 no goals
#align zpow_sub₀ zpow_sub₀

set_option linter.deprecated false in
theorem zpow_bit1' (a : G₀) (n : ℤ) : a ^ bit1 n = (a * a) ^ n * a := by
  rw [zpow_bit1₀, (Commute.refl a).mul_zpow]
  -- 🎉 no goals
#align zpow_bit1' zpow_bit1'

theorem zpow_eq_zero {x : G₀} {n : ℤ} (h : x ^ n = 0) : x = 0 :=
  by_contradiction fun hx => zpow_ne_zero_of_ne_zero hx n h
#align zpow_eq_zero zpow_eq_zero

theorem zpow_eq_zero_iff {a : G₀} {n : ℤ} (hn : n ≠ 0) : a ^ n = 0 ↔ a = 0 :=
  ⟨zpow_eq_zero, fun ha => ha.symm ▸ zero_zpow _ hn⟩
#align zpow_eq_zero_iff zpow_eq_zero_iff

theorem zpow_ne_zero {x : G₀} (n : ℤ) : x ≠ 0 → x ^ n ≠ 0 :=
  mt zpow_eq_zero
#align zpow_ne_zero zpow_ne_zero

theorem zpow_neg_mul_zpow_self (n : ℤ) {x : G₀} (h : x ≠ 0) : x ^ (-n) * x ^ n = 1 := by
  rw [zpow_neg]
  -- ⊢ (x ^ n)⁻¹ * x ^ n = 1
  exact inv_mul_cancel (zpow_ne_zero n h)
  -- 🎉 no goals
#align zpow_neg_mul_zpow_self zpow_neg_mul_zpow_self

end ZPow

section

variable {G₀ : Type*} [CommGroupWithZero G₀]

theorem div_sq_cancel (a b : G₀) : a ^ 2 * b / a = a * b := by
  by_cases ha : a = 0
  -- ⊢ a ^ 2 * b / a = a * b
  · simp [ha]
    -- 🎉 no goals
  rw [sq, mul_assoc, mul_div_cancel_left _ ha]
  -- 🎉 no goals
#align div_sq_cancel div_sq_cancel

end

/-- If a monoid homomorphism `f` between two `GroupWithZero`s maps `0` to `0`, then it maps `x^n`,
`n : ℤ`, to `(f x)^n`. -/
@[simp]
theorem map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZero G₀']
    [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n : ℤ) : f (x ^ n) = f x ^ n :=
  map_zpow' f (map_inv₀ f) x n
#align map_zpow₀ map_zpow₀
