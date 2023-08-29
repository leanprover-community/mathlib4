/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.Algebra.Invertible
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Algebra.GroupPower.Ring
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.Nat.Pow
import Mathlib.Data.Int.Cast.Lemmas

#align_import algebra.group_power.lemmas from "leanprover-community/mathlib"@"a07d750983b94c530ab69a726862c2ab6802b38c"

/-!
# Lemmas about power operations on monoids and groups

This file contains lemmas about `Monoid.pow`, `Group.pow`, `nsmul`, and `zsmul`
which require additional imports besides those available in `Mathlib.Algebra.GroupPower.Basic`.
-/

open Int

universe u v w x y z u₁ u₂

variable {α : Type*} {M : Type u} {N : Type v} {G : Type w} {H : Type x} {A : Type y} {B : Type z}
  {R : Type u₁} {S : Type u₂}

/-!
### (Additive) monoid
-/

section Monoid

@[simp]
theorem nsmul_one [AddMonoidWithOne A] : ∀ n : ℕ, n • (1 : A) = n := by
  let f : ℕ →+ A :=
  { toFun := fun n ↦ n • (1 : A),
    map_zero' := by simp [zero_nsmul],
    map_add' := by simp [add_nsmul] }
  refine' eq_natCast' f _
  -- ⊢ ↑f 1 = 1
  simp
  -- 🎉 no goals
#align nsmul_one nsmul_one

variable [Monoid M] [Monoid N] [AddMonoid A] [AddMonoid B]

instance invertiblePow (m : M) [Invertible m] (n : ℕ) :
    Invertible (m ^ n) where
  invOf := ⅟ m ^ n
  invOf_mul_self := by rw [← (commute_invOf m).symm.mul_pow, invOf_mul_self, one_pow]
                       -- 🎉 no goals
  mul_invOf_self := by rw [← (commute_invOf m).mul_pow, mul_invOf_self, one_pow]
                       -- 🎉 no goals
#align invertible_pow invertiblePow

theorem invOf_pow (m : M) [Invertible m] (n : ℕ) [Invertible (m ^ n)] : ⅟ (m ^ n) = ⅟ m ^ n :=
  @invertible_unique M _ (m ^ n) (m ^ n) _ (invertiblePow m n) rfl
#align inv_of_pow invOf_pow

@[to_additive]
theorem IsUnit.pow {m : M} (n : ℕ) : IsUnit m → IsUnit (m ^ n) := fun ⟨u, hu⟩ =>
  ⟨u ^ n, hu ▸ u.val_pow_eq_pow_val _⟩
#align is_unit.pow IsUnit.pow
#align is_add_unit.nsmul IsAddUnit.nsmul

/-- If a natural power of `x` is a unit, then `x` is a unit. -/
@[to_additive "If a natural multiple of `x` is an additive unit, then `x` is an additive unit."]
def Units.ofPow (u : Mˣ) (x : M) {n : ℕ} (hn : n ≠ 0) (hu : x ^ n = u) : Mˣ :=
  u.leftOfMul x (x ^ (n - 1))
    (by rwa [← _root_.pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt <| Nat.pos_of_ne_zero hn)])
        -- 🎉 no goals
    (Commute.self_pow _ _)
#align units.of_pow Units.ofPow
#align add_units.of_nsmul AddUnits.ofNSMul

@[to_additive (attr := simp)]
theorem isUnit_pow_iff {a : M} {n : ℕ} (hn : n ≠ 0) : IsUnit (a ^ n) ↔ IsUnit a :=
  ⟨fun ⟨u, hu⟩ => (u.ofPow a hn hu.symm).isUnit, fun h => h.pow n⟩
#align is_unit_pow_iff isUnit_pow_iff
#align is_add_unit_nsmul_iff isAddUnit_nsmul_iff

@[to_additive]
theorem isUnit_pow_succ_iff {m : M} {n : ℕ} : IsUnit (m ^ (n + 1)) ↔ IsUnit m :=
  isUnit_pow_iff n.succ_ne_zero
#align is_unit_pow_succ_iff isUnit_pow_succ_iff
#align is_add_unit_nsmul_succ_iff isAddUnit_nsmul_succ_iff

/-- If `x ^ n = 1`, `n ≠ 0`, then `x` is a unit. -/
@[to_additive (attr := simps!) "If `n • x = 0`, `n ≠ 0`, then `x` is an additive unit."]
def Units.ofPowEqOne (x : M) (n : ℕ) (hx : x ^ n = 1) (hn : n ≠ 0) : Mˣ :=
  Units.ofPow 1 x hn hx
#align units.of_pow_eq_one Units.ofPowEqOne
#align add_units.of_nsmul_eq_zero AddUnits.ofNSMulEqZero

@[to_additive (attr := simp)]
theorem Units.pow_ofPowEqOne {x : M} {n : ℕ} (hx : x ^ n = 1) (hn : n ≠ 0) :
    Units.ofPowEqOne x n hx hn ^ n = 1 :=
  Units.ext <| by simp [hx]
                  -- 🎉 no goals
#align units.pow_of_pow_eq_one Units.pow_ofPowEqOne
#align add_units.nsmul_of_nsmul_eq_zero AddUnits.nsmul_ofNSMulEqZero

@[to_additive]
theorem isUnit_ofPowEqOne {x : M} {n : ℕ} (hx : x ^ n = 1) (hn : n ≠ 0) : IsUnit x :=
  (Units.ofPowEqOne x n hx hn).isUnit
#align is_unit_of_pow_eq_one isUnit_ofPowEqOne
#align is_add_unit_of_nsmul_eq_zero isAddUnit_ofNSMulEqZero

/-- If `x ^ n = 1` then `x` has an inverse, `x^(n - 1)`. -/
def invertibleOfPowEqOne (x : M) (n : ℕ) (hx : x ^ n = 1) (hn : n ≠ 0) : Invertible x :=
  (Units.ofPowEqOne x n hx hn).invertible
#align invertible_of_pow_eq_one invertibleOfPowEqOne

theorem smul_pow [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N] (k : M) (x : N)
    (p : ℕ) : (k • x) ^ p = k ^ p • x ^ p := by
  induction' p with p IH
  -- ⊢ (k • x) ^ Nat.zero = k ^ Nat.zero • x ^ Nat.zero
  · simp
    -- 🎉 no goals
  · rw [pow_succ', IH, smul_mul_smul, ← pow_succ', ← pow_succ']
    -- 🎉 no goals
#align smul_pow smul_pow

@[simp]
theorem smul_pow' [MulDistribMulAction M N] (x : M) (m : N) (n : ℕ) : x • m ^ n = (x • m) ^ n := by
  induction' n with n ih
  -- ⊢ x • m ^ Nat.zero = (x • m) ^ Nat.zero
  · rw [pow_zero, pow_zero]
    -- ⊢ x • 1 = 1
    exact smul_one x
    -- 🎉 no goals
  · rw [pow_succ, pow_succ]
    -- ⊢ x • (m * m ^ n) = x • m * (x • m) ^ n
    exact (smul_mul' x m (m ^ n)).trans (congr_arg _ ih)
    -- 🎉 no goals
#align smul_pow' smul_pow'

end Monoid

@[simp]
theorem zsmul_one [AddGroupWithOne A] (n : ℤ) : n • (1 : A) = n := by cases n <;> simp
                                                                      -- ⊢ ofNat a✝ • 1 = ↑(ofNat a✝)
                                                                                  -- 🎉 no goals
                                                                                  -- 🎉 no goals
#align zsmul_one zsmul_one

section DivisionMonoid

variable [DivisionMonoid α]

-- Note that `mul_zsmul` and `zpow_mul` have the primes swapped
-- when additivised since their argument order,
-- and therefore the more "natural" choice of lemma, is reversed.
@[to_additive mul_zsmul']
theorem zpow_mul (a : α) : ∀ m n : ℤ, a ^ (m * n) = (a ^ m) ^ n
  | (m : ℕ), (n : ℕ) => by
    rw [zpow_ofNat, zpow_ofNat, ← pow_mul, ← zpow_ofNat]
    -- ⊢ a ^ (↑m * ↑n) = a ^ ↑(m * n)
    rfl
    -- 🎉 no goals
  | (m : ℕ), -[n+1] => by
    rw [zpow_ofNat, zpow_negSucc, ← pow_mul, ofNat_mul_negSucc, zpow_neg, inv_inj, ← zpow_ofNat]
    -- 🎉 no goals
  | -[m+1], (n : ℕ) => by
    rw [zpow_ofNat, zpow_negSucc, ← inv_pow, ← pow_mul, negSucc_mul_ofNat, zpow_neg, inv_pow,
      inv_inj, ← zpow_ofNat]
  | -[m+1], -[n+1] => by
    rw [zpow_negSucc, zpow_negSucc, negSucc_mul_negSucc, inv_pow, inv_inv, ← pow_mul, ←
      zpow_ofNat]
    rfl
    -- 🎉 no goals
#align zpow_mul zpow_mul
#align mul_zsmul' mul_zsmul'

@[to_additive mul_zsmul]
theorem zpow_mul' (a : α) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m := by rw [mul_comm, zpow_mul]
                                                                      -- 🎉 no goals
#align zpow_mul' zpow_mul'
#align mul_zsmul mul_zsmul

section bit0

set_option linter.deprecated false

@[to_additive bit0_zsmul]
theorem zpow_bit0 (a : α) : ∀ n : ℤ, a ^ bit0 n = a ^ n * a ^ n
  | (n : ℕ) => by simp only [zpow_ofNat, ← Int.ofNat_bit0, pow_bit0]
                  -- 🎉 no goals
  | -[n+1] => by
    simp [← mul_inv_rev, ← pow_bit0]
    -- ⊢ a ^ bit0 -[n+1] = (a ^ bit0 (n + 1))⁻¹
    rw [negSucc_eq, bit0_neg, zpow_neg]
    -- ⊢ (a ^ bit0 (↑n + 1))⁻¹ = (a ^ bit0 (n + 1))⁻¹
    norm_cast
    -- 🎉 no goals
#align zpow_bit0 zpow_bit0
#align bit0_zsmul bit0_zsmul

@[to_additive bit0_zsmul']
theorem zpow_bit0' (a : α) (n : ℤ) : a ^ bit0 n = (a * a) ^ n :=
  (zpow_bit0 a n).trans ((Commute.refl a).mul_zpow n).symm
#align zpow_bit0' zpow_bit0'
#align bit0_zsmul' bit0_zsmul'

@[simp]
theorem zpow_bit0_neg [HasDistribNeg α] (x : α) (n : ℤ) : (-x) ^ bit0 n = x ^ bit0 n := by
  rw [zpow_bit0', zpow_bit0', neg_mul_neg]
  -- 🎉 no goals
#align zpow_bit0_neg zpow_bit0_neg

end bit0

end DivisionMonoid

section Group

variable [Group G]

@[to_additive add_one_zsmul]
theorem zpow_add_one (a : G) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
  | (n : ℕ) => by simp only [← Int.ofNat_succ, zpow_ofNat, pow_succ']
                  -- 🎉 no goals
  | -[0+1] => by erw [zpow_zero, zpow_negSucc, pow_one, mul_left_inv]
                 -- 🎉 no goals
  | -[n + 1+1] => by
    rw [zpow_negSucc, pow_succ, mul_inv_rev, inv_mul_cancel_right]
    -- ⊢ a ^ (-[n + 1+1] + 1) = (a ^ (n + 1))⁻¹
    rw [Int.negSucc_eq, neg_add, add_assoc, neg_add_self, add_zero]
    -- ⊢ a ^ (-↑(n + 1)) = (a ^ (n + 1))⁻¹
    exact zpow_negSucc _ _
    -- 🎉 no goals
#align zpow_add_one zpow_add_one
#align add_one_zsmul add_one_zsmul

@[to_additive sub_one_zsmul]
theorem zpow_sub_one (a : G) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
  calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := (mul_inv_cancel_right _ _).symm
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one, sub_add_cancel]
                          -- 🎉 no goals
#align zpow_sub_one zpow_sub_one
#align sub_one_zsmul sub_one_zsmul

@[to_additive add_zsmul]
theorem zpow_add (a : G) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction' n using Int.induction_on with n ihn n ihn
  case hz => simp
  -- ⊢ a ^ (m + (↑n + 1)) = a ^ m * a ^ (↑n + 1)
  -- 🎉 no goals
  · simp only [← add_assoc, zpow_add_one, ihn, mul_assoc]
    -- 🎉 no goals
  · rw [zpow_sub_one, ← mul_assoc, ← ihn, ← zpow_sub_one, add_sub_assoc]
    -- 🎉 no goals
#align zpow_add zpow_add
#align add_zsmul add_zsmul

@[to_additive add_zsmul_self]
theorem mul_self_zpow (b : G) (m : ℤ) : b * b ^ m = b ^ (m + 1) := by
  conv_lhs =>
    congr
    rw [← zpow_one b]
  rw [← zpow_add, add_comm]
  -- 🎉 no goals
#align mul_self_zpow mul_self_zpow
#align add_zsmul_self add_zsmul_self

@[to_additive add_self_zsmul]
theorem mul_zpow_self (b : G) (m : ℤ) : b ^ m * b = b ^ (m + 1) := by
  conv_lhs =>
    congr
    · skip
    rw [← zpow_one b]
  rw [← zpow_add, add_comm]
  -- 🎉 no goals
#align mul_zpow_self mul_zpow_self
#align add_self_zsmul add_self_zsmul

@[to_additive sub_zsmul]
theorem zpow_sub (a : G) (m n : ℤ) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  rw [sub_eq_add_neg, zpow_add, zpow_neg]
  -- 🎉 no goals
#align zpow_sub zpow_sub
#align sub_zsmul sub_zsmul

@[to_additive one_add_zsmul]
theorem zpow_one_add (a : G) (i : ℤ) : a ^ (1 + i) = a * a ^ i := by rw [zpow_add, zpow_one]
                                                                     -- 🎉 no goals
#align zpow_one_add zpow_one_add
#align one_add_zsmul one_add_zsmul

@[to_additive]
theorem zpow_mul_comm (a : G) (i j : ℤ) : a ^ i * a ^ j = a ^ j * a ^ i :=
  (Commute.refl _).zpow_zpow _ _
#align zpow_mul_comm zpow_mul_comm
#align zsmul_add_comm zsmul_add_comm

section bit1

set_option linter.deprecated false

@[to_additive bit1_zsmul]
theorem zpow_bit1 (a : G) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a := by
  rw [bit1, zpow_add, zpow_bit0, zpow_one]
  -- 🎉 no goals
#align zpow_bit1 zpow_bit1
#align bit1_zsmul bit1_zsmul

end bit1

/-- To show a property of all powers of `g` it suffices to show it is closed under multiplication
by `g` and `g⁻¹` on the left. For subgroups generated by more than one element, see
`Subgroup.closure_induction_left`. -/
@[to_additive "To show a property of all multiples of `g` it suffices to show it is closed under
addition by `g` and `-g` on the left. For additive subgroups generated by more than one element, see
`AddSubgroup.closure_induction_left`."]
theorem zpow_induction_left {g : G} {P : G → Prop} (h_one : P (1 : G))
    (h_mul : ∀ a, P a → P (g * a)) (h_inv : ∀ a, P a → P (g⁻¹ * a)) (n : ℤ) : P (g ^ n) := by
  induction' n using Int.induction_on with n ih n ih
  · rwa [zpow_zero]
    -- 🎉 no goals
  · rw [add_comm, zpow_add, zpow_one]
    -- ⊢ P (g * g ^ ↑n)
    exact h_mul _ ih
    -- 🎉 no goals
  · rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one]
    -- ⊢ P (g⁻¹ * g ^ (-↑n))
    exact h_inv _ ih
    -- 🎉 no goals
#align zpow_induction_left zpow_induction_left
#align zsmul_induction_left zsmul_induction_left

/-- To show a property of all powers of `g` it suffices to show it is closed under multiplication
by `g` and `g⁻¹` on the right. For subgroups generated by more than one element, see
`Subgroup.closure_induction_right`. -/
@[to_additive "To show a property of all multiples of `g` it suffices to show it is closed under
addition by `g` and `-g` on the right. For additive subgroups generated by more than one element,
see `AddSubgroup.closure_induction_right`."]
theorem zpow_induction_right {g : G} {P : G → Prop} (h_one : P (1 : G))
    (h_mul : ∀ a, P a → P (a * g)) (h_inv : ∀ a, P a → P (a * g⁻¹)) (n : ℤ) : P (g ^ n) := by
  induction' n using Int.induction_on with n ih n ih
  · rwa [zpow_zero]
    -- 🎉 no goals
  · rw [zpow_add_one]
    -- ⊢ P (g ^ ↑n * g)
    exact h_mul _ ih
    -- 🎉 no goals
  · rw [zpow_sub_one]
    -- ⊢ P (g ^ (-↑n) * g⁻¹)
    exact h_inv _ ih
    -- 🎉 no goals
#align zpow_induction_right zpow_induction_right
#align zsmul_induction_right zsmul_induction_right

end Group

/-!
### `zpow`/`zsmul` and an order

Those lemmas are placed here
(rather than in `Mathlib.Algebra.GroupPower.Order` with their friends)
because they require facts from `Mathlib.Data.Int.Basic`.
-/

section OrderedAddCommGroup

variable [OrderedCommGroup α] {m n : ℤ} {a b : α}

@[to_additive zsmul_pos]
theorem one_lt_zpow' (ha : 1 < a) {k : ℤ} (hk : (0 : ℤ) < k) : 1 < a ^ k := by
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hk.le
  -- ⊢ 1 < a ^ k
  rw [hn, zpow_ofNat]
  -- ⊢ 1 < a ^ n
  refine' one_lt_pow' ha (coe_nat_pos.mp _).ne'
  -- ⊢ 0 < ↑n
  rwa [← hn]
  -- 🎉 no goals
#align one_lt_zpow' one_lt_zpow'
#align zsmul_pos zsmul_pos

@[to_additive zsmul_strictMono_left]
theorem zpow_strictMono_right (ha : 1 < a) : StrictMono fun n : ℤ => a ^ n := fun m n h =>
  calc
    a ^ m = a ^ m * 1 := (mul_one _).symm
    _ < a ^ m * a ^ (n - m) := mul_lt_mul_left' (one_lt_zpow' ha <| sub_pos_of_lt h) _
    _ = a ^ n := by rw [← zpow_add]; simp
                    -- ⊢ a ^ (m + (n - m)) = a ^ n
                                     -- 🎉 no goals
#align zpow_strict_mono_right zpow_strictMono_right
#align zsmul_strict_mono_left zsmul_strictMono_left

@[to_additive zsmul_mono_left]
theorem zpow_mono_right (ha : 1 ≤ a) : Monotone fun n : ℤ => a ^ n := fun m n h =>
  calc
    a ^ m = a ^ m * 1 := (mul_one _).symm
    _ ≤ a ^ m * a ^ (n - m) := mul_le_mul_left' (one_le_zpow ha <| sub_nonneg_of_le h) _
    _ = a ^ n := by rw [← zpow_add]; simp
                    -- ⊢ a ^ (m + (n - m)) = a ^ n
                                     -- 🎉 no goals
#align zpow_mono_right zpow_mono_right
#align zsmul_mono_left zsmul_mono_left

@[to_additive]
theorem zpow_le_zpow (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n :=
  zpow_mono_right ha h
#align zpow_le_zpow zpow_le_zpow
#align zsmul_le_zsmul zsmul_le_zsmul

@[to_additive]
theorem zpow_lt_zpow (ha : 1 < a) (h : m < n) : a ^ m < a ^ n :=
  zpow_strictMono_right ha h
#align zpow_lt_zpow zpow_lt_zpow
#align zsmul_lt_zsmul zsmul_lt_zsmul

@[to_additive]
theorem zpow_le_zpow_iff (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n :=
  (zpow_strictMono_right ha).le_iff_le
#align zpow_le_zpow_iff zpow_le_zpow_iff
#align zsmul_le_zsmul_iff zsmul_le_zsmul_iff

@[to_additive]
theorem zpow_lt_zpow_iff (ha : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  (zpow_strictMono_right ha).lt_iff_lt
#align zpow_lt_zpow_iff zpow_lt_zpow_iff
#align zsmul_lt_zsmul_iff zsmul_lt_zsmul_iff

variable (α)

@[to_additive zsmul_strictMono_right]
theorem zpow_strictMono_left (hn : 0 < n) : StrictMono ((· ^ n) : α → α) := fun a b hab => by
  rw [← one_lt_div', ← div_zpow]
  -- ⊢ 1 < (b / a) ^ n
  exact one_lt_zpow' (one_lt_div'.2 hab) hn
  -- 🎉 no goals
#align zpow_strict_mono_left zpow_strictMono_left
#align zsmul_strict_mono_right zsmul_strictMono_right

@[to_additive zsmul_mono_right]
theorem zpow_mono_left (hn : 0 ≤ n) : Monotone ((· ^ n) : α → α) := fun a b hab => by
  rw [← one_le_div', ← div_zpow]
  -- ⊢ 1 ≤ (b / a) ^ n
  exact one_le_zpow (one_le_div'.2 hab) hn
  -- 🎉 no goals
#align zpow_mono_left zpow_mono_left
#align zsmul_mono_right zsmul_mono_right

variable {α}

@[to_additive]
theorem zpow_le_zpow' (hn : 0 ≤ n) (h : a ≤ b) : a ^ n ≤ b ^ n :=
  zpow_mono_left α hn h
#align zpow_le_zpow' zpow_le_zpow'
#align zsmul_le_zsmul' zsmul_le_zsmul'

@[to_additive]
theorem zpow_lt_zpow' (hn : 0 < n) (h : a < b) : a ^ n < b ^ n :=
  zpow_strictMono_left α hn h
#align zpow_lt_zpow' zpow_lt_zpow'
#align zsmul_lt_zsmul' zsmul_lt_zsmul'

end OrderedAddCommGroup

section LinearOrderedCommGroup

variable [LinearOrderedCommGroup α] {n : ℤ} {a b : α}

@[to_additive]
theorem zpow_le_zpow_iff' (hn : 0 < n) {a b : α} : a ^ n ≤ b ^ n ↔ a ≤ b :=
  (zpow_strictMono_left α hn).le_iff_le
#align zpow_le_zpow_iff' zpow_le_zpow_iff'
#align zsmul_le_zsmul_iff' zsmul_le_zsmul_iff'

@[to_additive]
theorem zpow_lt_zpow_iff' (hn : 0 < n) {a b : α} : a ^ n < b ^ n ↔ a < b :=
  (zpow_strictMono_left α hn).lt_iff_lt
#align zpow_lt_zpow_iff' zpow_lt_zpow_iff'
#align zsmul_lt_zsmul_iff' zsmul_lt_zsmul_iff'

@[to_additive zsmul_right_injective
      "See also `smul_right_injective`. TODO: provide a `NoZeroSMulDivisors` instance. We can't do
      that here because importing that definition would create import cycles."]
theorem zpow_left_injective (hn : n ≠ 0) : Function.Injective ((· ^ n) : α → α) := by
  rcases hn.symm.lt_or_lt with (h | h)
  -- ⊢ Function.Injective fun x => x ^ n
  · exact (zpow_strictMono_left α h).injective
    -- 🎉 no goals
  · refine' fun a b (hab : a ^ n = b ^ n) => (zpow_strictMono_left α (neg_pos.mpr h)).injective _
    -- ⊢ a ^ (-n) = b ^ (-n)
    rw [zpow_neg, zpow_neg, hab]
    -- 🎉 no goals
#align zpow_left_injective zpow_left_injective
#align zsmul_right_injective zsmul_right_injective

@[to_additive zsmul_right_inj]
theorem zpow_left_inj (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b :=
  (zpow_left_injective hn).eq_iff
#align zpow_left_inj zpow_left_inj
#align zsmul_right_inj zsmul_right_inj

/-- Alias of `zsmul_right_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'` and
`zsmul_lt_zsmul_iff'`. -/
@[to_additive
      "Alias of `zsmul_right_inj`, for ease of discovery alongside
      `zsmul_le_zsmul_iff'` and `zsmul_lt_zsmul_iff'`."]
theorem zpow_eq_zpow_iff' (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b :=
  zpow_left_inj hn
#align zpow_eq_zpow_iff' zpow_eq_zpow_iff'
#align zsmul_eq_zsmul_iff' zsmul_eq_zsmul_iff'

end LinearOrderedCommGroup

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] {a b : α}

theorem abs_nsmul (n : ℕ) (a : α) : |n • a| = n • |a| := by
  cases' le_total a 0 with hneg hpos
  -- ⊢ |n • a| = n • |a|
  · rw [abs_of_nonpos hneg, ← abs_neg, ← neg_nsmul, abs_of_nonneg]
    -- ⊢ 0 ≤ n • -a
    exact nsmul_nonneg (neg_nonneg.mpr hneg) n
    -- 🎉 no goals
  · rw [abs_of_nonneg hpos, abs_of_nonneg]
    -- ⊢ 0 ≤ n • a
    exact nsmul_nonneg hpos n
    -- 🎉 no goals
#align abs_nsmul abs_nsmul

theorem abs_zsmul (n : ℤ) (a : α) : |n • a| = |n| • |a| := by
  obtain n0 | n0 := le_total 0 n
  -- ⊢ |n • a| = |n| • |a|
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le n0
    -- ⊢ |↑n • a| = |↑n| • |a|
    simp only [abs_nsmul, coe_nat_zsmul, Nat.abs_cast]
    -- 🎉 no goals
  · obtain ⟨m, h⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 n0)
    -- ⊢ |n • a| = |n| • |a|
    rw [← abs_neg, ← neg_zsmul, ← abs_neg n, h, coe_nat_zsmul, Nat.abs_cast, coe_nat_zsmul]
    -- ⊢ |m • a| = m • |a|
    exact abs_nsmul m _
    -- 🎉 no goals
#align abs_zsmul abs_zsmul

theorem abs_add_eq_add_abs_le (hle : a ≤ b) :
    |a + b| = |a| + |b| ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  obtain a0 | a0 := le_or_lt 0 a <;> obtain b0 | b0 := le_or_lt 0 b
  -- ⊢ |a + b| = |a| + |b| ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0
                                     -- ⊢ |a + b| = |a| + |b| ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0
                                     -- ⊢ |a + b| = |a| + |b| ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0
  · simp [a0, b0, abs_of_nonneg, add_nonneg a0 b0]
    -- 🎉 no goals
  · exact (lt_irrefl (0 : α) <| a0.trans_lt <| hle.trans_lt b0).elim
    -- 🎉 no goals
  any_goals simp [a0.le, b0.le, abs_of_nonpos, add_nonpos, add_comm]
  -- ⊢ |a + b| = |a| + |b| ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0
  have : (|a + b| = -a + b ↔ b ≤ 0) ↔ (|a + b| = |a| + |b| ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0) := by
    simp [a0, a0.le, a0.not_le, b0, abs_of_neg, abs_of_nonneg]
  refine' this.mp ⟨fun h => _, fun h => by simp only [le_antisymm h b0, abs_of_neg a0, add_zero]⟩
  -- ⊢ b ≤ 0
  obtain ab | ab := le_or_lt (a + b) 0
  -- ⊢ b ≤ 0
  · refine' le_of_eq (eq_zero_of_neg_eq _)
    -- ⊢ -b = b
    rwa [abs_of_nonpos ab, neg_add_rev, add_comm, add_right_inj] at h
    -- 🎉 no goals
  · refine' (lt_irrefl (0 : α) _).elim
    -- ⊢ 0 < 0
    rw [abs_of_pos ab, add_left_inj] at h
    -- ⊢ 0 < 0
    rwa [eq_zero_of_neg_eq h.symm] at a0
    -- 🎉 no goals
#align abs_add_eq_add_abs_le abs_add_eq_add_abs_le

theorem abs_add_eq_add_abs_iff (a b : α) : |a + b| = |a| + |b| ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  obtain ab | ab := le_total a b
  -- ⊢ |a + b| = |a| + |b| ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0
  · exact abs_add_eq_add_abs_le ab
    -- 🎉 no goals
  · rw [add_comm a, add_comm (abs _), abs_add_eq_add_abs_le ab, and_comm, @and_comm (b ≤ 0)]
    -- 🎉 no goals
#align abs_add_eq_add_abs_iff abs_add_eq_add_abs_iff

end LinearOrderedAddCommGroup

@[simp]
theorem WithBot.coe_nsmul [AddMonoid A] (a : A) (n : ℕ) : ↑(n • a) = n • (a : WithBot A) :=
  AddMonoidHom.map_nsmul
    { toFun := fun a : A => (a : WithBot A),
      map_zero' := WithBot.coe_zero,
      map_add' := WithBot.coe_add }
    a n
#align with_bot.coe_nsmul WithBot.coe_nsmul

theorem nsmul_eq_mul' [NonAssocSemiring R] (a : R) (n : ℕ) : n • a = a * n := by
  induction' n with n ih <;> [rw [zero_nsmul, Nat.cast_zero, mul_zero];
    rw [succ_nsmul', ih, Nat.cast_succ, mul_add, mul_one]]
#align nsmul_eq_mul' nsmul_eq_mul'ₓ
-- typeclasses do not match up exactly.

@[simp]
theorem nsmul_eq_mul [NonAssocSemiring R] (n : ℕ) (a : R) : n • a = n * a := by
  rw [nsmul_eq_mul', (n.cast_commute a).eq]
  -- 🎉 no goals
#align nsmul_eq_mul nsmul_eq_mulₓ
-- typeclasses do not match up exactly.

/-- Note that `AddCommMonoid.nat_smulCommClass` requires stronger assumptions on `R`. -/
instance NonUnitalNonAssocSemiring.nat_smulCommClass [NonUnitalNonAssocSemiring R] :
    SMulCommClass ℕ R R :=
  ⟨fun n x y => by
    induction' n with n ih
    -- ⊢ Nat.zero • x • y = x • Nat.zero • y
    · simp [zero_nsmul]
      -- 🎉 no goals
    · simp_rw [succ_nsmul, smul_eq_mul, mul_add, ← smul_eq_mul, ih]⟩
      -- 🎉 no goals
#align non_unital_non_assoc_semiring.nat_smul_comm_class NonUnitalNonAssocSemiring.nat_smulCommClass

/-- Note that `AddCommMonoid.nat_isScalarTower` requires stronger assumptions on `R`. -/
instance NonUnitalNonAssocSemiring.nat_isScalarTower [NonUnitalNonAssocSemiring R] :
    IsScalarTower ℕ R R :=
  ⟨fun n x y => by
    induction' n with n ih
    -- ⊢ (Nat.zero • x) • y = Nat.zero • x • y
    · simp [zero_nsmul]
      -- 🎉 no goals
    · simp_rw [succ_nsmul, ← ih, smul_eq_mul, add_mul]⟩
      -- 🎉 no goals
#align non_unital_non_assoc_semiring.nat_is_scalar_tower NonUnitalNonAssocSemiring.nat_isScalarTower

@[simp, norm_cast]
theorem Nat.cast_pow [Semiring R] (n m : ℕ) : (↑(n ^ m) : R) = (↑n : R) ^ m := by
  induction' m with m ih
  -- ⊢ ↑(n ^ zero) = ↑n ^ zero
  · simp
    -- 🎉 no goals
  · rw [_root_.pow_succ', _root_.pow_succ', Nat.cast_mul, ih]
    -- 🎉 no goals
#align nat.cast_pow Nat.cast_pow

-- Porting note: `norm_cast` attribute removed.
/- Porting note `simp` attribute removed as suggested by linter:
simp can prove this:
  by simp only [Nat.cast_pow]
-/
-- -- @[simp]
theorem Int.coe_nat_pow (n m : ℕ) : ((n ^ m : ℕ) : ℤ) = (n : ℤ) ^ m := by
  induction' m with m _ <;> simp
  -- ⊢ ↑(n ^ Nat.zero) = ↑n ^ Nat.zero
                            -- 🎉 no goals
                            -- 🎉 no goals
#align int.coe_nat_pow Int.coe_nat_pow

theorem Int.natAbs_pow (n : ℤ) (k : ℕ) : Int.natAbs (n ^ k) = Int.natAbs n ^ k := by
  induction' k with k ih <;> [rfl; rw [pow_succ', Int.natAbs_mul, pow_succ', ih]]
  -- 🎉 no goals
#align int.nat_abs_pow Int.natAbs_pow

section bit0_bit1

set_option linter.deprecated false

-- The next four lemmas allow us to replace multiplication by a numeral with a `zsmul` expression.
-- They are used by the `noncomm_ring` tactic, to normalise expressions before passing to `abel`.
theorem bit0_mul [NonUnitalNonAssocRing R] {n r : R} : bit0 n * r = (2 : ℤ) • (n * r) := by
  dsimp [bit0]
  -- ⊢ (n + n) * r = 2 • (n * r)
  rw [add_mul, ← one_add_one_eq_two, add_zsmul, one_zsmul]
  -- 🎉 no goals
#align bit0_mul bit0_mul

theorem mul_bit0 [NonUnitalNonAssocRing R] {n r : R} : r * bit0 n = (2 : ℤ) • (r * n) := by
  dsimp [bit0]
  -- ⊢ r * (n + n) = 2 • (r * n)
  rw [mul_add, ← one_add_one_eq_two, add_zsmul, one_zsmul]
  -- 🎉 no goals
#align mul_bit0 mul_bit0

theorem bit1_mul [NonAssocRing R] {n r : R} : bit1 n * r = (2 : ℤ) • (n * r) + r := by
  dsimp [bit1]
  -- ⊢ (bit0 n + 1) * r = 2 • (n * r) + r
  rw [add_mul, bit0_mul, one_mul]
  -- 🎉 no goals
#align bit1_mul bit1_mul

theorem mul_bit1 [NonAssocRing R] {n r : R} : r * bit1 n = (2 : ℤ) • (r * n) + r := by
  dsimp [bit1]
  -- ⊢ r * (bit0 n + 1) = 2 • (r * n) + r
  rw [mul_add, mul_bit0, mul_one]
  -- 🎉 no goals
#align mul_bit1 mul_bit1

end bit0_bit1

/-- Note this holds in marginally more generality than `Int.cast_mul` -/
theorem Int.cast_mul_eq_zsmul_cast [AddCommGroupWithOne α] :
    ∀ m n, ((m * n : ℤ) : α) = m • (n : α) :=
  fun m =>
  Int.inductionOn' m 0 (by simp) (fun k _ ih n => by simp [add_mul, add_zsmul, ih]) fun k _ ih n =>
                           -- 🎉 no goals
                                                     -- 🎉 no goals
    by simp [sub_mul, sub_zsmul, ih, ← sub_eq_add_neg]
       -- 🎉 no goals
#align int.cast_mul_eq_zsmul_cast Int.cast_mul_eq_zsmul_cast

@[simp]
theorem zsmul_eq_mul [Ring R] (a : R) : ∀ n : ℤ, n • a = n * a
  | (n : ℕ) => by rw [coe_nat_zsmul, nsmul_eq_mul, Int.cast_ofNat]
                  -- 🎉 no goals
  | -[n+1] => by simp [Nat.cast_succ, neg_add_rev, Int.cast_negSucc, add_mul]
                 -- 🎉 no goals
#align zsmul_eq_mul zsmul_eq_mul

theorem zsmul_eq_mul' [Ring R] (a : R) (n : ℤ) : n • a = a * n := by
  rw [zsmul_eq_mul, (n.cast_commute a).eq]
  -- 🎉 no goals
#align zsmul_eq_mul' zsmul_eq_mul'

/-- Note that `AddCommGroup.int_smulCommClass` requires stronger assumptions on `R`. -/
instance NonUnitalNonAssocRing.int_smulCommClass [NonUnitalNonAssocRing R] :
    SMulCommClass ℤ R R :=
  ⟨fun n x y =>
    match n with
    | (n : ℕ) => by simp_rw [coe_nat_zsmul, smul_comm]
                    -- 🎉 no goals
    | -[n+1] => by simp_rw [negSucc_zsmul, smul_eq_mul, mul_neg, mul_smul_comm]⟩
                   -- 🎉 no goals
#align non_unital_non_assoc_ring.int_smul_comm_class NonUnitalNonAssocRing.int_smulCommClass

/-- Note that `AddCommGroup.int_isScalarTower` requires stronger assumptions on `R`. -/
instance NonUnitalNonAssocRing.int_isScalarTower [NonUnitalNonAssocRing R] :
    IsScalarTower ℤ R R :=
  ⟨fun n x y =>
    match n with
    | (n : ℕ) => by simp_rw [coe_nat_zsmul, smul_assoc]
                    -- 🎉 no goals
    | -[n+1] => by simp_rw [negSucc_zsmul, smul_eq_mul, neg_mul, smul_mul_assoc]⟩
                   -- 🎉 no goals
#align non_unital_non_assoc_ring.int_is_scalar_tower NonUnitalNonAssocRing.int_isScalarTower

theorem zsmul_int_int (a b : ℤ) : a • b = a * b := by simp
                                                      -- 🎉 no goals
#align zsmul_int_int zsmul_int_int

theorem zsmul_int_one (n : ℤ) : n • (1 : ℤ) = n := by simp
                                                      -- 🎉 no goals
#align zsmul_int_one zsmul_int_one

@[simp, norm_cast]
theorem Int.cast_pow [Ring R] (n : ℤ) (m : ℕ) : (↑(n ^ m) : R) = (↑n : R) ^ m := by
  induction' m with m ih
  -- ⊢ ↑(n ^ Nat.zero) = ↑n ^ Nat.zero
  · rw [pow_zero, pow_zero, Int.cast_one]
    -- 🎉 no goals
  · rw [pow_succ, pow_succ, Int.cast_mul, ih]
    -- 🎉 no goals
#align int.cast_pow Int.cast_powₓ
-- typeclasses do not align exactly

theorem neg_one_pow_eq_pow_mod_two [Ring R] {n : ℕ} : (-1 : R) ^ n = (-1) ^ (n % 2) := by
  rw [← Nat.mod_add_div n 2, pow_add, pow_mul]; simp [sq]
  -- ⊢ (-1) ^ (n % 2) * ((-1) ^ 2) ^ (n / 2) = (-1) ^ ((n % 2 + 2 * (n / 2)) % 2)
                                                -- 🎉 no goals
#align neg_one_pow_eq_pow_mod_two neg_one_pow_eq_pow_mod_two

section OrderedSemiring

variable [OrderedSemiring R] {a : R}

/-- Bernoulli's inequality. This version works for semirings but requires
additional hypotheses `0 ≤ a * a` and `0 ≤ (1 + a) * (1 + a)`. -/
theorem one_add_mul_le_pow' (Hsq : 0 ≤ a * a) (Hsq' : 0 ≤ (1 + a) * (1 + a)) (H : 0 ≤ 2 + a) :
    ∀ n : ℕ, 1 + (n : R) * a ≤ (1 + a) ^ n
  | 0 => by simp
            -- 🎉 no goals
  | 1 => by simp
            -- 🎉 no goals
  | n + 2 =>
    have : 0 ≤ (n : R) * (a * a * (2 + a)) + a * a :=
      add_nonneg (mul_nonneg n.cast_nonneg (mul_nonneg Hsq H)) Hsq
    calc
      1 + (↑(n + 2) : R) * a ≤ 1 + ↑(n + 2) * a + (n * (a * a * (2 + a)) + a * a) :=
        le_add_of_nonneg_right this
      _ = (1 + a) * (1 + a) * (1 + n * a) := by {
          simp only [Nat.cast_add, add_mul, mul_add, one_mul, mul_one, ← one_add_one_eq_two,
            Nat.cast_one, add_assoc, add_right_inj]
          simp only [← add_assoc, add_comm _ (↑n * a)]
          simp only [add_assoc, (n.cast_commute (_ : R)).left_comm]
          simp only [add_comm, add_left_comm] }
      _ ≤ (1 + a) * (1 + a) * (1 + a) ^ n :=
        mul_le_mul_of_nonneg_left (one_add_mul_le_pow' Hsq Hsq' H _) Hsq'
      _ = (1 + a) ^ (n + 2) := by simp only [pow_succ, mul_assoc]
                                  -- 🎉 no goals
#align one_add_mul_le_pow' one_add_mul_le_pow'

theorem pow_le_pow_of_le_one_aux (h : 0 ≤ a) (ha : a ≤ 1) (i : ℕ) :
    ∀ k : ℕ, a ^ (i + k) ≤ a ^ i
  | 0 => by simp
            -- 🎉 no goals
  | k + 1 => by
    rw [← add_assoc, ← one_mul (a ^ i), pow_succ]
    -- ⊢ a * a ^ (i + k) ≤ 1 * a ^ i
    exact mul_le_mul ha (pow_le_pow_of_le_one_aux h ha _ _) (pow_nonneg h _) zero_le_one
    -- 🎉 no goals
-- Porting note: no #align because private in Lean 3

theorem pow_le_pow_of_le_one (h : 0 ≤ a) (ha : a ≤ 1) {i j : ℕ} (hij : i ≤ j) : a ^ j ≤ a ^ i := by
  let ⟨k, hk⟩ := Nat.exists_eq_add_of_le hij
  -- ⊢ a ^ j ≤ a ^ i
  rw [hk]; exact pow_le_pow_of_le_one_aux h ha _ _
  -- ⊢ a ^ (i + k) ≤ a ^ i
           -- 🎉 no goals
#align pow_le_pow_of_le_one pow_le_pow_of_le_one

theorem pow_le_of_le_one (h₀ : 0 ≤ a) (h₁ : a ≤ 1) {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ a :=
  (pow_one a).subst (pow_le_pow_of_le_one h₀ h₁ (Nat.pos_of_ne_zero hn))
#align pow_le_of_le_one pow_le_of_le_one

theorem sq_le (h₀ : 0 ≤ a) (h₁ : a ≤ 1) : a ^ 2 ≤ a :=
  pow_le_of_le_one h₀ h₁ two_ne_zero
#align sq_le sq_le

end OrderedSemiring

section LinearOrderedSemiring

variable [LinearOrderedSemiring R]

theorem sign_cases_of_C_mul_pow_nonneg {C r : R} (h : ∀ n : ℕ, 0 ≤ C * r ^ n) :
    C = 0 ∨ 0 < C ∧ 0 ≤ r := by
  have : 0 ≤ C := by simpa only [pow_zero, mul_one] using h 0
  -- ⊢ C = 0 ∨ 0 < C ∧ 0 ≤ r
  refine' this.eq_or_lt.elim (fun h => Or.inl h.symm) fun hC => Or.inr ⟨hC, _⟩
  -- ⊢ 0 ≤ r
  refine' nonneg_of_mul_nonneg_right _ hC
  -- ⊢ 0 ≤ C * r
  simpa only [pow_one] using h 1
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align sign_cases_of_C_mul_pow_nonneg sign_cases_of_C_mul_pow_nonneg

end LinearOrderedSemiring

section LinearOrderedRing

variable [LinearOrderedRing R] {a : R} {n : ℕ}

@[simp]
theorem abs_pow (a : R) (n : ℕ) : |a ^ n| = |a| ^ n :=
  (pow_abs a n).symm
#align abs_pow abs_pow

section bit1

set_option linter.deprecated false

@[simp]
theorem pow_bit1_neg_iff : a ^ bit1 n < 0 ↔ a < 0 :=
  ⟨fun h => not_le.1 fun h' => not_le.2 h <| pow_nonneg h' _, fun ha => pow_bit1_neg ha n⟩
#align pow_bit1_neg_iff pow_bit1_neg_iff

@[simp]
theorem pow_bit1_nonneg_iff : 0 ≤ a ^ bit1 n ↔ 0 ≤ a :=
  le_iff_le_iff_lt_iff_lt.2 pow_bit1_neg_iff
#align pow_bit1_nonneg_iff pow_bit1_nonneg_iff

@[simp]
theorem pow_bit1_nonpos_iff : a ^ bit1 n ≤ 0 ↔ a ≤ 0 := by
  simp only [le_iff_lt_or_eq, pow_bit1_neg_iff]
  -- ⊢ a < 0 ∨ a ^ bit1 n = 0 ↔ a < 0 ∨ a = 0
  refine' ⟨_, _⟩
  -- ⊢ a < 0 ∨ a ^ bit1 n = 0 → a < 0 ∨ a = 0
  · rintro (hpos | hz)
    -- ⊢ a < 0 ∨ a = 0
    · left
      -- ⊢ a < 0
      exact hpos
      -- 🎉 no goals
    · right
      -- ⊢ a = 0
      exact (pow_eq_zero_iff'.1 hz).1
      -- 🎉 no goals
  · rintro (hneg | hz)
    -- ⊢ a < 0 ∨ a ^ bit1 n = 0
    · left
      -- ⊢ a < 0
      exact hneg
      -- 🎉 no goals
    · right
      -- ⊢ a ^ bit1 n = 0
      simp [hz, bit1]
      -- 🎉 no goals
#align pow_bit1_nonpos_iff pow_bit1_nonpos_iff

@[simp]
theorem pow_bit1_pos_iff : 0 < a ^ bit1 n ↔ 0 < a :=
  lt_iff_lt_of_le_iff_le pow_bit1_nonpos_iff
#align pow_bit1_pos_iff pow_bit1_pos_iff

theorem strictMono_pow_bit1 (n : ℕ) : StrictMono fun a : R => a ^ bit1 n := by
  intro a b hab
  -- ⊢ (fun a => a ^ bit1 n) a < (fun a => a ^ bit1 n) b
  cases' le_total a 0 with ha ha
  -- ⊢ (fun a => a ^ bit1 n) a < (fun a => a ^ bit1 n) b
  · cases' le_or_lt b 0 with hb hb
    -- ⊢ (fun a => a ^ bit1 n) a < (fun a => a ^ bit1 n) b
    · rw [← neg_lt_neg_iff, ← neg_pow_bit1, ← neg_pow_bit1]
      -- ⊢ (-b) ^ bit1 n < (-a) ^ bit1 n
      exact pow_lt_pow_of_lt_left (neg_lt_neg hab) (neg_nonneg.2 hb) (bit1_pos (zero_le n))
      -- 🎉 no goals
    · exact (pow_bit1_nonpos_iff.2 ha).trans_lt (pow_bit1_pos_iff.2 hb)
      -- 🎉 no goals
  · exact pow_lt_pow_of_lt_left hab ha (bit1_pos (zero_le n))
    -- 🎉 no goals
#align strict_mono_pow_bit1 strictMono_pow_bit1

end bit1

/-- Bernoulli's inequality for `n : ℕ`, `-2 ≤ a`. -/
theorem one_add_mul_le_pow (H : -2 ≤ a) (n : ℕ) : 1 + (n : R) * a ≤ (1 + a) ^ n :=
  one_add_mul_le_pow' (mul_self_nonneg _) (mul_self_nonneg _) (neg_le_iff_add_nonneg'.1 H) _
#align one_add_mul_le_pow one_add_mul_le_pow

/-- Bernoulli's inequality reformulated to estimate `a^n`. -/
theorem one_add_mul_sub_le_pow (H : -1 ≤ a) (n : ℕ) : 1 + (n : R) * (a - 1) ≤ a ^ n := by
  have : -2 ≤ a - 1 := by
    rwa [← one_add_one_eq_two, neg_add, ← sub_eq_add_neg, sub_le_sub_iff_right]
  simpa only [add_sub_cancel'_right] using one_add_mul_le_pow this n
  -- 🎉 no goals
#align one_add_mul_sub_le_pow one_add_mul_sub_le_pow

end LinearOrderedRing

namespace Int

lemma natAbs_sq (x : ℤ) : (x.natAbs : ℤ) ^ 2 = x ^ 2 := by rw [sq, Int.natAbs_mul_self', sq]
                                                           -- 🎉 no goals
#align int.nat_abs_sq Int.natAbs_sq

alias natAbs_pow_two := natAbs_sq
#align int.nat_abs_pow_two Int.natAbs_pow_two

theorem natAbs_le_self_sq (a : ℤ) : (Int.natAbs a : ℤ) ≤ a ^ 2 := by
  rw [← Int.natAbs_sq a, sq]
  -- ⊢ ↑(natAbs a) ≤ ↑(natAbs a) * ↑(natAbs a)
  norm_cast
  -- ⊢ natAbs a ≤ natAbs a * natAbs a
  apply Nat.le_mul_self
  -- 🎉 no goals
#align int.abs_le_self_sq Int.natAbs_le_self_sq

alias natAbs_le_self_pow_two := natAbs_le_self_sq

theorem le_self_sq (b : ℤ) : b ≤ b ^ 2 :=
  le_trans le_natAbs (natAbs_le_self_sq _)
#align int.le_self_sq Int.le_self_sq

alias le_self_pow_two := le_self_sq
#align int.le_self_pow_two Int.le_self_pow_two

theorem pow_right_injective {x : ℤ} (h : 1 < x.natAbs) :
    Function.Injective ((· ^ ·) x : ℕ → ℤ) := by
  suffices Function.Injective (natAbs ∘ ((· ^ ·) x : ℕ → ℤ)) by
    exact Function.Injective.of_comp this
  convert Nat.pow_right_injective h using 2
  -- ⊢ (natAbs ∘ (fun x x_1 => x ^ x_1) x) x✝ = natAbs x ^ x✝
  rw [Function.comp_apply, natAbs_pow]
  -- 🎉 no goals
#align int.pow_right_injective Int.pow_right_injective

end Int

variable (M G A)

/-- Additive homomorphisms from `ℕ` are defined by the image of `1`. -/
def multiplesHom [AddMonoid A] : A ≃ (ℕ →+ A) where
  toFun : A → ℕ →+ A := fun x =>
  { toFun := fun n => n • x
    map_zero' := zero_nsmul x
    map_add' := fun _ _ => add_nsmul _ _ _ }
  invFun f := f 1
  left_inv := one_nsmul
  right_inv f := AddMonoidHom.ext_nat <| one_nsmul (f 1)
#align multiples_hom multiplesHom

/-- Additive homomorphisms from `ℤ` are defined by the image of `1`. -/
def zmultiplesHom [AddGroup A] :
    A ≃ (ℤ →+ A) where
  toFun x :=
  { toFun := fun n => n • x
    map_zero' := zero_zsmul x
    map_add' := fun _ _ => add_zsmul _ _ _ }
  invFun f := f 1
  left_inv := one_zsmul
  right_inv f := AddMonoidHom.ext_int <| one_zsmul (f 1)
#align zmultiples_hom zmultiplesHom

/-- Monoid homomorphisms from `Multiplicative ℕ` are defined by the image
of `Multiplicative.ofAdd 1`. -/
def powersHom [Monoid M] : M ≃ (Multiplicative ℕ →* M) :=
  Additive.ofMul.trans <| (multiplesHom _).trans <| AddMonoidHom.toMultiplicative''
#align powers_hom powersHom

/-- Monoid homomorphisms from `Multiplicative ℤ` are defined by the image
of `Multiplicative.ofAdd 1`. -/
def zpowersHom [Group G] : G ≃ (Multiplicative ℤ →* G) :=
  Additive.ofMul.trans <| (zmultiplesHom _).trans <| AddMonoidHom.toMultiplicative''
#align zpowers_hom zpowersHom

attribute [to_additive existing multiplesHom] powersHom

attribute [to_additive existing zmultiplesHom] zpowersHom

variable {M G A}

theorem powersHom_apply [Monoid M] (x : M) (n : Multiplicative ℕ) :
    powersHom M x n = x ^ (Multiplicative.toAdd n) :=
  rfl
#align powers_hom_apply powersHom_apply

theorem powersHom_symm_apply [Monoid M] (f : Multiplicative ℕ →* M) :
    (powersHom M).symm f = f (Multiplicative.ofAdd 1) :=
  rfl
#align powers_hom_symm_apply powersHom_symm_apply

theorem zpowersHom_apply [Group G] (x : G) (n : Multiplicative ℤ) :
    zpowersHom G x n = x ^ (Multiplicative.toAdd n) :=
  rfl
#align zpowers_hom_apply zpowersHom_apply

theorem zpowersHom_symm_apply [Group G] (f : Multiplicative ℤ →* G) :
    (zpowersHom G).symm f = f (Multiplicative.ofAdd 1) :=
  rfl
#align zpowers_hom_symm_apply zpowersHom_symm_apply

-- todo: can `to_additive` generate the following lemmas automatically?

theorem multiplesHom_apply [AddMonoid A] (x : A) (n : ℕ) : multiplesHom A x n = n • x :=
  rfl
#align multiples_hom_apply multiplesHom_apply

attribute [to_additive existing (attr := simp) multiplesHom_apply] powersHom_apply

theorem multiplesHom_symm_apply [AddMonoid A] (f : ℕ →+ A) : (multiplesHom A).symm f = f 1 :=
  rfl
#align multiples_hom_symm_apply multiplesHom_symm_apply

attribute [to_additive existing (attr := simp) multiplesHom_symm_apply] powersHom_symm_apply

theorem zmultiplesHom_apply [AddGroup A] (x : A) (n : ℤ) : zmultiplesHom A x n = n • x :=
  rfl
#align zmultiples_hom_apply zmultiplesHom_apply

attribute [to_additive existing (attr := simp) zmultiplesHom_apply] zpowersHom_apply

theorem zmultiplesHom_symm_apply [AddGroup A] (f : ℤ →+ A) : (zmultiplesHom A).symm f = f 1 :=
  rfl
#align zmultiples_hom_symm_apply zmultiplesHom_symm_apply

attribute [to_additive existing (attr := simp) zmultiplesHom_symm_apply] zpowersHom_symm_apply

-- TODO use to_additive in the rest of this file
theorem MonoidHom.apply_mnat [Monoid M] (f : Multiplicative ℕ →* M) (n : Multiplicative ℕ) :
    f n = f (Multiplicative.ofAdd 1) ^ (Multiplicative.toAdd n) := by
  rw [← powersHom_symm_apply, ← powersHom_apply, Equiv.apply_symm_apply]
  -- 🎉 no goals
#align monoid_hom.apply_mnat MonoidHom.apply_mnat

@[ext]
theorem MonoidHom.ext_mnat [Monoid M] ⦃f g : Multiplicative ℕ →* M⦄
    (h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g :=
  MonoidHom.ext fun n => by rw [f.apply_mnat, g.apply_mnat, h]
                            -- 🎉 no goals
#align monoid_hom.ext_mnat MonoidHom.ext_mnat

theorem MonoidHom.apply_mint [Group M] (f : Multiplicative ℤ →* M) (n : Multiplicative ℤ) :
    f n = f (Multiplicative.ofAdd 1) ^ (Multiplicative.toAdd n) := by
  rw [← zpowersHom_symm_apply, ← zpowersHom_apply, Equiv.apply_symm_apply]
  -- 🎉 no goals
#align monoid_hom.apply_mint MonoidHom.apply_mint

/-! `MonoidHom.ext_mint` is defined in `Data.Int.Cast` -/

theorem AddMonoidHom.apply_nat [AddMonoid M] (f : ℕ →+ M) (n : ℕ) : f n = n • f 1 := by
  rw [← multiplesHom_symm_apply, ← multiplesHom_apply, Equiv.apply_symm_apply]
  -- 🎉 no goals
#align add_monoid_hom.apply_nat AddMonoidHom.apply_nat

/-! `AddMonoidHom.ext_nat` is defined in `Data.Nat.Cast` -/

theorem AddMonoidHom.apply_int [AddGroup M] (f : ℤ →+ M) (n : ℤ) : f n = n • f 1 := by
  rw [← zmultiplesHom_symm_apply, ← zmultiplesHom_apply, Equiv.apply_symm_apply]
  -- 🎉 no goals
#align add_monoid_hom.apply_int AddMonoidHom.apply_int

/-! `AddMonoidHom.ext_int` is defined in `Data.Int.Cast` -/

variable (M G A)
/-- If `M` is commutative, `powersHom` is a multiplicative equivalence. -/
def powersMulHom [CommMonoid M] : M ≃* (Multiplicative ℕ →* M) :=
  { powersHom M with map_mul' := fun a b => MonoidHom.ext fun n => by simp [mul_pow] }
                                                                      -- 🎉 no goals
#align powers_mul_hom powersMulHom

/-- If `M` is commutative, `zpowersHom` is a multiplicative equivalence. -/
def zpowersMulHom [CommGroup G] : G ≃* (Multiplicative ℤ →* G) :=
  { zpowersHom G with map_mul' := fun a b => MonoidHom.ext fun n => by simp [mul_zpow] }
                                                                       -- 🎉 no goals
#align zpowers_mul_hom zpowersMulHom

/-- If `M` is commutative, `multiplesHom` is an additive equivalence. -/
def multiplesAddHom [AddCommMonoid A] : A ≃+ (ℕ →+ A) :=
  { multiplesHom A with map_add' := fun a b => AddMonoidHom.ext fun n => by simp [nsmul_add] }
                                                                            -- 🎉 no goals
#align multiples_add_hom multiplesAddHom

/-- If `M` is commutative, `zmultiplesHom` is an additive equivalence. -/
def zmultiplesAddHom [AddCommGroup A] : A ≃+ (ℤ →+ A) :=
  { zmultiplesHom A with map_add' := fun a b => AddMonoidHom.ext fun n => by simp [zsmul_add] }
                                                                             -- 🎉 no goals
#align zmultiples_add_hom zmultiplesAddHom

variable {M G A}

@[simp]
theorem powersMulHom_apply [CommMonoid M] (x : M) (n : Multiplicative ℕ) :
    powersMulHom M x n = x ^ (Multiplicative.toAdd n) :=
  rfl
#align powers_mul_hom_apply powersMulHom_apply

@[simp]
theorem powersMulHom_symm_apply [CommMonoid M] (f : Multiplicative ℕ →* M) :
    (powersMulHom M).symm f = f (Multiplicative.ofAdd 1) :=
  rfl
#align powers_mul_hom_symm_apply powersMulHom_symm_apply

@[simp]
theorem zpowersMulHom_apply [CommGroup G] (x : G) (n : Multiplicative ℤ) :
    zpowersMulHom G x n = x ^ (Multiplicative.toAdd n) :=
  rfl
#align zpowers_mul_hom_apply zpowersMulHom_apply

@[simp]
theorem zpowersMulHom_symm_apply [CommGroup G] (f : Multiplicative ℤ →* G) :
    (zpowersMulHom G).symm f = f (Multiplicative.ofAdd 1) :=
  rfl
#align zpowers_mul_hom_symm_apply zpowersMulHom_symm_apply

@[simp]
theorem multiplesAddHom_apply [AddCommMonoid A] (x : A) (n : ℕ) : multiplesAddHom A x n = n • x :=
  rfl
#align multiples_add_hom_apply multiplesAddHom_apply

@[simp]
theorem multiplesAddHom_symm_apply [AddCommMonoid A] (f : ℕ →+ A) :
    (multiplesAddHom A).symm f = f 1 :=
  rfl
#align multiples_add_hom_symm_apply multiplesAddHom_symm_apply

@[simp]
theorem zmultiplesAddHom_apply [AddCommGroup A] (x : A) (n : ℤ) :
    zmultiplesAddHom A x n = n • x :=
  rfl
#align zmultiples_add_hom_apply zmultiplesAddHom_apply

@[simp]
theorem zmultiplesAddHom_symm_apply [AddCommGroup A] (f : ℤ →+ A) :
    (zmultiplesAddHom A).symm f = f 1 :=
  rfl
#align zmultiples_add_hom_symm_apply zmultiplesAddHom_symm_apply

/-!
### Commutativity (again)

Facts about `SemiconjBy` and `Commute` that require `zpow` or `zsmul`, or the fact that integer
multiplication equals semiring multiplication.
-/


namespace SemiconjBy

section

variable [Semiring R] {a x y : R}

@[simp]
theorem cast_nat_mul_right (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy a ((n : R) * x) (n * y) :=
  SemiconjBy.mul_right (Nat.commute_cast _ _) h
#align semiconj_by.cast_nat_mul_right SemiconjBy.cast_nat_mul_right

@[simp]
theorem cast_nat_mul_left (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy ((n : R) * a) x y :=
  SemiconjBy.mul_left (Nat.cast_commute _ _) h
#align semiconj_by.cast_nat_mul_left SemiconjBy.cast_nat_mul_left

@[simp]
theorem cast_nat_mul_cast_nat_mul (h : SemiconjBy a x y) (m n : ℕ) :
    SemiconjBy ((m : R) * a) (n * x) (n * y) :=
  (h.cast_nat_mul_left m).cast_nat_mul_right n
#align semiconj_by.cast_nat_mul_cast_nat_mul SemiconjBy.cast_nat_mul_cast_nat_mul

end

variable [Monoid M] [Group G] [Ring R]

@[to_additive (attr := simp)]
theorem units_zpow_right {a : M} {x y : Mˣ} (h : SemiconjBy a x y) :
    ∀ m : ℤ, SemiconjBy a ↑(x ^ m) ↑(y ^ m)
  | (n : ℕ) => by simp only [zpow_ofNat, Units.val_pow_eq_pow_val, h, pow_right]
                  -- 🎉 no goals
  | -[n+1] => by simp only [zpow_negSucc, Units.val_pow_eq_pow_val, units_inv_right, h, pow_right]
                 -- 🎉 no goals
#align semiconj_by.units_zpow_right SemiconjBy.units_zpow_right
#align add_semiconj_by.add_units_zsmul_right AddSemiconjBy.addUnits_zsmul_right

variable {a b x y x' y' : R}

@[simp]
theorem cast_int_mul_right (h : SemiconjBy a x y) (m : ℤ) : SemiconjBy a ((m : ℤ) * x) (m * y) :=
  SemiconjBy.mul_right (Int.commute_cast _ _) h
#align semiconj_by.cast_int_mul_right SemiconjBy.cast_int_mul_right

@[simp]
theorem cast_int_mul_left (h : SemiconjBy a x y) (m : ℤ) : SemiconjBy ((m : R) * a) x y :=
  SemiconjBy.mul_left (Int.cast_commute _ _) h
#align semiconj_by.cast_int_mul_left SemiconjBy.cast_int_mul_left

@[simp]
theorem cast_int_mul_cast_int_mul (h : SemiconjBy a x y) (m n : ℤ) :
    SemiconjBy ((m : R) * a) (n * x) (n * y) :=
  (h.cast_int_mul_left m).cast_int_mul_right n
#align semiconj_by.cast_int_mul_cast_int_mul SemiconjBy.cast_int_mul_cast_int_mul

end SemiconjBy

namespace Commute

section

variable [Semiring R] {a b : R}

@[simp]
theorem cast_nat_mul_right (h : Commute a b) (n : ℕ) : Commute a ((n : R) * b) :=
  SemiconjBy.cast_nat_mul_right h n
#align commute.cast_nat_mul_right Commute.cast_nat_mul_right

@[simp]
theorem cast_nat_mul_left (h : Commute a b) (n : ℕ) : Commute ((n : R) * a) b :=
  SemiconjBy.cast_nat_mul_left h n
#align commute.cast_nat_mul_left Commute.cast_nat_mul_left

@[simp]
theorem cast_nat_mul_cast_nat_mul (h : Commute a b)
    (m n : ℕ) : Commute (m * a : R) (n * b : R) :=
  SemiconjBy.cast_nat_mul_cast_nat_mul h m n
#align commute.cast_nat_mul_cast_nat_mul Commute.cast_nat_mul_cast_nat_mul

variable (a) (m n : ℕ)

/- Porting note: `simp` attribute removed as linter reports:
simp can prove this:
  by simp only [Commute.refl, Commute.cast_nat_mul_right]
-/
-- @[simp]
theorem self_cast_nat_mul : Commute a (n * a : R) :=
  (Commute.refl a).cast_nat_mul_right n
#align commute.self_cast_nat_mul Commute.self_cast_nat_mul

/- Porting note: `simp` attribute removed as linter reports:
simp can prove this:
  by simp only [Commute.refl, Commute.cast_nat_mul_left]
-/
-- @[simp]
theorem cast_nat_mul_self : Commute ((n : R) * a) a :=
  (Commute.refl a).cast_nat_mul_left n
#align commute.cast_nat_mul_self Commute.cast_nat_mul_self

/- Porting note: `simp` attribute removed as linter reports:
simp can prove this:
  by simp only [Commute.refl, Commute.cast_nat_mul_left, Commute.cast_nat_mul_right]
-/
-- @[simp]
theorem self_cast_nat_mul_cast_nat_mul : Commute (m * a : R) (n * a : R) :=
  (Commute.refl a).cast_nat_mul_cast_nat_mul m n
#align commute.self_cast_nat_mul_cast_nat_mul Commute.self_cast_nat_mul_cast_nat_mul

end

variable [Monoid M] [Group G] [Ring R]

@[to_additive (attr := simp)]
theorem units_zpow_right {a : M} {u : Mˣ} (h : Commute a u)
    (m : ℤ) : Commute a ↑(u ^ m) :=
  SemiconjBy.units_zpow_right h m
#align commute.units_zpow_right Commute.units_zpow_right
#align add_commute.add_units_zsmul_right AddCommute.addUnits_zsmul_right

@[to_additive (attr := simp)]
theorem units_zpow_left {u : Mˣ} {a : M} (h : Commute (↑u) a)
  (m : ℤ) : Commute (↑(u ^ m)) a :=
  (h.symm.units_zpow_right m).symm
#align commute.units_zpow_left Commute.units_zpow_left
#align add_commute.add_units_zsmul_left AddCommute.addUnits_zsmul_left

variable {a b : R}

@[simp]
theorem cast_int_mul_right (h : Commute a b) (m : ℤ) : Commute a (m * b : R) :=
  SemiconjBy.cast_int_mul_right h m
#align commute.cast_int_mul_right Commute.cast_int_mul_right

@[simp]
theorem cast_int_mul_left (h : Commute a b) (m : ℤ) :
   Commute ((m : R) * a) b :=
  SemiconjBy.cast_int_mul_left h m
#align commute.cast_int_mul_left Commute.cast_int_mul_left

theorem cast_int_mul_cast_int_mul (h : Commute a b)
  (m n : ℤ) : Commute (m * a : R) (n * b : R) :=
  SemiconjBy.cast_int_mul_cast_int_mul h m n
#align commute.cast_int_mul_cast_int_mul Commute.cast_int_mul_cast_int_mul

variable (a) (m n : ℤ)

@[simp]
theorem cast_int_left : Commute (m : R) a := Int.cast_commute _ _
#align commute.cast_int_left Commute.cast_int_left

@[simp]
theorem cast_int_right : Commute a m := Int.commute_cast _ _
#align commute.cast_int_right Commute.cast_int_right

/- Porting note: `simp` attribute removed as linter reports:
simp can prove this:
  by simp only [Commute.cast_int_right, Commute.refl, Commute.mul_right]
-/
-- @[simp]
theorem self_cast_int_mul : Commute a (n * a : R) :=
  (Commute.refl a).cast_int_mul_right n
#align commute.self_cast_int_mul Commute.self_cast_int_mul

/- Porting note: `simp` attribute removed as linter reports:
simp can prove this:
  by simp only [Commute.cast_int_left, Commute.refl, Commute.mul_left]
-/
-- @[simp]
theorem cast_int_mul_self : Commute ((n : R) * a) a :=
  (Commute.refl a).cast_int_mul_left n
#align commute.cast_int_mul_self Commute.cast_int_mul_self

theorem self_cast_int_mul_cast_int_mul : Commute (m * a : R) (n * a : R) :=
  (Commute.refl a).cast_int_mul_cast_int_mul m n
#align commute.self_cast_int_mul_cast_int_mul Commute.self_cast_int_mul_cast_int_mul

end Commute

section Multiplicative

open Multiplicative

@[simp]
theorem Nat.toAdd_pow (a : Multiplicative ℕ) (b : ℕ) : toAdd (a ^ b) = toAdd a * b :=
  mul_comm _ _
#align nat.to_add_pow Nat.toAdd_pow

@[simp]
theorem Nat.ofAdd_mul (a b : ℕ) : ofAdd (a * b) = ofAdd a ^ b :=
  (Nat.toAdd_pow _ _).symm
#align nat.of_add_mul Nat.ofAdd_mul

@[simp]
theorem Int.toAdd_pow (a : Multiplicative ℤ) (b : ℕ) : toAdd (a ^ b) = toAdd a * b :=
  mul_comm _ _
#align int.to_add_pow Int.toAdd_pow

@[simp]
theorem Int.toAdd_zpow (a : Multiplicative ℤ) (b : ℤ) : toAdd (a ^ b) = toAdd a * b :=
  mul_comm _ _
#align int.to_add_zpow Int.toAdd_zpow

@[simp]
theorem Int.ofAdd_mul (a b : ℤ) : ofAdd (a * b) = ofAdd a ^ b :=
  (Int.toAdd_zpow _ _).symm
#align int.of_add_mul Int.ofAdd_mul

end Multiplicative

namespace Units

variable [Monoid M]

theorem conj_pow (u : Mˣ) (x : M) (n : ℕ) :
      ((↑u : M) * x * (↑u⁻¹ : M)) ^ n =
      (u : M) * x ^ n * (↑u⁻¹ : M) :=
  (divp_eq_iff_mul_eq.2
  ((u.mk_semiconjBy x).pow_right n).eq.symm).symm
#align units.conj_pow Units.conj_pow

theorem conj_pow' (u : Mˣ) (x : M) (n : ℕ) :
  ((↑u⁻¹ : M) * x * (u : M)) ^ n = (↑u⁻¹ : M) * x ^ n * (u : M) :=
  u⁻¹.conj_pow x n
#align units.conj_pow' Units.conj_pow'

end Units

namespace MulOpposite

/-- Moving to the opposite monoid commutes with taking powers. -/
@[simp]
theorem op_pow [Monoid M] (x : M) (n : ℕ) : op (x ^ n) = op x ^ n :=
  rfl
#align mul_opposite.op_pow MulOpposite.op_pow

@[simp]
theorem unop_pow [Monoid M] (x : Mᵐᵒᵖ) (n : ℕ) : unop (x ^ n) = unop x ^ n :=
  rfl
#align mul_opposite.unop_pow MulOpposite.unop_pow

/-- Moving to the opposite group or `GroupWithZero` commutes with taking powers. -/
@[simp]
theorem op_zpow [DivInvMonoid M] (x : M) (z : ℤ) : op (x ^ z) = op x ^ z :=
  rfl
#align mul_opposite.op_zpow MulOpposite.op_zpow

@[simp]
theorem unop_zpow [DivInvMonoid M] (x : Mᵐᵒᵖ) (z : ℤ) : unop (x ^ z) = unop x ^ z :=
  rfl
#align mul_opposite.unop_zpow MulOpposite.unop_zpow

end MulOpposite

-- Porting note: this was added in an ad hoc port for use in `Tactic/NormNum/Basic`

@[simp] theorem pow_eq {m : ℤ} {n : ℕ} : m.pow n = m ^ n := rfl
