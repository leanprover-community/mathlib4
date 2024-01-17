/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Algebra.GroupPower.Ring
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

section DivisionMonoid

variable [DivisionMonoid α]

-- Note that `mul_zsmul` and `zpow_mul` have the primes swapped
-- when additivised since their argument order,
-- and therefore the more "natural" choice of lemma, is reversed.
@[to_additive mul_zsmul']
theorem zpow_mul (a : α) : ∀ m n : ℤ, a ^ (m * n) = (a ^ m) ^ n
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
theorem zpow_mul' (a : α) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m := by rw [mul_comm, zpow_mul]
#align zpow_mul' zpow_mul'
#align mul_zsmul mul_zsmul

section bit0

set_option linter.deprecated false

@[to_additive bit0_zsmul]
theorem zpow_bit0 (a : α) : ∀ n : ℤ, a ^ bit0 n = a ^ n * a ^ n
  | (n : ℕ) => by simp only [zpow_ofNat, ← Int.ofNat_bit0, pow_bit0]
  | -[n+1] => by
    simp only [zpow_negSucc, <-mul_inv_rev, <-pow_bit0]
    rw [negSucc_eq, bit0_neg, zpow_neg]
    norm_cast
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
#align zpow_bit0_neg zpow_bit0_neg

end bit0

end DivisionMonoid

section Group

variable [Group G]

@[to_additive add_one_zsmul]
theorem zpow_add_one (a : G) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
  | (n : ℕ) => by simp only [← Int.ofNat_succ, zpow_ofNat, pow_succ']
  | -[0+1] => by erw [zpow_zero, zpow_negSucc, pow_one, mul_left_inv]
  | -[n + 1+1] => by
    rw [zpow_negSucc, pow_succ, mul_inv_rev, inv_mul_cancel_right]
    rw [Int.negSucc_eq, neg_add, add_assoc, neg_add_self, add_zero]
    exact zpow_negSucc _ _
#align zpow_add_one zpow_add_one
#align add_one_zsmul add_one_zsmul

@[to_additive sub_one_zsmul]
theorem zpow_sub_one (a : G) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
  calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := (mul_inv_cancel_right _ _).symm
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one, sub_add_cancel]
#align zpow_sub_one zpow_sub_one
#align sub_one_zsmul sub_one_zsmul

@[to_additive add_zsmul]
theorem zpow_add (a : G) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n using Int.induction_on with
  | hz => simp
  | hp n ihn => simp only [← add_assoc, zpow_add_one, ihn, mul_assoc]
  | hn n ihn => rw [zpow_sub_one, ← mul_assoc, ← ihn, ← zpow_sub_one, add_sub_assoc]
#align zpow_add zpow_add
#align add_zsmul add_zsmul

@[to_additive add_zsmul_self]
theorem mul_self_zpow (b : G) (m : ℤ) : b * b ^ m = b ^ (m + 1) := by
  conv_lhs =>
    congr
    rw [← zpow_one b]
  rw [← zpow_add, add_comm]
#align mul_self_zpow mul_self_zpow
#align add_zsmul_self add_zsmul_self

@[to_additive add_self_zsmul]
theorem mul_zpow_self (b : G) (m : ℤ) : b ^ m * b = b ^ (m + 1) := by
  conv_lhs =>
    congr
    · skip
    rw [← zpow_one b]
  rw [← zpow_add, add_comm]
#align mul_zpow_self mul_zpow_self
#align add_self_zsmul add_self_zsmul

@[to_additive sub_zsmul]
theorem zpow_sub (a : G) (m n : ℤ) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  rw [sub_eq_add_neg, zpow_add, zpow_neg]
#align zpow_sub zpow_sub
#align sub_zsmul sub_zsmul

@[to_additive one_add_zsmul]
theorem zpow_one_add (a : G) (i : ℤ) : a ^ (1 + i) = a * a ^ i := by rw [zpow_add, zpow_one]
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
  · rw [add_comm, zpow_add, zpow_one]
    exact h_mul _ ih
  · rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one]
    exact h_inv _ ih
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
  · rw [zpow_add_one]
    exact h_mul _ ih
  · rw [zpow_sub_one]
    exact h_inv _ ih
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
  rw [hn, zpow_ofNat]
  refine' one_lt_pow' ha (coe_nat_pos.mp _).ne'
  rwa [← hn]
#align one_lt_zpow' one_lt_zpow'
#align zsmul_pos zsmul_pos

@[to_additive zsmul_strictMono_left]
theorem zpow_right_strictMono (ha : 1 < a) : StrictMono fun n : ℤ => a ^ n := fun m n h =>
  calc
    a ^ m = a ^ m * 1 := (mul_one _).symm
    _ < a ^ m * a ^ (n - m) := mul_lt_mul_left' (one_lt_zpow' ha <| sub_pos_of_lt h) _
    _ = a ^ n := by rw [← zpow_add]; simp
#align zpow_strict_mono_right zpow_right_strictMono
#align zsmul_strict_mono_left zsmul_strictMono_left

@[to_additive zsmul_mono_left]
theorem zpow_mono_right (ha : 1 ≤ a) : Monotone fun n : ℤ => a ^ n := fun m n h =>
  calc
    a ^ m = a ^ m * 1 := (mul_one _).symm
    _ ≤ a ^ m * a ^ (n - m) := mul_le_mul_left' (one_le_zpow ha <| sub_nonneg_of_le h) _
    _ = a ^ n := by rw [← zpow_add]; simp
#align zpow_mono_right zpow_mono_right
#align zsmul_mono_left zsmul_mono_left

@[to_additive]
theorem zpow_le_zpow (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n :=
  zpow_mono_right ha h
#align zpow_le_zpow zpow_le_zpow
#align zsmul_le_zsmul zsmul_le_zsmul

@[to_additive]
theorem zpow_lt_zpow (ha : 1 < a) (h : m < n) : a ^ m < a ^ n :=
  zpow_right_strictMono ha h
#align zpow_lt_zpow zpow_lt_zpow
#align zsmul_lt_zsmul zsmul_lt_zsmul

@[to_additive]
theorem zpow_le_zpow_iff (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n :=
  (zpow_right_strictMono ha).le_iff_le
#align zpow_le_zpow_iff zpow_le_zpow_iff
#align zsmul_le_zsmul_iff zsmul_le_zsmul_iff

@[to_additive]
theorem zpow_lt_zpow_iff (ha : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  (zpow_right_strictMono ha).lt_iff_lt
#align zpow_lt_zpow_iff zpow_lt_zpow_iff
#align zsmul_lt_zsmul_iff zsmul_lt_zsmul_iff

variable (α)

@[to_additive zsmul_strictMono_right]
theorem zpow_strictMono_left (hn : 0 < n) : StrictMono ((· ^ n) : α → α) := fun a b hab => by
  rw [← one_lt_div', ← div_zpow]
  exact one_lt_zpow' (one_lt_div'.2 hab) hn
#align zpow_strict_mono_left zpow_strictMono_left
#align zsmul_strict_mono_right zsmul_strictMono_right

@[to_additive zsmul_mono_right]
theorem zpow_mono_left (hn : 0 ≤ n) : Monotone ((· ^ n) : α → α) := fun a b hab => by
  rw [← one_le_div', ← div_zpow]
  exact one_le_zpow (one_le_div'.2 hab) hn
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
  · exact (zpow_strictMono_left α h).injective
  · refine' fun a b (hab : a ^ n = b ^ n) => (zpow_strictMono_left α (neg_pos.mpr h)).injective _
    rw [zpow_neg, zpow_neg, hab]
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
  rcases le_total a 0 with hneg | hpos
  · rw [abs_of_nonpos hneg, ← abs_neg, ← neg_nsmul, abs_of_nonneg]
    exact nsmul_nonneg (neg_nonneg.mpr hneg) n
  · rw [abs_of_nonneg hpos, abs_of_nonneg]
    exact nsmul_nonneg hpos n
#align abs_nsmul abs_nsmul

theorem abs_zsmul (n : ℤ) (a : α) : |n • a| = |n| • |a| := by
  obtain n0 | n0 := le_total 0 n
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le n0
    simp only [abs_nsmul, coe_nat_zsmul, Nat.abs_cast]
  · obtain ⟨m, h⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 n0)
    rw [← abs_neg, ← neg_zsmul, ← abs_neg n, h, coe_nat_zsmul, Nat.abs_cast, coe_nat_zsmul]
    exact abs_nsmul m _
#align abs_zsmul abs_zsmul

theorem abs_add_eq_add_abs_le (hle : a ≤ b) :
    |a + b| = |a| + |b| ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  obtain a0 | a0 := le_or_lt 0 a <;> obtain b0 | b0 := le_or_lt 0 b
  · simp [a0, b0, abs_of_nonneg, add_nonneg a0 b0]
  · exact (lt_irrefl (0 : α) <| a0.trans_lt <| hle.trans_lt b0).elim
  any_goals simp [a0.le, b0.le, abs_of_nonpos, add_nonpos, add_comm]
  have : (|a + b| = -a + b ↔ b ≤ 0) ↔ (|a + b| = |a| + |b| ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0) := by
    simp [a0, a0.le, a0.not_le, b0, abs_of_neg, abs_of_nonneg]
  refine' this.mp ⟨fun h => _, fun h => by simp only [le_antisymm h b0, abs_of_neg a0, add_zero]⟩
  obtain ab | ab := le_or_lt (a + b) 0
  · refine' le_of_eq (eq_zero_of_neg_eq _)
    rwa [abs_of_nonpos ab, neg_add_rev, add_comm, add_right_inj] at h
  · refine' (lt_irrefl (0 : α) _).elim
    rw [abs_of_pos ab, add_left_inj] at h
    rwa [eq_zero_of_neg_eq h.symm] at a0
#align abs_add_eq_add_abs_le abs_add_eq_add_abs_le

theorem abs_add_eq_add_abs_iff (a b : α) : |a + b| = |a| + |b| ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  obtain ab | ab := le_total a b
  · exact abs_add_eq_add_abs_le ab
  · rw [add_comm a, add_comm (abs _), abs_add_eq_add_abs_le ab, and_comm, @and_comm (b ≤ 0)]
#align abs_add_eq_add_abs_iff abs_add_eq_add_abs_iff

end LinearOrderedAddCommGroup

section bit0_bit1

set_option linter.deprecated false

-- The next four lemmas allow us to replace multiplication by a numeral with a `zsmul` expression.
-- They are used by the `noncomm_ring` tactic, to normalise expressions before passing to `abel`.
theorem bit0_mul [NonUnitalNonAssocRing R] {n r : R} : bit0 n * r = (2 : ℤ) • (n * r) := by
  dsimp [bit0]
  rw [add_mul, ← one_add_one_eq_two, add_zsmul, one_zsmul]
#align bit0_mul bit0_mul

theorem mul_bit0 [NonUnitalNonAssocRing R] {n r : R} : r * bit0 n = (2 : ℤ) • (r * n) := by
  dsimp [bit0]
  rw [mul_add, ← one_add_one_eq_two, add_zsmul, one_zsmul]
#align mul_bit0 mul_bit0

theorem bit1_mul [NonAssocRing R] {n r : R} : bit1 n * r = (2 : ℤ) • (n * r) + r := by
  dsimp [bit1]
  rw [add_mul, bit0_mul, one_mul]
#align bit1_mul bit1_mul

theorem mul_bit1 [NonAssocRing R] {n r : R} : r * bit1 n = (2 : ℤ) • (r * n) + r := by
  dsimp [bit1]
  rw [mul_add, mul_bit0, mul_one]
#align mul_bit1 mul_bit1

end bit0_bit1

/-- Note this holds in marginally more generality than `Int.cast_mul` -/
theorem Int.cast_mul_eq_zsmul_cast [AddCommGroupWithOne α] :
    ∀ m n, ((m * n : ℤ) : α) = m • (n : α) :=
  fun m =>
  Int.inductionOn' m 0 (by simp) (fun k _ ih n => by simp [add_mul, add_zsmul, ih]) fun k _ ih n =>
    by simp [sub_mul, sub_zsmul, ih, ← sub_eq_add_neg]
#align int.cast_mul_eq_zsmul_cast Int.cast_mul_eq_zsmul_cast

theorem neg_one_pow_eq_pow_mod_two [Ring R] {n : ℕ} : (-1 : R) ^ n = (-1) ^ (n % 2) := by
  rw [← Nat.mod_add_div n 2, pow_add, pow_mul]; simp [sq]
#align neg_one_pow_eq_pow_mod_two neg_one_pow_eq_pow_mod_two

section OrderedSemiring

variable [OrderedSemiring R] {a : R}

theorem pow_le_pow_of_le_one_aux (h : 0 ≤ a) (ha : a ≤ 1) (i : ℕ) :
    ∀ k : ℕ, a ^ (i + k) ≤ a ^ i
  | 0 => by simp
  | k + 1 => by
    rw [← add_assoc, ← one_mul (a ^ i), pow_succ]
    exact mul_le_mul ha (pow_le_pow_of_le_one_aux h ha _ _) (pow_nonneg h _) zero_le_one
-- Porting note: no #align because private in Lean 3

theorem pow_le_pow_of_le_one (h : 0 ≤ a) (ha : a ≤ 1) {i j : ℕ} (hij : i ≤ j) : a ^ j ≤ a ^ i := by
  let ⟨k, hk⟩ := Nat.exists_eq_add_of_le hij
  rw [hk]; exact pow_le_pow_of_le_one_aux h ha _ _
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
  refine' this.eq_or_lt.elim (fun h => Or.inl h.symm) fun hC => Or.inr ⟨hC, _⟩
  refine' nonneg_of_mul_nonneg_right _ hC
  simpa only [pow_one] using h 1
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
  refine' ⟨_, _⟩
  · rintro (hpos | hz)
    · left
      exact hpos
    · right
      exact (pow_eq_zero_iff'.1 hz).1
  · rintro (hneg | hz)
    · left
      exact hneg
    · right
      simp [hz, bit1]
#align pow_bit1_nonpos_iff pow_bit1_nonpos_iff

@[simp]
theorem pow_bit1_pos_iff : 0 < a ^ bit1 n ↔ 0 < a :=
  lt_iff_lt_of_le_iff_le pow_bit1_nonpos_iff
#align pow_bit1_pos_iff pow_bit1_pos_iff

theorem strictMono_pow_bit1 (n : ℕ) : StrictMono fun a : R => a ^ bit1 n := by
  intro a b hab
  rcases le_total a 0 with ha | ha
  · rcases le_or_lt b 0 with hb | hb
    · rw [← neg_lt_neg_iff, ← neg_pow_bit1, ← neg_pow_bit1]
      exact pow_lt_pow_left (neg_lt_neg hab) (neg_nonneg.2 hb) n.bit1_ne_zero
    · exact (pow_bit1_nonpos_iff.2 ha).trans_lt (pow_bit1_pos_iff.2 hb)
  · exact pow_lt_pow_left hab ha n.bit1_ne_zero
#align strict_mono_pow_bit1 strictMono_pow_bit1

end bit1
end LinearOrderedRing

namespace Int

lemma natAbs_sq (x : ℤ) : (x.natAbs : ℤ) ^ 2 = x ^ 2 := by rw [sq, Int.natAbs_mul_self', sq]
#align int.nat_abs_sq Int.natAbs_sq

alias natAbs_pow_two := natAbs_sq
#align int.nat_abs_pow_two Int.natAbs_pow_two

theorem natAbs_le_self_sq (a : ℤ) : (Int.natAbs a : ℤ) ≤ a ^ 2 := by
  rw [← Int.natAbs_sq a, sq]
  norm_cast
  apply Nat.le_mul_self
#align int.abs_le_self_sq Int.natAbs_le_self_sq

alias natAbs_le_self_pow_two := natAbs_le_self_sq

theorem le_self_sq (b : ℤ) : b ≤ b ^ 2 :=
  le_trans le_natAbs (natAbs_le_self_sq _)
#align int.le_self_sq Int.le_self_sq

alias le_self_pow_two := le_self_sq
#align int.le_self_pow_two Int.le_self_pow_two

theorem pow_right_injective {x : ℤ} (h : 1 < x.natAbs) :
    Function.Injective ((x ^ ·) : ℕ → ℤ) := by
  suffices Function.Injective (natAbs ∘ (x ^ · : ℕ → ℤ)) by
    exact Function.Injective.of_comp this
  convert Nat.pow_right_injective h using 2
  rw [Function.comp_apply, natAbs_pow]
#align int.pow_right_injective Int.pow_right_injective

end Int

variable (M G A)

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

/-- Monoid homomorphisms from `Multiplicative ℤ` are defined by the image
of `Multiplicative.ofAdd 1`. -/
def zpowersHom [Group G] : G ≃ (Multiplicative ℤ →* G) :=
  Additive.ofMul.trans <| (zmultiplesHom _).trans <| AddMonoidHom.toMultiplicative''
#align zpowers_hom zpowersHom

attribute [to_additive existing zmultiplesHom] zpowersHom

variable {M G A}

theorem zpowersHom_apply [Group G] (x : G) (n : Multiplicative ℤ) :
    zpowersHom G x n = x ^ (Multiplicative.toAdd n) :=
  rfl
#align zpowers_hom_apply zpowersHom_apply

theorem zpowersHom_symm_apply [Group G] (f : Multiplicative ℤ →* G) :
    (zpowersHom G).symm f = f (Multiplicative.ofAdd 1) :=
  rfl
#align zpowers_hom_symm_apply zpowersHom_symm_apply

-- todo: can `to_additive` generate the following lemmas automatically?

theorem zmultiplesHom_apply [AddGroup A] (x : A) (n : ℤ) : zmultiplesHom A x n = n • x :=
  rfl
#align zmultiples_hom_apply zmultiplesHom_apply

attribute [to_additive existing (attr := simp) zmultiplesHom_apply] zpowersHom_apply

theorem zmultiplesHom_symm_apply [AddGroup A] (f : ℤ →+ A) : (zmultiplesHom A).symm f = f 1 :=
  rfl
#align zmultiples_hom_symm_apply zmultiplesHom_symm_apply

attribute [to_additive existing (attr := simp) zmultiplesHom_symm_apply] zpowersHom_symm_apply

theorem MonoidHom.apply_mint [Group M] (f : Multiplicative ℤ →* M) (n : Multiplicative ℤ) :
    f n = f (Multiplicative.ofAdd 1) ^ (Multiplicative.toAdd n) := by
  rw [← zpowersHom_symm_apply, ← zpowersHom_apply, Equiv.apply_symm_apply]
#align monoid_hom.apply_mint MonoidHom.apply_mint

/-! `MonoidHom.ext_mint` is defined in `Data.Int.Cast` -/

/-! `AddMonoidHom.ext_nat` is defined in `Data.Nat.Cast` -/

theorem AddMonoidHom.apply_int [AddGroup M] (f : ℤ →+ M) (n : ℤ) : f n = n • f 1 := by
  rw [← zmultiplesHom_symm_apply, ← zmultiplesHom_apply, Equiv.apply_symm_apply]
#align add_monoid_hom.apply_int AddMonoidHom.apply_int

/-! `AddMonoidHom.ext_int` is defined in `Data.Int.Cast` -/

variable (M G A)

/-- If `M` is commutative, `zpowersHom` is a multiplicative equivalence. -/
def zpowersMulHom [CommGroup G] : G ≃* (Multiplicative ℤ →* G) :=
  { zpowersHom G with map_mul' := fun a b => MonoidHom.ext fun n => by simp [mul_zpow] }
#align zpowers_mul_hom zpowersMulHom

/-- If `M` is commutative, `zmultiplesHom` is an additive equivalence. -/
def zmultiplesAddHom [AddCommGroup A] : A ≃+ (ℤ →+ A) :=
  { zmultiplesHom A with map_add' := fun a b => AddMonoidHom.ext fun n => by simp [zsmul_add] }
#align zmultiples_add_hom zmultiplesAddHom

variable {M G A}

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
theorem zmultiplesAddHom_apply [AddCommGroup A] (x : A) (n : ℤ) :
    zmultiplesAddHom A x n = n • x :=
  rfl
#align zmultiples_add_hom_apply zmultiplesAddHom_apply

@[simp]
theorem zmultiplesAddHom_symm_apply [AddCommGroup A] (f : ℤ →+ A) :
    (zmultiplesAddHom A).symm f = f 1 :=
  rfl
#align zmultiples_add_hom_symm_apply zmultiplesAddHom_symm_apply
@[simp] theorem pow_eq {m : ℤ} {n : ℕ} : m.pow n = m ^ n := by simp
