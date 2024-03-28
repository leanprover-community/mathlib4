/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.Algebra.GroupPower.CovariantClass
import Mathlib.Algebra.GroupPower.Ring
import Mathlib.Algebra.Order.Ring.Canonical

#align_import algebra.group_power.order from "leanprover-community/mathlib"@"00f91228655eecdcd3ac97a7fd8dbcb139fe990a"

/-!
# Lemmas about the interaction of power operations with order

Note that some lemmas are in `Algebra/GroupPower/Lemmas.lean` as they import files which
depend on this file.
-/

assert_not_exists Set.range

open Function Int

variable {α M R : Type*}

section OrderedCommGroup
variable [OrderedCommGroup α] {m n : ℤ} {a b : α}

@[to_additive zsmul_pos] lemma one_lt_zpow' (ha : 1 < a) (hn : 0 < n) : 1 < a ^ n := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
  rw [zpow_natCast]
  refine' one_lt_pow' ha ?_
  rintro rfl
  simp at hn
#align one_lt_zpow' one_lt_zpow'
#align zsmul_pos zsmul_pos

@[to_additive zsmul_strictMono_left]
lemma zpow_right_strictMono (ha : 1 < a) : StrictMono fun n : ℤ ↦ a ^ n := fun m n h ↦
  calc
    a ^ m = a ^ m * 1 := (mul_one _).symm
    _ < a ^ m * a ^ (n - m) := mul_lt_mul_left' (one_lt_zpow' ha <| Int.sub_pos_of_lt h) _
    _ = a ^ n := by simp [← zpow_add, m.add_comm]
#align zpow_strict_mono_right zpow_right_strictMono
#align zsmul_strict_mono_left zsmul_strictMono_left

@[to_additive zsmul_mono_left]
lemma zpow_mono_right (ha : 1 ≤ a) : Monotone fun n : ℤ ↦ a ^ n := fun m n h ↦
  calc
    a ^ m = a ^ m * 1 := (mul_one _).symm
    _ ≤ a ^ m * a ^ (n - m) := mul_le_mul_left' (one_le_zpow ha <| Int.sub_nonneg_of_le h) _
    _ = a ^ n := by simp [← zpow_add, m.add_comm]
#align zpow_mono_right zpow_mono_right
#align zsmul_mono_left zsmul_mono_left

@[to_additive (attr := gcongr)]
lemma zpow_le_zpow (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n := zpow_mono_right ha h
#align zpow_le_zpow zpow_le_zpow
#align zsmul_le_zsmul zsmul_le_zsmul

@[to_additive (attr := gcongr)]
lemma zpow_lt_zpow (ha : 1 < a) (h : m < n) : a ^ m < a ^ n := zpow_right_strictMono ha h
#align zpow_lt_zpow zpow_lt_zpow
#align zsmul_lt_zsmul zsmul_lt_zsmul

@[to_additive]
lemma zpow_le_zpow_iff (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n := (zpow_right_strictMono ha).le_iff_le
#align zpow_le_zpow_iff zpow_le_zpow_iff
#align zsmul_le_zsmul_iff zsmul_le_zsmul_iff

@[to_additive]
lemma zpow_lt_zpow_iff (ha : 1 < a) : a ^ m < a ^ n ↔ m < n := (zpow_right_strictMono ha).lt_iff_lt
#align zpow_lt_zpow_iff zpow_lt_zpow_iff
#align zsmul_lt_zsmul_iff zsmul_lt_zsmul_iff

variable (α)

@[to_additive zsmul_strictMono_right]
lemma zpow_strictMono_left (hn : 0 < n) : StrictMono ((· ^ n) : α → α) := fun a b hab => by
  rw [← one_lt_div', ← div_zpow]; exact one_lt_zpow' (one_lt_div'.2 hab) hn
#align zpow_strict_mono_left zpow_strictMono_left
#align zsmul_strict_mono_right zsmul_strictMono_right

@[to_additive zsmul_mono_right]
lemma zpow_mono_left (hn : 0 ≤ n) : Monotone ((· ^ n) : α → α) := fun a b hab => by
  rw [← one_le_div', ← div_zpow]; exact one_le_zpow (one_le_div'.2 hab) hn
#align zpow_mono_left zpow_mono_left
#align zsmul_mono_right zsmul_mono_right

variable {α}

@[to_additive (attr := gcongr)]
lemma zpow_le_zpow' (hn : 0 ≤ n) (h : a ≤ b) : a ^ n ≤ b ^ n := zpow_mono_left α hn h
#align zpow_le_zpow' zpow_le_zpow'
#align zsmul_le_zsmul' zsmul_le_zsmul'

@[to_additive (attr := gcongr)]
lemma zpow_lt_zpow' (hn : 0 < n) (h : a < b) : a ^ n < b ^ n := zpow_strictMono_left α hn h
#align zpow_lt_zpow' zpow_lt_zpow'
#align zsmul_lt_zsmul' zsmul_lt_zsmul'

end OrderedCommGroup

section LinearOrderedCommGroup

variable [LinearOrderedCommGroup α] {n : ℤ} {a b : α}

@[to_additive] lemma zpow_le_zpow_iff' (hn : 0 < n) : a ^ n ≤ b ^ n ↔ a ≤ b :=
  (zpow_strictMono_left α hn).le_iff_le
#align zpow_le_zpow_iff' zpow_le_zpow_iff'
#align zsmul_le_zsmul_iff' zsmul_le_zsmul_iff'

@[to_additive] lemma zpow_lt_zpow_iff' (hn : 0 < n) : a ^ n < b ^ n ↔ a < b :=
  (zpow_strictMono_left α hn).lt_iff_lt
#align zpow_lt_zpow_iff' zpow_lt_zpow_iff'
#align zsmul_lt_zsmul_iff' zsmul_lt_zsmul_iff'

@[to_additive zsmul_right_injective
"See also `smul_right_injective`. TODO: provide a `NoZeroSMulDivisors` instance. We can't do
that here because importing that definition would create import cycles."]
lemma zpow_left_injective (hn : n ≠ 0) : Injective ((· ^ n) : α → α) := by
  obtain hn | hn := hn.lt_or_lt
  · refine fun a b (hab : a ^ n = b ^ n) ↦
      (zpow_strictMono_left _ $ Int.neg_pos_of_neg hn).injective ?_
    rw [zpow_neg, zpow_neg, hab]
  · exact (zpow_strictMono_left _ hn).injective
#align zpow_left_injective zpow_left_injective
#align zsmul_right_injective zsmul_right_injective

@[to_additive zsmul_right_inj]
lemma zpow_left_inj (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := (zpow_left_injective hn).eq_iff
#align zpow_left_inj zpow_left_inj
#align zsmul_right_inj zsmul_right_inj

/-- Alias of `zpow_left_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'` and
`zsmul_lt_zsmul_iff'`. -/
@[to_additive "Alias of `zsmul_right_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'` and
`zsmul_lt_zsmul_iff'`."]
lemma zpow_eq_zpow_iff' (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := zpow_left_inj hn
#align zpow_eq_zpow_iff' zpow_eq_zpow_iff'
#align zsmul_eq_zsmul_iff' zsmul_eq_zsmul_iff'

end LinearOrderedCommGroup

namespace CanonicallyOrderedCommSemiring

variable [CanonicallyOrderedCommSemiring R]

theorem pow_pos {a : R} (H : 0 < a) (n : ℕ) : 0 < a ^ n :=
  pos_iff_ne_zero.2 <| pow_ne_zero _ H.ne'
#align canonically_ordered_comm_semiring.pow_pos CanonicallyOrderedCommSemiring.pow_pos

end CanonicallyOrderedCommSemiring

section OrderedSemiring

variable [OrderedSemiring R] {a b x y : R} {n m : ℕ}

theorem zero_pow_le_one : ∀ n : ℕ, (0 : R) ^ n ≤ 1
  | 0 => (pow_zero _).le
  | n + 1 => by rw [zero_pow n.succ_ne_zero]; exact zero_le_one
#align zero_pow_le_one zero_pow_le_one

theorem pow_add_pow_le (hx : 0 ≤ x) (hy : 0 ≤ y) (hn : n ≠ 0) : x ^ n + y ^ n ≤ (x + y) ^ n := by
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨k, rfl⟩
  induction' k with k ih;
  · have eqn : Nat.succ Nat.zero = 1 := rfl
    rw [eqn]
    simp only [pow_one, le_refl]
  · let n := k.succ
    have h1 := add_nonneg (mul_nonneg hx (pow_nonneg hy n)) (mul_nonneg hy (pow_nonneg hx n))
    have h2 := add_nonneg hx hy
    calc
      x ^ n.succ + y ^ n.succ ≤ x * x ^ n + y * y ^ n + (x * y ^ n + y * x ^ n) := by
        rw [pow_succ' _ n, pow_succ' _ n]
        exact le_add_of_nonneg_right h1
      _ = (x + y) * (x ^ n + y ^ n) := by
        rw [add_mul, mul_add, mul_add, add_comm (y * x ^ n), ← add_assoc, ← add_assoc,
          add_assoc (x * x ^ n) (x * y ^ n), add_comm (x * y ^ n) (y * y ^ n), ← add_assoc]
      _ ≤ (x + y) ^ n.succ := by
        rw [pow_succ' _ n]
        exact mul_le_mul_of_nonneg_left (ih (Nat.succ_ne_zero k)) h2
#align pow_add_pow_le pow_add_pow_le

theorem pow_le_one : ∀ n : ℕ, 0 ≤ a → a ≤ 1 → a ^ n ≤ 1
  | 0, _, _ => (pow_zero a).le
  | n + 1, h₀, h₁ => (pow_succ a n).le.trans (mul_le_one (pow_le_one n h₀ h₁) h₀ h₁)
#align pow_le_one pow_le_one

theorem pow_lt_one (h₀ : 0 ≤ a) (h₁ : a < 1) : ∀ {n : ℕ}, n ≠ 0 → a ^ n < 1
  | 0, h => (h rfl).elim
  | n + 1, _ => by
    rw [pow_succ']
    exact mul_lt_one_of_nonneg_of_lt_one_left h₀ h₁ (pow_le_one _ h₀ h₁.le)
#align pow_lt_one pow_lt_one

theorem one_le_pow_of_one_le (H : 1 ≤ a) : ∀ n : ℕ, 1 ≤ a ^ n
  | 0 => by rw [pow_zero]
  | n + 1 => by
    rw [pow_succ']
    simpa only [mul_one] using
      mul_le_mul H (one_le_pow_of_one_le H n) zero_le_one (le_trans zero_le_one H)
#align one_le_pow_of_one_le one_le_pow_of_one_le

theorem pow_right_mono (h : 1 ≤ a) : Monotone (a ^ ·) :=
  monotone_nat_of_le_succ fun n => by
    rw [pow_succ']
    exact le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans h) _) h
#align pow_mono pow_right_mono

@[gcongr]
theorem pow_le_pow_right (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m := pow_right_mono ha h
#align pow_le_pow pow_le_pow_right

theorem le_self_pow (ha : 1 ≤ a) (h : m ≠ 0) : a ≤ a ^ m := by
  simpa only [pow_one] using pow_le_pow_right ha <| Nat.pos_iff_ne_zero.2 h
#align self_le_pow le_self_pow
#align le_self_pow le_self_pow

@[mono, gcongr]
theorem pow_le_pow_left {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) : ∀ n, a ^ n ≤ b ^ n
  | 0 => by simp
  | n + 1 => by simpa only [pow_succ']
      using mul_le_mul hab (pow_le_pow_left ha hab _) (pow_nonneg ha _) (ha.trans hab)
#align pow_le_pow_of_le_left pow_le_pow_left

theorem one_lt_pow (ha : 1 < a) : ∀ {n : ℕ} (_ : n ≠ 0), 1 < a ^ n
  | 0, h => (h rfl).elim
  | n + 1, _ => by
    rw [pow_succ']
    exact one_lt_mul_of_lt_of_le ha (one_le_pow_of_one_le ha.le _)
#align one_lt_pow one_lt_pow

lemma pow_add_pow_le' (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ n + b ^ n ≤ 2 * (a + b) ^ n := by
  rw [two_mul]
  exact add_le_add (pow_le_pow_left ha (le_add_of_nonneg_right hb) _)
    (pow_le_pow_left hb (le_add_of_nonneg_left ha) _)

end OrderedSemiring

section StrictOrderedSemiring

variable [StrictOrderedSemiring R] {a x y : R} {n m : ℕ}

@[gcongr]
theorem pow_lt_pow_left (h : x < y) (hx : 0 ≤ x) : ∀ {n : ℕ}, n ≠ 0 → x ^ n < y ^ n
  | 0, hn => by contradiction
  | n + 1, _ => by
    simpa only [pow_succ] using
      mul_lt_mul_of_le_of_le' (pow_le_pow_left hx h.le _) h (pow_pos (hx.trans_lt h) _) hx
#align pow_lt_pow_of_lt_left pow_lt_pow_left

/-- See also `pow_left_strictMono` and `Nat.pow_left_strictMono`. -/
lemma pow_left_strictMonoOn (hn : n ≠ 0) : StrictMonoOn (· ^ n : R → R) {a | 0 ≤ a} :=
  fun _a ha _b _ hab ↦ pow_lt_pow_left hab ha hn
#align strict_mono_on_pow pow_left_strictMonoOn

/-- See also `pow_right_strictMono'`. -/
lemma pow_right_strictMono (h : 1 < a) : StrictMono (a ^ ·) :=
  have : 0 < a := zero_le_one.trans_lt h
  strictMono_nat_of_lt_succ fun n => by
    simpa only [one_mul, pow_succ'] using mul_lt_mul h (le_refl (a ^ n)) (pow_pos this _) this.le
#align pow_strict_mono_right pow_right_strictMono

@[gcongr]
theorem pow_lt_pow_right (h : 1 < a) (hmn : m < n) : a ^ m < a ^ n := pow_right_strictMono h hmn
#align pow_lt_pow_right pow_lt_pow_right
#align nat.pow_lt_pow_of_lt_right pow_lt_pow_right

lemma pow_lt_pow_iff_right (h : 1 < a) : a ^ n < a ^ m ↔ n < m := (pow_right_strictMono h).lt_iff_lt
#align pow_lt_pow_iff_ pow_lt_pow_iff_right

lemma pow_le_pow_iff_right (h : 1 < a) : a ^ n ≤ a ^ m ↔ n ≤ m := (pow_right_strictMono h).le_iff_le
#align pow_le_pow_iff pow_le_pow_iff_right

theorem lt_self_pow (h : 1 < a) (hm : 1 < m) : a < a ^ m := by
  simpa only [pow_one] using pow_lt_pow_right h hm

theorem pow_right_strictAnti (h₀ : 0 < a) (h₁ : a < 1) : StrictAnti (a ^ ·) :=
  strictAnti_nat_of_succ_lt fun n => by
    simpa only [pow_succ', one_mul] using mul_lt_mul h₁ le_rfl (pow_pos h₀ n) zero_le_one
#align strict_anti_pow pow_right_strictAnti

theorem pow_lt_pow_iff_right_of_lt_one (h₀ : 0 < a) (h₁ : a < 1) : a ^ m < a ^ n ↔ n < m :=
  (pow_right_strictAnti h₀ h₁).lt_iff_lt
#align pow_lt_pow_iff_of_lt_one pow_lt_pow_iff_right_of_lt_one

theorem pow_lt_pow_right_of_lt_one (h₀ : 0 < a) (h₁ : a < 1) (hmn : m < n) : a ^ n < a ^ m :=
  (pow_lt_pow_iff_right_of_lt_one h₀ h₁).2 hmn
#align pow_lt_pow_of_lt_one pow_lt_pow_right_of_lt_one

theorem pow_lt_self_of_lt_one (h₀ : 0 < a) (h₁ : a < 1) (hn : 1 < n) : a ^ n < a := by
  simpa only [pow_one] using pow_lt_pow_right_of_lt_one h₀ h₁ hn
#align pow_lt_self_of_lt_one pow_lt_self_of_lt_one

theorem sq_pos_of_pos (ha : 0 < a) : 0 < a ^ 2 := pow_pos ha _
#align sq_pos_of_pos sq_pos_of_pos

end StrictOrderedSemiring

section StrictOrderedRing
set_option linter.deprecated false

variable [StrictOrderedRing R] {a : R}

theorem pow_bit0_pos_of_neg (ha : a < 0) (n : ℕ) : 0 < a ^ bit0 n := by
  rw [pow_bit0']
  exact pow_pos (mul_pos_of_neg_of_neg ha ha) _
#align pow_bit0_pos_of_neg pow_bit0_pos_of_neg

theorem pow_bit1_neg (ha : a < 0) (n : ℕ) : a ^ bit1 n < 0 := by
  rw [bit1, pow_succ']
  exact mul_neg_of_neg_of_pos ha (pow_bit0_pos_of_neg ha n)
#align pow_bit1_neg pow_bit1_neg

theorem sq_pos_of_neg (ha : a < 0) : 0 < a ^ 2 :=
  pow_bit0_pos_of_neg ha 1
#align sq_pos_of_neg sq_pos_of_neg

end StrictOrderedRing

section LinearOrderedSemiring
variable [LinearOrderedSemiring R] {a b : R} {m n : ℕ}

lemma pow_le_pow_iff_left (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) : a ^ n ≤ b ^ n ↔ a ≤ b :=
  (pow_left_strictMonoOn hn).le_iff_le ha hb

lemma pow_lt_pow_iff_left (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) : a ^ n < b ^ n ↔ a < b :=
  (pow_left_strictMonoOn hn).lt_iff_lt ha hb

@[simp]
lemma pow_left_inj (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b :=
  (pow_left_strictMonoOn hn).eq_iff_eq ha hb
#align pow_left_inj pow_left_inj

lemma pow_right_injective (ha₀ : 0 < a) (ha₁ : a ≠ 1) : Injective (a ^ ·) := by
  obtain ha₁ | ha₁ := ha₁.lt_or_lt
  · exact (pow_right_strictAnti ha₀ ha₁).injective
  · exact (pow_right_strictMono ha₁).injective

@[simp]
lemma pow_right_inj (ha₀ : 0 < a) (ha₁ : a ≠ 1) : a ^ m = a ^ n ↔ m = n :=
  (pow_right_injective ha₀ ha₁).eq_iff

theorem pow_le_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n ≤ 1 ↔ a ≤ 1 := by
  simpa only [one_pow] using pow_le_pow_iff_left ha zero_le_one hn
#align pow_le_one_iff_of_nonneg pow_le_one_iff_of_nonneg

theorem one_le_pow_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : 1 ≤ a ^ n ↔ 1 ≤ a := by
  simpa only [one_pow] using pow_le_pow_iff_left (zero_le_one' R) ha hn
#align one_le_pow_iff_of_nonneg one_le_pow_iff_of_nonneg

theorem pow_lt_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n < 1 ↔ a < 1 :=
  lt_iff_lt_of_le_iff_le (one_le_pow_iff_of_nonneg ha hn)
#align pow_lt_one_iff_of_nonneg pow_lt_one_iff_of_nonneg

theorem one_lt_pow_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : 1 < a ^ n ↔ 1 < a := by
  simpa only [one_pow] using pow_lt_pow_iff_left (zero_le_one' R) ha hn
#align one_lt_pow_iff_of_nonneg one_lt_pow_iff_of_nonneg

lemma pow_eq_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 := by
  simpa only [one_pow] using pow_left_inj ha zero_le_one hn

theorem sq_le_one_iff {a : R} (ha : 0 ≤ a) : a ^ 2 ≤ 1 ↔ a ≤ 1 :=
  pow_le_one_iff_of_nonneg ha (Nat.succ_ne_zero _)
#align sq_le_one_iff sq_le_one_iff

theorem sq_lt_one_iff {a : R} (ha : 0 ≤ a) : a ^ 2 < 1 ↔ a < 1 :=
  pow_lt_one_iff_of_nonneg ha (Nat.succ_ne_zero _)
#align sq_lt_one_iff sq_lt_one_iff

theorem one_le_sq_iff {a : R} (ha : 0 ≤ a) : 1 ≤ a ^ 2 ↔ 1 ≤ a :=
  one_le_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)
#align one_le_sq_iff one_le_sq_iff

theorem one_lt_sq_iff {a : R} (ha : 0 ≤ a) : 1 < a ^ 2 ↔ 1 < a :=
  one_lt_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)
#align one_lt_sq_iff one_lt_sq_iff

theorem lt_of_pow_lt_pow_left (n : ℕ) (hb : 0 ≤ b) (h : a ^ n < b ^ n) : a < b :=
  lt_of_not_ge fun hn => not_lt_of_ge (pow_le_pow_left hb hn _) h
#align lt_of_pow_lt_pow lt_of_pow_lt_pow_left

theorem le_of_pow_le_pow_left (hn : n ≠ 0) (hb : 0 ≤ b) (h : a ^ n ≤ b ^ n) : a ≤ b :=
  le_of_not_lt fun h1 => not_le_of_lt (pow_lt_pow_left h1 hb hn) h
#align le_of_pow_le_pow le_of_pow_le_pow_left

@[simp]
theorem sq_eq_sq {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 = b ^ 2 ↔ a = b :=
  pow_left_inj ha hb (by decide)
#align sq_eq_sq sq_eq_sq

theorem lt_of_mul_self_lt_mul_self (hb : 0 ≤ b) : a * a < b * b → a < b := by
  simp_rw [← sq]
  exact lt_of_pow_lt_pow_left _ hb
#align lt_of_mul_self_lt_mul_self lt_of_mul_self_lt_mul_self

variable [ExistsAddOfLE R]

lemma add_sq_le : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  calc
    (a + b) ^ 2 = a ^ 2 + b ^ 2 + (a * b + b * a) := by
        simp_rw [pow_succ', pow_zero, mul_one, add_mul, mul_add, add_comm (b * a), add_add_add_comm]
    _ ≤ a ^ 2 + b ^ 2 + (a * a + b * b) := add_le_add_left ?_ _
    _ = _ := by simp_rw [pow_succ', pow_zero, mul_one, two_mul]
  cases le_total a b
  · exact mul_add_mul_le_mul_add_mul ‹_› ‹_›
  · exact mul_add_mul_le_mul_add_mul' ‹_› ‹_›

-- TODO: Use `gcongr`, `positivity`, `ring` once those tactics are made available here
lemma add_pow_le (ha : 0 ≤ a) (hb : 0 ≤ b) : ∀ n, (a + b) ^ n ≤ 2 ^ (n - 1) * (a ^ n + b ^ n)
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [pow_succ]
    calc
      _ ≤ 2 ^ n * (a ^ (n + 1) + b ^ (n + 1)) * (a + b) :=
          mul_le_mul_of_nonneg_right (add_pow_le ha hb (n + 1)) $ add_nonneg ha hb
      _ = 2 ^ n * (a ^ (n + 2) + b ^ (n + 2) + (a ^ (n + 1) * b + b ^ (n + 1) * a)) := by
          rw [mul_assoc, mul_add, add_mul, add_mul, ← pow_succ, ← pow_succ, add_comm _ (b ^ _),
            add_add_add_comm, add_comm (_ * a)]
      _ ≤ 2 ^ n * (a ^ (n + 2) + b ^ (n + 2) + (a ^ (n + 1) * a + b ^ (n + 1) * b)) :=
          mul_le_mul_of_nonneg_left (add_le_add_left ?_ _) $ pow_nonneg (zero_le_two (α := R)) _
      _ = _ := by simp only [← pow_succ, ← two_mul, ← mul_assoc]; rfl
    · obtain hab | hba := le_total a b
      · exact mul_add_mul_le_mul_add_mul (pow_le_pow_left ha hab _) hab
      · exact mul_add_mul_le_mul_add_mul' (pow_le_pow_left hb hba _) hba

-- TODO: State using `Even`
protected lemma Even.add_pow_le (hn : ∃ k, 2 * k = n) :
    (a + b) ^ n ≤ 2 ^ (n - 1) * (a ^ n + b ^ n) := by
  obtain ⟨n, rfl⟩ := hn
  rw [pow_mul]
  calc
    _ ≤ (2 * (a ^ 2 + b ^ 2)) ^ n := pow_le_pow_left (sq_nonneg _) add_sq_le _
    _ = 2 ^ n * (a ^ 2 + b ^ 2) ^ n := by -- TODO: Should be `Nat.cast_commute`
        rw [Commute.mul_pow]; simp [Commute, SemiconjBy, two_mul, mul_two]
    _ ≤ 2 ^ n * (2 ^ (n - 1) * ((a ^ 2) ^ n + (b ^ 2) ^ n)) := mul_le_mul_of_nonneg_left
          (add_pow_le (sq_nonneg _) (sq_nonneg _) _) $ pow_nonneg (zero_le_two (α := R)) _
    _ = _ := by simp only [← mul_assoc, ← pow_add, ← pow_mul]; cases n; rfl; simp [Nat.two_mul]

end LinearOrderedSemiring

section LinearOrderedRing
variable [LinearOrderedRing R] {a b : R} {n : ℕ}

section deprecated
set_option linter.deprecated false

theorem pow_bit0_nonneg (a : R) (n : ℕ) : 0 ≤ a ^ bit0 n := by
  rw [pow_bit0]
  exact mul_self_nonneg _
#align pow_bit0_nonneg pow_bit0_nonneg

theorem pow_bit0_pos {a : R} (h : a ≠ 0) (n : ℕ) : 0 < a ^ bit0 n :=
  (pow_bit0_nonneg a n).lt_of_ne (pow_ne_zero _ h).symm
#align pow_bit0_pos pow_bit0_pos

theorem sq_pos_of_ne_zero {R : Type*} [LinearOrderedSemiring R] [ExistsAddOfLE R]
    (a : R) (h : a ≠ 0) : 0 < a ^ 2 := by
  rwa [(sq_nonneg a).lt_iff_ne, ne_comm, pow_ne_zero_iff two_ne_zero]
#align sq_pos_of_ne_zero sq_pos_of_ne_zero

alias pow_two_pos_of_ne_zero := sq_pos_of_ne_zero
#align pow_two_pos_of_ne_zero pow_two_pos_of_ne_zero

theorem pow_bit0_pos_iff (a : R) {n : ℕ} (hn : n ≠ 0) : 0 < a ^ bit0 n ↔ a ≠ 0 := by
  refine' ⟨fun h => _, fun h => pow_bit0_pos h n⟩
  rintro rfl
  rw [zero_pow (Nat.bit0_ne_zero hn)] at h
  exact lt_irrefl _ h
#align pow_bit0_pos_iff pow_bit0_pos_iff

@[simp]
lemma pow_bit1_neg_iff : a ^ bit1 n < 0 ↔ a < 0 :=
  ⟨fun h ↦ not_le.1 fun h' => not_le.2 h <| pow_nonneg h' _, fun ha ↦ pow_bit1_neg ha n⟩
#align pow_bit1_neg_iff pow_bit1_neg_iff

@[simp]
lemma pow_bit1_nonneg_iff : 0 ≤ a ^ bit1 n ↔ 0 ≤ a := le_iff_le_iff_lt_iff_lt.2 pow_bit1_neg_iff
#align pow_bit1_nonneg_iff pow_bit1_nonneg_iff

@[simp]
lemma pow_bit1_nonpos_iff : a ^ bit1 n ≤ 0 ↔ a ≤ 0 := by
  simp only [le_iff_lt_or_eq, pow_bit1_neg_iff, pow_eq_zero_iff']; simp [bit1]
#align pow_bit1_nonpos_iff pow_bit1_nonpos_iff

@[simp]
lemma pow_bit1_pos_iff : 0 < a ^ bit1 n ↔ 0 < a := lt_iff_lt_of_le_iff_le pow_bit1_nonpos_iff
#align pow_bit1_pos_iff pow_bit1_pos_iff

lemma strictMono_pow_bit1 (n : ℕ) : StrictMono (· ^ bit1 n : R → R) := by
  intro a b hab
  rcases le_total a 0 with ha | ha
  · rcases le_or_lt b 0 with hb | hb
    · rw [← neg_lt_neg_iff, ← neg_pow_bit1, ← neg_pow_bit1]
      exact pow_lt_pow_left (neg_lt_neg hab) (neg_nonneg.2 hb) n.bit1_ne_zero
    · exact (pow_bit1_nonpos_iff.2 ha).trans_lt (pow_bit1_pos_iff.2 hb)
  · exact pow_lt_pow_left hab ha n.bit1_ne_zero
#align strict_mono_pow_bit1 strictMono_pow_bit1

end deprecated

lemma sq_pos_iff {R : Type*} [LinearOrderedSemiring R] [ExistsAddOfLE R] (a : R) :
    0 < a ^ 2 ↔ a ≠ 0 := by
  rw [← pow_ne_zero_iff two_ne_zero, (sq_nonneg a).lt_iff_ne, ne_comm]
#align sq_pos_iff sq_pos_iff

lemma pow_four_le_pow_two_of_pow_two_le (h : a ^ 2 ≤ b) : a ^ 4 ≤ b ^ 2 :=
  (pow_mul a 2 2).symm ▸ pow_le_pow_left (sq_nonneg a) h 2
#align pow_four_le_pow_two_of_pow_two_le pow_four_le_pow_two_of_pow_two_le

end LinearOrderedRing

namespace MonoidHom

variable [Ring R] [Monoid M] [LinearOrder M] [CovariantClass M M (· * ·) (· ≤ ·)] (f : R →* M)

theorem map_neg_one : f (-1) = 1 :=
  (pow_eq_one_iff (Nat.succ_ne_zero 1)).1 <| by rw [← map_pow, neg_one_sq, map_one]
#align monoid_hom.map_neg_one MonoidHom.map_neg_one

@[simp]
theorem map_neg (x : R) : f (-x) = f x := by rw [← neg_one_mul, map_mul, map_neg_one, one_mul]
#align monoid_hom.map_neg MonoidHom.map_neg

theorem map_sub_swap (x y : R) : f (x - y) = f (y - x) := by rw [← map_neg, neg_sub]
#align monoid_hom.map_sub_swap MonoidHom.map_sub_swap

end MonoidHom

namespace Nat
variable {n : ℕ} {f : α → ℕ}

/-- See also `pow_left_strictMonoOn`. -/
protected lemma pow_left_strictMono (hn : n ≠ 0) : StrictMono (. ^ n : ℕ → ℕ) :=
  fun _ _ h ↦ Nat.pow_lt_pow_left h hn
#align nat.pow_left_strict_mono Nat.pow_left_strictMono

lemma _root_.StrictMono.nat_pow [Preorder α] (hn : n ≠ 0) (hf : StrictMono f) :
    StrictMono (f · ^ n) := (Nat.pow_left_strictMono hn).comp hf
#align strict_mono.nat_pow StrictMono.nat_pow

end Nat

/-!
### Deprecated lemmas

Those lemmas have been deprecated on 2023-12-23.
-/

@[deprecated] alias pow_mono := pow_right_mono
@[deprecated] alias pow_le_pow := pow_le_pow_right
@[deprecated] alias pow_le_pow_of_le_left := pow_le_pow_left
@[deprecated] alias pow_lt_pow_of_lt_left := pow_lt_pow_left
@[deprecated] alias strictMonoOn_pow := pow_left_strictMonoOn
@[deprecated] alias pow_strictMono_right := pow_right_strictMono
@[deprecated] alias pow_lt_pow := pow_lt_pow_right
@[deprecated] alias pow_lt_pow_iff := pow_lt_pow_iff_right
@[deprecated] alias pow_le_pow_iff := pow_le_pow_iff_right
@[deprecated] alias self_lt_pow := lt_self_pow
@[deprecated] alias strictAnti_pow := pow_right_strictAnti
@[deprecated] alias pow_lt_pow_iff_of_lt_one := pow_lt_pow_iff_right_of_lt_one
@[deprecated] alias pow_lt_pow_of_lt_one := pow_lt_pow_right_of_lt_one
@[deprecated] alias lt_of_pow_lt_pow := lt_of_pow_lt_pow_left
@[deprecated] alias le_of_pow_le_pow := le_of_pow_le_pow_left
@[deprecated] alias self_le_pow := le_self_pow
@[deprecated] alias Nat.pow_lt_pow_of_lt_left := Nat.pow_lt_pow_left
@[deprecated] alias Nat.pow_le_iff_le_left := Nat.pow_le_pow_iff_left
@[deprecated] alias Nat.pow_lt_pow_of_lt_right := pow_lt_pow_right
@[deprecated] protected alias Nat.pow_right_strictMono := pow_right_strictMono
@[deprecated] alias Nat.pow_le_iff_le_right := pow_le_pow_iff_right
@[deprecated] alias Nat.pow_lt_iff_lt_right := pow_lt_pow_iff_right
