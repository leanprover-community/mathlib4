/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.WithZero
import Mathlib.Algebra.GroupPower.CovariantClass
import Mathlib.Algebra.GroupPower.Ring
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Nat.Order.Basic

#align_import algebra.group_power.order from "leanprover-community/mathlib"@"00f91228655eecdcd3ac97a7fd8dbcb139fe990a"

/-!
# Lemmas about the interaction of power operations with order

Note that some lemmas are in `Algebra/GroupPower/Lemmas.lean` as they import files which
depend on this file.
-/

open Function

variable {M R : Type*}

namespace CanonicallyOrderedCommSemiring

variable [CanonicallyOrderedCommSemiring R]

theorem pow_pos {a : R} (H : 0 < a) (n : ℕ) : 0 < a ^ n :=
  pos_iff_ne_zero.2 <| pow_ne_zero _ H.ne'
#align canonically_ordered_comm_semiring.pow_pos CanonicallyOrderedCommSemiring.pow_pos

end CanonicallyOrderedCommSemiring

section OrderedSemiring

variable [OrderedSemiring R] {a x y : R} {n m : ℕ}

theorem zero_pow_le_one : ∀ n : ℕ, (0 : R) ^ n ≤ 1
  | 0 => (pow_zero _).le
  | n + 1 => by
    rw [zero_pow n.succ_pos]
    exact zero_le_one
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
        rw [pow_succ _ n, pow_succ _ n]
        exact le_add_of_nonneg_right h1
      _ = (x + y) * (x ^ n + y ^ n) := by
        rw [add_mul, mul_add, mul_add, add_comm (y * x ^ n), ← add_assoc, ← add_assoc,
          add_assoc (x * x ^ n) (x * y ^ n), add_comm (x * y ^ n) (y * y ^ n), ← add_assoc]
      _ ≤ (x + y) ^ n.succ := by
        rw [pow_succ _ n]
        exact mul_le_mul_of_nonneg_left (ih (Nat.succ_ne_zero k)) h2
#align pow_add_pow_le pow_add_pow_le

theorem pow_le_one : ∀ n : ℕ, 0 ≤ a → a ≤ 1 → a ^ n ≤ 1
  | 0, _, _ => (pow_zero a).le
  | n + 1, h₀, h₁ => (pow_succ' a n).le.trans (mul_le_one (pow_le_one n h₀ h₁) h₀ h₁)
#align pow_le_one pow_le_one

theorem pow_lt_one (h₀ : 0 ≤ a) (h₁ : a < 1) : ∀ {n : ℕ}, n ≠ 0 → a ^ n < 1
  | 0, h => (h rfl).elim
  | n + 1, _ => by
    rw [pow_succ]
    exact mul_lt_one_of_nonneg_of_lt_one_left h₀ h₁ (pow_le_one _ h₀ h₁.le)
#align pow_lt_one pow_lt_one

theorem one_le_pow_of_one_le (H : 1 ≤ a) : ∀ n : ℕ, 1 ≤ a ^ n
  | 0 => by rw [pow_zero]
  | n + 1 => by
    rw [pow_succ]
    simpa only [mul_one] using
      mul_le_mul H (one_le_pow_of_one_le H n) zero_le_one (le_trans zero_le_one H)
#align one_le_pow_of_one_le one_le_pow_of_one_le

theorem pow_right_mono (h : 1 ≤ a) : Monotone (a ^ ·) :=
  monotone_nat_of_le_succ fun n => by
    rw [pow_succ]
    exact le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans h) _) h
#align pow_mono pow_right_mono

theorem pow_le_pow_right (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m := pow_right_mono ha h
#align pow_le_pow pow_le_pow_right

theorem le_self_pow (ha : 1 ≤ a) (h : m ≠ 0) : a ≤ a ^ m := by
  simpa only [pow_one] using pow_le_pow_right ha <| pos_iff_ne_zero.2 h
#align self_le_pow le_self_pow
#align le_self_pow le_self_pow

@[mono]
theorem pow_le_pow_left {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) : ∀ n, a ^ n ≤ b ^ n
  | 0 => by simp
  | n + 1 => by simpa only [pow_succ]
      using mul_le_mul hab (pow_le_pow_left ha hab _) (pow_nonneg ha _) (ha.trans hab)
#align pow_le_pow_of_le_left pow_le_pow_left

theorem one_lt_pow (ha : 1 < a) : ∀ {n : ℕ} (_ : n ≠ 0), 1 < a ^ n
  | 0, h => (h rfl).elim
  | n + 1, _ => by
    rw [pow_succ]
    exact one_lt_mul_of_lt_of_le ha (one_le_pow_of_one_le ha.le _)
#align one_lt_pow one_lt_pow

end OrderedSemiring

section StrictOrderedSemiring

variable [StrictOrderedSemiring R] {a x y : R} {n m : ℕ}

theorem pow_lt_pow_left (h : x < y) (hx : 0 ≤ x) : ∀ {n : ℕ}, n ≠ 0 → x ^ n < y ^ n
  | 0, hn => by contradiction
  | n + 1, _ => by
    simpa only [pow_succ'] using mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
      (pow_le_pow_left hx h.le _) h hx (pow_pos (hx.trans_lt h) _)
#align pow_lt_pow_of_lt_left pow_lt_pow_left

/-- See also `pow_left_strictMonoOn`. -/
lemma pow_left_strictMonoOn (hn : n ≠ 0) : StrictMonoOn (· ^ n : R → R) (Set.Ici 0) :=
  fun _a ha _b _ hab ↦ pow_lt_pow_left hab ha hn
#align strict_mono_on_pow pow_left_strictMonoOn

/-- See also `pow_right_strictMono'`. -/
lemma pow_right_strictMono (h : 1 < a) : StrictMono (a ^ ·) :=
  have : 0 < a := zero_le_one.trans_lt h
  strictMono_nat_of_lt_succ fun n => by
    simpa only [one_mul, pow_succ] using mul_lt_mul h (le_refl (a ^ n)) (pow_pos this _) this.le
#align pow_strict_mono_right pow_right_strictMono

theorem pow_lt_pow_right (h : 1 < a) (hmn : m < n) : a ^ m < a ^ n := pow_right_strictMono h hmn
#align pow_lt_pow_right pow_lt_pow_right

lemma pow_lt_pow_iff_right (h : 1 < a) : a ^ n < a ^ m ↔ n < m := (pow_right_strictMono h).lt_iff_lt
#align pow_lt_pow_iff_ pow_lt_pow_iff_right

lemma pow_le_pow_iff_right (h : 1 < a) : a ^ n ≤ a ^ m ↔ n ≤ m := (pow_right_strictMono h).le_iff_le
#align pow_le_pow_iff pow_le_pow_iff_right

theorem lt_self_pow (h : 1 < a) (hm : 1 < m) : a < a ^ m := by
  simpa only [pow_one] using pow_lt_pow_right h hm

theorem pow_right_strictAnti (h₀ : 0 < a) (h₁ : a < 1) : StrictAnti (a ^ ·) :=
  strictAnti_nat_of_succ_lt fun n => by
    simpa only [pow_succ, one_mul] using mul_lt_mul h₁ le_rfl (pow_pos h₀ n) zero_le_one
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

theorem sq_pos_of_pos (ha : 0 < a) : 0 < a ^ 2 := by
  rw [sq]
  exact mul_pos ha ha
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
  rw [bit1, pow_succ]
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

end LinearOrderedSemiring

section LinearOrderedRing

variable [LinearOrderedRing R]

theorem pow_abs (a : R) (n : ℕ) : |a| ^ n = |a ^ n| :=
  ((absHom.toMonoidHom : R →* R).map_pow a n).symm
#align pow_abs pow_abs

theorem abs_neg_one_pow (n : ℕ) : |(-1 : R) ^ n| = 1 := by rw [← pow_abs, abs_neg, abs_one, one_pow]
#align abs_neg_one_pow abs_neg_one_pow

theorem abs_pow_eq_one (a : R) {n : ℕ} (h : n ≠ 0) : |a ^ n| = 1 ↔ |a| = 1 := by
  convert pow_left_inj (abs_nonneg a) zero_le_one h
  exacts [(pow_abs _ _).symm, (one_pow _).symm]
#align abs_pow_eq_one abs_pow_eq_one

section
set_option linter.deprecated false

theorem pow_bit0_nonneg (a : R) (n : ℕ) : 0 ≤ a ^ bit0 n := by
  rw [pow_bit0]
  exact mul_self_nonneg _
#align pow_bit0_nonneg pow_bit0_nonneg

theorem sq_nonneg (a : R) : 0 ≤ a ^ 2 :=
  pow_bit0_nonneg a 1
#align sq_nonneg sq_nonneg

alias pow_two_nonneg := sq_nonneg
#align pow_two_nonneg pow_two_nonneg

theorem pow_bit0_pos {a : R} (h : a ≠ 0) (n : ℕ) : 0 < a ^ bit0 n :=
  (pow_bit0_nonneg a n).lt_of_ne (pow_ne_zero _ h).symm
#align pow_bit0_pos pow_bit0_pos

theorem sq_pos_of_ne_zero (a : R) (h : a ≠ 0) : 0 < a ^ 2 :=
  pow_bit0_pos h 1
#align sq_pos_of_ne_zero sq_pos_of_ne_zero

alias pow_two_pos_of_ne_zero := sq_pos_of_ne_zero
#align pow_two_pos_of_ne_zero pow_two_pos_of_ne_zero

theorem pow_bit0_pos_iff (a : R) {n : ℕ} (hn : n ≠ 0) : 0 < a ^ bit0 n ↔ a ≠ 0 := by
  refine' ⟨fun h => _, fun h => pow_bit0_pos h n⟩
  rintro rfl
  rw [zero_pow (Nat.zero_lt_bit0 hn)] at h
  exact lt_irrefl _ h
#align pow_bit0_pos_iff pow_bit0_pos_iff

end

theorem sq_pos_iff (a : R) : 0 < a ^ 2 ↔ a ≠ 0 :=
  pow_bit0_pos_iff a one_ne_zero
#align sq_pos_iff sq_pos_iff

variable {x y : R}

-- Porting note: added `simp` to replace `pow_bit0_abs`
@[simp]
theorem sq_abs (x : R) : |x| ^ 2 = x ^ 2 := by simpa only [sq] using abs_mul_abs_self x
#align sq_abs sq_abs

theorem abs_sq (x : R) : |x ^ 2| = x ^ 2 := by simpa only [sq] using abs_mul_self x
#align abs_sq abs_sq

theorem sq_lt_sq : x ^ 2 < y ^ 2 ↔ |x| < |y| := by
  simpa only [sq_abs] using
    (pow_left_strictMonoOn two_ne_zero).lt_iff_lt (abs_nonneg x) (abs_nonneg y)
#align sq_lt_sq sq_lt_sq

theorem sq_lt_sq' (h1 : -y < x) (h2 : x < y) : x ^ 2 < y ^ 2 :=
  sq_lt_sq.2 (lt_of_lt_of_le (abs_lt.2 ⟨h1, h2⟩) (le_abs_self _))
#align sq_lt_sq' sq_lt_sq'

theorem sq_le_sq : x ^ 2 ≤ y ^ 2 ↔ |x| ≤ |y| := by
  simpa only [sq_abs] using
    (pow_left_strictMonoOn two_ne_zero).le_iff_le (abs_nonneg x) (abs_nonneg y)
#align sq_le_sq sq_le_sq

theorem sq_le_sq' (h1 : -y ≤ x) (h2 : x ≤ y) : x ^ 2 ≤ y ^ 2 :=
  sq_le_sq.2 (le_trans (abs_le.mpr ⟨h1, h2⟩) (le_abs_self _))
#align sq_le_sq' sq_le_sq'

theorem abs_lt_of_sq_lt_sq (h : x ^ 2 < y ^ 2) (hy : 0 ≤ y) : |x| < y := by
  rwa [← abs_of_nonneg hy, ← sq_lt_sq]
#align abs_lt_of_sq_lt_sq abs_lt_of_sq_lt_sq

theorem abs_lt_of_sq_lt_sq' (h : x ^ 2 < y ^ 2) (hy : 0 ≤ y) : -y < x ∧ x < y :=
  abs_lt.mp <| abs_lt_of_sq_lt_sq h hy
#align abs_lt_of_sq_lt_sq' abs_lt_of_sq_lt_sq'

theorem abs_le_of_sq_le_sq (h : x ^ 2 ≤ y ^ 2) (hy : 0 ≤ y) : |x| ≤ y := by
  rwa [← abs_of_nonneg hy, ← sq_le_sq]
#align abs_le_of_sq_le_sq abs_le_of_sq_le_sq

theorem abs_le_of_sq_le_sq' (h : x ^ 2 ≤ y ^ 2) (hy : 0 ≤ y) : -y ≤ x ∧ x ≤ y :=
  abs_le.mp <| abs_le_of_sq_le_sq h hy
#align abs_le_of_sq_le_sq' abs_le_of_sq_le_sq'

theorem sq_eq_sq_iff_abs_eq_abs (x y : R) : x ^ 2 = y ^ 2 ↔ |x| = |y| := by
  simp only [le_antisymm_iff, sq_le_sq]
#align sq_eq_sq_iff_abs_eq_abs sq_eq_sq_iff_abs_eq_abs

@[simp]
theorem sq_le_one_iff_abs_le_one (x : R) : x ^ 2 ≤ 1 ↔ |x| ≤ 1 := by
  simpa only [one_pow, abs_one] using @sq_le_sq _ _ x 1
#align sq_le_one_iff_abs_le_one sq_le_one_iff_abs_le_one

@[simp]
theorem sq_lt_one_iff_abs_lt_one (x : R) : x ^ 2 < 1 ↔ |x| < 1 := by
  simpa only [one_pow, abs_one] using @sq_lt_sq _ _ x 1
#align sq_lt_one_iff_abs_lt_one sq_lt_one_iff_abs_lt_one

@[simp]
theorem one_le_sq_iff_one_le_abs (x : R) : 1 ≤ x ^ 2 ↔ 1 ≤ |x| := by
  simpa only [one_pow, abs_one] using @sq_le_sq _ _ 1 x
#align one_le_sq_iff_one_le_abs one_le_sq_iff_one_le_abs

@[simp]
theorem one_lt_sq_iff_one_lt_abs (x : R) : 1 < x ^ 2 ↔ 1 < |x| := by
  simpa only [one_pow, abs_one] using @sq_lt_sq _ _ 1 x
#align one_lt_sq_iff_one_lt_abs one_lt_sq_iff_one_lt_abs

theorem pow_four_le_pow_two_of_pow_two_le {x y : R} (h : x ^ 2 ≤ y) : x ^ 4 ≤ y ^ 2 :=
  (pow_mul x 2 2).symm ▸ pow_le_pow_left (sq_nonneg x) h 2
#align pow_four_le_pow_two_of_pow_two_le pow_four_le_pow_two_of_pow_two_le

end LinearOrderedRing

section LinearOrderedCommRing

variable [LinearOrderedCommRing R]

/-- Arithmetic mean-geometric mean (AM-GM) inequality for linearly ordered commutative rings. -/
theorem two_mul_le_add_sq (a b : R) : 2 * a * b ≤ a ^ 2 + b ^ 2 :=
  sub_nonneg.mp ((sub_add_eq_add_sub _ _ _).subst ((sub_sq a b).subst (sq_nonneg _)))
#align two_mul_le_add_sq two_mul_le_add_sq

alias two_mul_le_add_pow_two := two_mul_le_add_sq
#align two_mul_le_add_pow_two two_mul_le_add_pow_two

end LinearOrderedCommRing

section LinearOrderedCommMonoidWithZero

variable [LinearOrderedCommMonoidWithZero M] [NoZeroDivisors M] {a : M} {n : ℕ}

theorem pow_pos_iff (hn : 0 < n) : 0 < a ^ n ↔ 0 < a := by
  simp_rw [zero_lt_iff, pow_ne_zero_iff hn]
#align pow_pos_iff pow_pos_iff

end LinearOrderedCommMonoidWithZero

section LinearOrderedCommGroupWithZero

variable [LinearOrderedCommGroupWithZero M] {a : M} {m n : ℕ}

theorem pow_lt_pow_succ (ha : 1 < a) : a ^ n < a ^ n.succ := by
  rw [← one_mul (a ^ n), pow_succ]
  exact mul_lt_right₀ _ ha (pow_ne_zero _ (zero_lt_one.trans ha).ne')
#align pow_lt_pow_succ pow_lt_pow_succ

theorem pow_lt_pow_right₀ (ha : 1 < a) (hmn : m < n) : a ^ m < a ^ n := by
  induction' hmn with n _ ih
  exacts [pow_lt_pow_succ ha, lt_trans ih (pow_lt_pow_succ ha)]
#align pow_lt_pow₀ pow_lt_pow_right₀

end LinearOrderedCommGroupWithZero

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
@[deprecated] alias pow_lt_pow₀ := pow_lt_pow_right₀
@[deprecated] alias self_le_pow := le_self_pow
