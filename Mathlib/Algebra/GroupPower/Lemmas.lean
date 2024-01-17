/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
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
