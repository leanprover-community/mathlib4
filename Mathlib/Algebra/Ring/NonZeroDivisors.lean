/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Regular.Basic
import Mathlib.Algebra.Regular.Opposite
import Mathlib.Algebra.Ring.Basic

/-!
# Non-zero divisors in a ring
-/

assert_not_exists Field

open scoped nonZeroDivisors

section Monoid

variable {R : Type*} [Monoid R] {r : R}

@[to_additive]
theorem IsLeftRegular.pow_injective [IsMulTorsionFree R]
    (hx : IsLeftRegular r) (hx' : r ≠ 1) : Function.Injective (fun n ↦ r ^ n) := by
  intro n m hnm
  have main {n m} (h₁ : n ≤ m) (h₂ : r ^ n = r ^ m) : n = m := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le h₁
    rw [pow_add, eq_comm, IsLeftRegular.mul_left_eq_self_iff (hx.pow n),
      IsMulTorsionFree.pow_eq_one_iff_right hx'] at h₂
    rw [h₂, Nat.add_zero]
  obtain h | h := Nat.le_or_le n m
  · exact main h hnm
  · exact (main h hnm.symm).symm

@[to_additive]
theorem IsRightRegular.pow_injective {M : Type*} [Monoid M] [IsMulTorsionFree M] {x : M}
    (hx : IsRightRegular x) (hx' : x ≠ 1) : Function.Injective (fun n ↦ x ^ n) :=
  MulOpposite.unop_injective.comp <| (isLeftRegular_op.mpr hx).pow_injective  <|
    (MulOpposite.op_eq_one_iff x).not.mpr hx'

theorem IsMulTorsionFree.pow_right_injective {M : Type*} [CancelMonoid M] [IsMulTorsionFree M]
    {x : M} (hx : x ≠ 1) : Function.Injective (fun n ↦ x ^ n) :=
  IsLeftRegular.pow_injective (IsLeftRegular.all x) hx

@[simp]
theorem IsMulTorsionFree.pow_right_inj {M : Type*} [CancelMonoid M] [IsMulTorsionFree M] {x : M}
    (hx : x ≠ 1) {n m : ℕ} : x ^ n = x ^ m ↔ n = m := (pow_right_injective hx).eq_iff

theorem IsMulTorsionFree.pow_right_injective₀ {M : Type*} [CancelMonoidWithZero M]
    [IsMulTorsionFree M] {x : M} (hx : x ≠ 1) (hx' : x ≠ 0) : Function.Injective (fun n ↦ x ^ n) :=
  IsLeftRegular.pow_injective (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hx') hx

@[simp]
theorem IsMulTorsionFree.pow_right_inj₀ {M : Type*} [CancelMonoidWithZero M] [IsMulTorsionFree M]
    {x : M} (hx : x ≠ 1) (hx' : x ≠ 0) {n m : ℕ} : x ^ n = x ^ m ↔ n = m :=
  (pow_right_injective₀ hx hx').eq_iff

variable [Finite R]

theorem IsLeftRegular.isUnit_of_finite (h : IsLeftRegular r) : IsUnit r := by
  rwa [IsUnit.isUnit_iff_mulLeft_bijective, ← Finite.injective_iff_bijective]

theorem IsRightRegular.isUnit_of_finite (h : IsRightRegular r) : IsUnit r := by
  rwa [IsUnit.isUnit_iff_mulRight_bijective, ← Finite.injective_iff_bijective]

theorem isRegular_iff_isUnit_of_finite : IsRegular r ↔ IsUnit r where
  mp h := h.1.isUnit_of_finite
  mpr h := h.isRegular

end Monoid

section Ring

variable {R : Type*} [Ring R] {a x y r : R}

lemma isLeftRegular_iff_mem_nonZeroDivisorsLeft : IsLeftRegular r ↔ r ∈ nonZeroDivisorsLeft R :=
  isLeftRegular_iff_right_eq_zero_of_mul

lemma isRightRegular_iff_mem_nonZeroDivisorsRight : IsRightRegular r ↔ r ∈ nonZeroDivisorsRight R :=
  isRightRegular_iff_left_eq_zero_of_mul

lemma isRegular_iff_mem_nonZeroDivisors : IsRegular r ↔ r ∈ R⁰ := isRegular_iff_eq_zero_of_mul

lemma le_nonZeroDivisorsLeft_iff_isLeftRegular {S : Submonoid R} :
    S ≤ nonZeroDivisorsLeft R ↔ ∀ s : S, IsLeftRegular (s : R) := by
  simp_rw [SetLike.le_def, isLeftRegular_iff_mem_nonZeroDivisorsLeft, Subtype.forall]

lemma le_nonZeroDivisorsRight_iff_isRightRegular {S : Submonoid R} :
    S ≤ nonZeroDivisorsRight R ↔ ∀ s : S, IsRightRegular (s : R) := by
  simp_rw [SetLike.le_def, isRightRegular_iff_mem_nonZeroDivisorsRight, Subtype.forall]

lemma le_nonZeroDivisors_iff_isRegular {S : Submonoid R} :
    S ≤ R⁰ ↔ ∀ s : S, IsRegular (s : R) := by
  simp_rw [nonZeroDivisors, le_inf_iff, le_nonZeroDivisorsLeft_iff_isLeftRegular,
    le_nonZeroDivisorsRight_iff_isRightRegular, isRegular_iff, forall_and]

@[deprecated (since := "2025-07-16")]
alias isLeftRegular_iff_mem_nonZeroDivisorsRight := isLeftRegular_iff_mem_nonZeroDivisorsLeft

@[deprecated (since := "2025-07-16")]
alias isRightRegular_iff_mem_nonZeroDivisorsLeft := isRightRegular_iff_mem_nonZeroDivisorsRight

@[deprecated (since := "2025-07-16")]
alias le_nonZeroDivisors_iff_isRightRegular := le_nonZeroDivisorsRight_iff_isRightRegular

lemma mul_cancel_left_mem_nonZeroDivisorsLeft (hr : r ∈ nonZeroDivisorsLeft R) :
    r * x = r * y ↔ x = y :=
  ⟨(isLeftRegular_iff_mem_nonZeroDivisorsLeft.mpr hr ·), congr_arg (r * ·)⟩

lemma mul_cancel_right_mem_nonZeroDivisorsRight (hr : r ∈ nonZeroDivisorsRight R) :
    x * r = y * r ↔ x = y :=
  ⟨(isRightRegular_iff_mem_nonZeroDivisorsRight.mpr hr ·), congr_arg (· * r)⟩

@[simp]
lemma mul_cancel_left_mem_nonZeroDivisors (hr : r ∈ R⁰) : r * x = r * y ↔ x = y :=
  mul_cancel_left_mem_nonZeroDivisorsLeft hr.1

lemma mul_cancel_left_coe_nonZeroDivisors {c : R⁰} : (c : R) * x = c * y ↔ x = y :=
  mul_cancel_left_mem_nonZeroDivisors c.prop

lemma mul_cancel_right_mem_nonZeroDivisors (hr : r ∈ R⁰) : x * r = y * r ↔ x = y :=
  mul_cancel_right_mem_nonZeroDivisorsRight hr.2

lemma mul_cancel_right_coe_nonZeroDivisors {c : R⁰} : x * c = y * c ↔ x = y :=
  mul_cancel_right_mem_nonZeroDivisors c.prop

/-- In a finite ring, an element is a unit iff it is a non-zero-divisor. -/
lemma isUnit_iff_mem_nonZeroDivisors_of_finite [Finite R] : IsUnit a ↔ a ∈ nonZeroDivisors R := by
  rw [← isRegular_iff_mem_nonZeroDivisors, isRegular_iff_isUnit_of_finite]

lemma dvd_cancel_left_mem_nonZeroDivisors (hr : r ∈ R⁰) : r * x ∣ r * y ↔ x ∣ y :=
  (isLeftRegular_iff_mem_nonZeroDivisorsLeft.mpr hr.1).dvd_cancel_left

lemma dvd_cancel_left_coe_nonZeroDivisors {c : R⁰} : c * x ∣ c * y ↔ x ∣ y :=
  dvd_cancel_left_mem_nonZeroDivisors c.prop

end Ring

section CommRing
variable {R : Type*} [CommRing R] {r x y : R}

lemma dvd_cancel_right_mem_nonZeroDivisors (hr : r ∈ R⁰) : x * r ∣ y * r ↔ x ∣ y := by
  simp_rw [← mul_comm r, dvd_cancel_left_mem_nonZeroDivisors hr]

lemma dvd_cancel_right_coe_nonZeroDivisors {c : R⁰} : x * c ∣ y * c ↔ x ∣ y :=
  dvd_cancel_right_mem_nonZeroDivisors c.prop

end CommRing
