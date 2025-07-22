/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Regular.Basic
import Mathlib.Algebra.Ring.Defs

/-!
# Non-zero divisors in a ring
-/

assert_not_exists Field

open scoped nonZeroDivisors

section MonoidWithZero

variable {R : Type*} [MonoidWithZero R] {r : R}

theorem IsLeftRegular.mem_nonZeroDivisorsLeft (h : IsLeftRegular r) : r ∈ nonZeroDivisorsLeft R :=
  fun x hrx ↦ h (by simpa)

theorem IsRightRegular.mem_nonZeroDivisorsRight (h : IsRightRegular r) :
    r ∈ nonZeroDivisorsRight R :=
  fun x hrx ↦ h (by simpa)

end MonoidWithZero

section Monoid

variable {R : Type*} [Monoid R] [Finite R] {r : R}

theorem IsLeftRegular.isUnit_of_finite (h : IsLeftRegular r) : IsUnit r := by
  rwa [IsUnit.isUnit_iff_mulLeft_bijective, ← Finite.injective_iff_bijective]

theorem IsRightRegular.isUnit_of_finite (h : IsRightRegular r) : IsUnit r := by
  rwa [IsUnit.isUnit_iff_mulRight_bijective, ← Finite.injective_iff_bijective]

theorem isRegular_iff_isUnit_of_finite {r : R} : IsRegular r ↔ IsUnit r where
  mp h := h.1.isUnit_of_finite
  mpr h := h.isRegular

end Monoid

section Ring

variable {R : Type*} [Ring R] {a x y r : R}

lemma mul_cancel_left_mem_nonZeroDivisorsLeft (hr : r ∈ nonZeroDivisorsLeft R) :
    r * x = r * y ↔ x = y := by
  refine ⟨fun h ↦ ?_, congrArg (r * ·)⟩
  rw [← sub_eq_zero, ← mul_left_mem_nonZeroDivisorsLeft_eq_zero_iff hr, mul_sub, h, sub_self]

lemma mul_cancel_right_mem_nonZeroDivisorsRight (hr : r ∈ nonZeroDivisorsRight R) :
    x * r = y * r ↔ x = y := by
  refine ⟨fun h ↦ ?_, congrArg (· * r)⟩
  rw [← sub_eq_zero, ← mul_right_mem_nonZeroDivisorsRight_eq_zero_iff hr, sub_mul, h, sub_self]

lemma mul_cancel_right_mem_nonZeroDivisors (hr : r ∈ R⁰) : x * r = y * r ↔ x = y :=
  mul_cancel_right_mem_nonZeroDivisorsRight hr.2

lemma mul_cancel_right_coe_nonZeroDivisors {c : R⁰} : x * c = y * c ↔ x = y :=
  mul_cancel_right_mem_nonZeroDivisors c.prop

lemma isLeftRegular_iff_mem_nonZeroDivisorsLeft : IsLeftRegular r ↔ r ∈ nonZeroDivisorsLeft R :=
  ⟨fun h r' eq ↦ h (by simp_rw [eq, mul_zero]),
    fun h r₁ r₂ eq ↦ sub_eq_zero.mp <| h _ <| by simp_rw [mul_sub, eq, sub_self]⟩

lemma isRightRegular_iff_mem_nonZeroDivisorsRight : IsRightRegular r ↔ r ∈ nonZeroDivisorsRight R :=
  ⟨fun h r' eq ↦ h (by simp_rw [eq, zero_mul]),
    fun h r₁ r₂ eq ↦ sub_eq_zero.mp <| h _ <| by simp_rw [sub_mul, eq, sub_self]⟩

lemma isRegular_iff_mem_nonZeroDivisors : IsRegular r ↔ r ∈ R⁰ := by
  rw [isRegular_iff, isLeftRegular_iff_mem_nonZeroDivisorsLeft,
    isRightRegular_iff_mem_nonZeroDivisorsRight, nonZeroDivisors, Submonoid.mem_inf]

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

/-- In a finite ring, an element is a unit iff it is a non-zero-divisor. -/
lemma isUnit_iff_mem_nonZeroDivisors_of_finite [Finite R] : IsUnit a ↔ a ∈ nonZeroDivisors R := by
  rw [← isRegular_iff_mem_nonZeroDivisors, isRegular_iff_isUnit_of_finite]

end Ring

section CommRing
variable {R : Type*} [CommRing R] {r x y : R}

@[simp]
lemma mul_cancel_left_mem_nonZeroDivisors (hr : r ∈ R⁰) : r * x = r * y ↔ x = y := by
  simp_rw [mul_comm r, mul_cancel_right_mem_nonZeroDivisors hr]

lemma mul_cancel_left_coe_nonZeroDivisors {c : R⁰} : (c : R) * x = c * y ↔ x = y :=
  mul_cancel_left_mem_nonZeroDivisors c.prop

lemma dvd_cancel_right_mem_nonZeroDivisors (hr : r ∈ R⁰) : x * r ∣ y * r ↔ x ∣ y :=
  ⟨fun ⟨z, _⟩ ↦ ⟨z, by rwa [← mul_cancel_right_mem_nonZeroDivisors hr, mul_assoc, mul_comm z r,
    ← mul_assoc]⟩, fun ⟨z, h⟩ ↦ ⟨z, by rw [h, mul_assoc, mul_comm z r, ← mul_assoc]⟩⟩

lemma dvd_cancel_right_coe_nonZeroDivisors {c : R⁰} : x * c ∣ y * c ↔ x ∣ y :=
  dvd_cancel_right_mem_nonZeroDivisors c.prop

lemma dvd_cancel_left_mem_nonZeroDivisors (hr : r ∈ R⁰) : r * x ∣ r * y ↔ x ∣ y :=
  ⟨fun ⟨z, _⟩ ↦ ⟨z, by rwa [← mul_cancel_left_mem_nonZeroDivisors hr, ← mul_assoc]⟩,
    fun ⟨z, h⟩ ↦ ⟨z, by rw [h, ← mul_assoc]⟩⟩

lemma dvd_cancel_left_coe_nonZeroDivisors {c : R⁰} : c * x ∣ c * y ↔ x ∣ y :=
  dvd_cancel_left_mem_nonZeroDivisors c.prop

end CommRing
