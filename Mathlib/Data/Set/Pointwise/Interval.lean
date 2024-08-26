/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Algebra.Order.Interval.Set.Monoid
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.MinMax

/-!
# (Pre)images of intervals

In this file we prove a bunch of trivial lemmas like “if we add `a` to all points of `[b, c]`,
then we get `[a + b, a + c]`”. For the functions `x ↦ x ± a`, `x ↦ a ± x`, and `x ↦ -x` we prove
lemmas about preimages and images of all intervals. We also prove a few lemmas about images under
`x ↦ a * x`, `x ↦ x * a` and `x ↦ x⁻¹`.
-/


open Interval Pointwise

variable {α : Type*}

namespace Set

/-! ### Binary pointwise operations

Note that the subset operations below only cover the cases with the largest possible intervals on
the LHS: to conclude that `Ioo a b * Ioo c d ⊆ Ioo (a * c) (c * d)`, you can use monotonicity of `*`
and `Set.Ico_mul_Ioc_subset`.

TODO: repeat these lemmas for the generality of `mul_le_mul` (which assumes nonnegativity), which
the unprimed names have been reserved for
-/

section ContravariantLE

variable [Mul α] [Preorder α]
variable [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (Function.swap HMul.hMul) LE.le]

@[to_additive Icc_add_Icc_subset]
theorem Icc_mul_Icc_subset' (a b c d : α) : Icc a b * Icc c d ⊆ Icc (a * c) (b * d) := by
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_le_mul' hya hzc, mul_le_mul' hyb hzd⟩

@[to_additive Iic_add_Iic_subset]
theorem Iic_mul_Iic_subset' (a b : α) : Iic a * Iic b ⊆ Iic (a * b) := by
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_le_mul' hya hzb

@[to_additive Ici_add_Ici_subset]
theorem Ici_mul_Ici_subset' (a b : α) : Ici a * Ici b ⊆ Ici (a * b) := by
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_le_mul' hya hzb

end ContravariantLE

section ContravariantLT

variable [Mul α] [PartialOrder α]
variable [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (Function.swap HMul.hMul) LT.lt]

@[to_additive Icc_add_Ico_subset]
theorem Icc_mul_Ico_subset' (a b c d : α) : Icc a b * Ico c d ⊆ Ico (a * c) (b * d) := by
  haveI := covariantClass_le_of_lt
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_le_mul' hya hzc, mul_lt_mul_of_le_of_lt hyb hzd⟩

@[to_additive Ico_add_Icc_subset]
theorem Ico_mul_Icc_subset' (a b c d : α) : Ico a b * Icc c d ⊆ Ico (a * c) (b * d) := by
  haveI := covariantClass_le_of_lt
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_le_mul' hya hzc, mul_lt_mul_of_lt_of_le hyb hzd⟩

@[to_additive Ioc_add_Ico_subset]
theorem Ioc_mul_Ico_subset' (a b c d : α) : Ioc a b * Ico c d ⊆ Ioo (a * c) (b * d) := by
  haveI := covariantClass_le_of_lt
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_lt_mul_of_lt_of_le hya hzc, mul_lt_mul_of_le_of_lt hyb hzd⟩

@[to_additive Ico_add_Ioc_subset]
theorem Ico_mul_Ioc_subset' (a b c d : α) : Ico a b * Ioc c d ⊆ Ioo (a * c) (b * d) := by
  haveI := covariantClass_le_of_lt
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_lt_mul_of_le_of_lt hya hzc, mul_lt_mul_of_lt_of_le hyb hzd⟩

@[to_additive Iic_add_Iio_subset]
theorem Iic_mul_Iio_subset' (a b : α) : Iic a * Iio b ⊆ Iio (a * b) := by
  haveI := covariantClass_le_of_lt
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_le_of_lt hya hzb

@[to_additive Iio_add_Iic_subset]
theorem Iio_mul_Iic_subset' (a b : α) : Iio a * Iic b ⊆ Iio (a * b) := by
  haveI := covariantClass_le_of_lt
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_lt_of_le hya hzb

@[to_additive Ioi_add_Ici_subset]
theorem Ioi_mul_Ici_subset' (a b : α) : Ioi a * Ici b ⊆ Ioi (a * b) := by
  haveI := covariantClass_le_of_lt
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_lt_of_le hya hzb

@[to_additive Ici_add_Ioi_subset]
theorem Ici_mul_Ioi_subset' (a b : α) : Ici a * Ioi b ⊆ Ioi (a * b) := by
  haveI := covariantClass_le_of_lt
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_le_of_lt hya hzb

end ContravariantLT

section OrderedAddCommGroup

variable [OrderedAddCommGroup α] (a b c : α)

/-!
### Preimages under `x ↦ a + x`
-/


@[simp]
theorem preimage_const_add_Ici : (fun x => a + x) ⁻¹' Ici b = Ici (b - a) :=
  ext fun _x => sub_le_iff_le_add'.symm

@[simp]
theorem preimage_const_add_Ioi : (fun x => a + x) ⁻¹' Ioi b = Ioi (b - a) :=
  ext fun _x => sub_lt_iff_lt_add'.symm

@[simp]
theorem preimage_const_add_Iic : (fun x => a + x) ⁻¹' Iic b = Iic (b - a) :=
  ext fun _x => le_sub_iff_add_le'.symm

@[simp]
theorem preimage_const_add_Iio : (fun x => a + x) ⁻¹' Iio b = Iio (b - a) :=
  ext fun _x => lt_sub_iff_add_lt'.symm

@[simp]
theorem preimage_const_add_Icc : (fun x => a + x) ⁻¹' Icc b c = Icc (b - a) (c - a) := by
  simp [← Ici_inter_Iic]

@[simp]
theorem preimage_const_add_Ico : (fun x => a + x) ⁻¹' Ico b c = Ico (b - a) (c - a) := by
  simp [← Ici_inter_Iio]

@[simp]
theorem preimage_const_add_Ioc : (fun x => a + x) ⁻¹' Ioc b c = Ioc (b - a) (c - a) := by
  simp [← Ioi_inter_Iic]

@[simp]
theorem preimage_const_add_Ioo : (fun x => a + x) ⁻¹' Ioo b c = Ioo (b - a) (c - a) := by
  simp [← Ioi_inter_Iio]

/-!
### Preimages under `x ↦ x + a`
-/


@[simp]
theorem preimage_add_const_Ici : (fun x => x + a) ⁻¹' Ici b = Ici (b - a) :=
  ext fun _x => sub_le_iff_le_add.symm

@[simp]
theorem preimage_add_const_Ioi : (fun x => x + a) ⁻¹' Ioi b = Ioi (b - a) :=
  ext fun _x => sub_lt_iff_lt_add.symm

@[simp]
theorem preimage_add_const_Iic : (fun x => x + a) ⁻¹' Iic b = Iic (b - a) :=
  ext fun _x => le_sub_iff_add_le.symm

@[simp]
theorem preimage_add_const_Iio : (fun x => x + a) ⁻¹' Iio b = Iio (b - a) :=
  ext fun _x => lt_sub_iff_add_lt.symm

@[simp]
theorem preimage_add_const_Icc : (fun x => x + a) ⁻¹' Icc b c = Icc (b - a) (c - a) := by
  simp [← Ici_inter_Iic]

@[simp]
theorem preimage_add_const_Ico : (fun x => x + a) ⁻¹' Ico b c = Ico (b - a) (c - a) := by
  simp [← Ici_inter_Iio]

@[simp]
theorem preimage_add_const_Ioc : (fun x => x + a) ⁻¹' Ioc b c = Ioc (b - a) (c - a) := by
  simp [← Ioi_inter_Iic]

@[simp]
theorem preimage_add_const_Ioo : (fun x => x + a) ⁻¹' Ioo b c = Ioo (b - a) (c - a) := by
  simp [← Ioi_inter_Iio]

/-!
### Preimages under `x ↦ -x`
-/


@[simp]
theorem preimage_neg_Ici : -Ici a = Iic (-a) :=
  ext fun _x => le_neg

@[simp]
theorem preimage_neg_Iic : -Iic a = Ici (-a) :=
  ext fun _x => neg_le

@[simp]
theorem preimage_neg_Ioi : -Ioi a = Iio (-a) :=
  ext fun _x => lt_neg

@[simp]
theorem preimage_neg_Iio : -Iio a = Ioi (-a) :=
  ext fun _x => neg_lt

@[simp]
theorem preimage_neg_Icc : -Icc a b = Icc (-b) (-a) := by simp [← Ici_inter_Iic, inter_comm]

@[simp]
theorem preimage_neg_Ico : -Ico a b = Ioc (-b) (-a) := by
  simp [← Ici_inter_Iio, ← Ioi_inter_Iic, inter_comm]

@[simp]
theorem preimage_neg_Ioc : -Ioc a b = Ico (-b) (-a) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[simp]
theorem preimage_neg_Ioo : -Ioo a b = Ioo (-b) (-a) := by simp [← Ioi_inter_Iio, inter_comm]

/-!
### Preimages under `x ↦ x - a`
-/


@[simp]
theorem preimage_sub_const_Ici : (fun x => x - a) ⁻¹' Ici b = Ici (b + a) := by
  simp [sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Ioi : (fun x => x - a) ⁻¹' Ioi b = Ioi (b + a) := by
  simp [sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Iic : (fun x => x - a) ⁻¹' Iic b = Iic (b + a) := by
  simp [sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Iio : (fun x => x - a) ⁻¹' Iio b = Iio (b + a) := by
  simp [sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Icc : (fun x => x - a) ⁻¹' Icc b c = Icc (b + a) (c + a) := by
  simp [sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Ico : (fun x => x - a) ⁻¹' Ico b c = Ico (b + a) (c + a) := by
  simp [sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Ioc : (fun x => x - a) ⁻¹' Ioc b c = Ioc (b + a) (c + a) := by
  simp [sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Ioo : (fun x => x - a) ⁻¹' Ioo b c = Ioo (b + a) (c + a) := by
  simp [sub_eq_add_neg]

/-!
### Preimages under `x ↦ a - x`
-/


@[simp]
theorem preimage_const_sub_Ici : (fun x => a - x) ⁻¹' Ici b = Iic (a - b) :=
  ext fun _x => le_sub_comm

@[simp]
theorem preimage_const_sub_Iic : (fun x => a - x) ⁻¹' Iic b = Ici (a - b) :=
  ext fun _x => sub_le_comm

@[simp]
theorem preimage_const_sub_Ioi : (fun x => a - x) ⁻¹' Ioi b = Iio (a - b) :=
  ext fun _x => lt_sub_comm

@[simp]
theorem preimage_const_sub_Iio : (fun x => a - x) ⁻¹' Iio b = Ioi (a - b) :=
  ext fun _x => sub_lt_comm

@[simp]
theorem preimage_const_sub_Icc : (fun x => a - x) ⁻¹' Icc b c = Icc (a - c) (a - b) := by
  simp [← Ici_inter_Iic, inter_comm]

@[simp]
theorem preimage_const_sub_Ico : (fun x => a - x) ⁻¹' Ico b c = Ioc (a - c) (a - b) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[simp]
theorem preimage_const_sub_Ioc : (fun x => a - x) ⁻¹' Ioc b c = Ico (a - c) (a - b) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[simp]
theorem preimage_const_sub_Ioo : (fun x => a - x) ⁻¹' Ioo b c = Ioo (a - c) (a - b) := by
  simp [← Ioi_inter_Iio, inter_comm]

/-!
### Images under `x ↦ a + x`
-/


-- @[simp] -- Porting note (#10618): simp can prove this modulo `add_comm`
theorem image_const_add_Iic : (fun x => a + x) '' Iic b = Iic (a + b) := by simp [add_comm]

-- @[simp] -- Porting note (#10618): simp can prove this modulo `add_comm`
theorem image_const_add_Iio : (fun x => a + x) '' Iio b = Iio (a + b) := by simp [add_comm]

/-!
### Images under `x ↦ x + a`
-/


-- @[simp] -- Porting note (#10618): simp can prove this
theorem image_add_const_Iic : (fun x => x + a) '' Iic b = Iic (b + a) := by simp

-- @[simp] -- Porting note (#10618): simp can prove this
theorem image_add_const_Iio : (fun x => x + a) '' Iio b = Iio (b + a) := by simp

/-!
### Images under `x ↦ -x`
-/


theorem image_neg_Ici : Neg.neg '' Ici a = Iic (-a) := by simp

theorem image_neg_Iic : Neg.neg '' Iic a = Ici (-a) := by simp

theorem image_neg_Ioi : Neg.neg '' Ioi a = Iio (-a) := by simp

theorem image_neg_Iio : Neg.neg '' Iio a = Ioi (-a) := by simp

theorem image_neg_Icc : Neg.neg '' Icc a b = Icc (-b) (-a) := by simp

theorem image_neg_Ico : Neg.neg '' Ico a b = Ioc (-b) (-a) := by simp

theorem image_neg_Ioc : Neg.neg '' Ioc a b = Ico (-b) (-a) := by simp

theorem image_neg_Ioo : Neg.neg '' Ioo a b = Ioo (-b) (-a) := by simp

/-!
### Images under `x ↦ a - x`
-/


@[simp]
theorem image_const_sub_Ici : (fun x => a - x) '' Ici b = Iic (a - b) := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp_def] at this
  simp [sub_eq_add_neg, this, add_comm]

@[simp]
theorem image_const_sub_Iic : (fun x => a - x) '' Iic b = Ici (a - b) := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp_def] at this
  simp [sub_eq_add_neg, this, add_comm]

@[simp]
theorem image_const_sub_Ioi : (fun x => a - x) '' Ioi b = Iio (a - b) := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp_def] at this
  simp [sub_eq_add_neg, this, add_comm]

@[simp]
theorem image_const_sub_Iio : (fun x => a - x) '' Iio b = Ioi (a - b) := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp_def] at this
  simp [sub_eq_add_neg, this, add_comm]

@[simp]
theorem image_const_sub_Icc : (fun x => a - x) '' Icc b c = Icc (a - c) (a - b) := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp_def] at this
  simp [sub_eq_add_neg, this, add_comm]

@[simp]
theorem image_const_sub_Ico : (fun x => a - x) '' Ico b c = Ioc (a - c) (a - b) := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp_def] at this
  simp [sub_eq_add_neg, this, add_comm]

@[simp]
theorem image_const_sub_Ioc : (fun x => a - x) '' Ioc b c = Ico (a - c) (a - b) := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp_def] at this
  simp [sub_eq_add_neg, this, add_comm]

@[simp]
theorem image_const_sub_Ioo : (fun x => a - x) '' Ioo b c = Ioo (a - c) (a - b) := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp_def] at this
  simp [sub_eq_add_neg, this, add_comm]

/-!
### Images under `x ↦ x - a`
-/


@[simp]
theorem image_sub_const_Ici : (fun x => x - a) '' Ici b = Ici (b - a) := by simp [sub_eq_neg_add]

@[simp]
theorem image_sub_const_Iic : (fun x => x - a) '' Iic b = Iic (b - a) := by simp [sub_eq_neg_add]

@[simp]
theorem image_sub_const_Ioi : (fun x => x - a) '' Ioi b = Ioi (b - a) := by simp [sub_eq_neg_add]

@[simp]
theorem image_sub_const_Iio : (fun x => x - a) '' Iio b = Iio (b - a) := by simp [sub_eq_neg_add]

@[simp]
theorem image_sub_const_Icc : (fun x => x - a) '' Icc b c = Icc (b - a) (c - a) := by
  simp [sub_eq_neg_add]

@[simp]
theorem image_sub_const_Ico : (fun x => x - a) '' Ico b c = Ico (b - a) (c - a) := by
  simp [sub_eq_neg_add]

@[simp]
theorem image_sub_const_Ioc : (fun x => x - a) '' Ioc b c = Ioc (b - a) (c - a) := by
  simp [sub_eq_neg_add]

@[simp]
theorem image_sub_const_Ioo : (fun x => x - a) '' Ioo b c = Ioo (b - a) (c - a) := by
  simp [sub_eq_neg_add]

/-!
### Bijections
-/


theorem Iic_add_bij : BijOn (· + a) (Iic b) (Iic (b + a)) :=
  image_add_const_Iic a b ▸ (add_left_injective _).injOn.bijOn_image

theorem Iio_add_bij : BijOn (· + a) (Iio b) (Iio (b + a)) :=
  image_add_const_Iio a b ▸ (add_left_injective _).injOn.bijOn_image

end OrderedAddCommGroup

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] (a b c d : α)

@[simp]
theorem preimage_const_add_uIcc : (fun x => a + x) ⁻¹' [[b, c]] = [[b - a, c - a]] := by
  simp only [← Icc_min_max, preimage_const_add_Icc, min_sub_sub_right, max_sub_sub_right]

@[simp]
theorem preimage_add_const_uIcc : (fun x => x + a) ⁻¹' [[b, c]] = [[b - a, c - a]] := by
  simpa only [add_comm] using preimage_const_add_uIcc a b c

-- TODO: Why is the notation `-[[a, b]]` broken?
@[simp]
theorem preimage_neg_uIcc : @Neg.neg (Set α) Set.neg [[a, b]] = [[-a, -b]] := by
  simp only [← Icc_min_max, preimage_neg_Icc, min_neg_neg, max_neg_neg]

@[simp]
theorem preimage_sub_const_uIcc : (fun x => x - a) ⁻¹' [[b, c]] = [[b + a, c + a]] := by
  simp [sub_eq_add_neg]

@[simp]
theorem preimage_const_sub_uIcc : (fun x => a - x) ⁻¹' [[b, c]] = [[a - b, a - c]] := by
  simp_rw [← Icc_min_max, preimage_const_sub_Icc]
  simp only [sub_eq_add_neg, min_add_add_left, max_add_add_left, min_neg_neg, max_neg_neg]

-- @[simp] -- Porting note (#10618): simp can prove this module `add_comm`
theorem image_const_add_uIcc : (fun x => a + x) '' [[b, c]] = [[a + b, a + c]] := by simp [add_comm]

-- @[simp] -- Porting note (#10618): simp can prove this
theorem image_add_const_uIcc : (fun x => x + a) '' [[b, c]] = [[b + a, c + a]] := by simp

@[simp]
theorem image_const_sub_uIcc : (fun x => a - x) '' [[b, c]] = [[a - b, a - c]] := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp_def] at this
  simp [sub_eq_add_neg, this, add_comm]

@[simp]
theorem image_sub_const_uIcc : (fun x => x - a) '' [[b, c]] = [[b - a, c - a]] := by
  simp [sub_eq_add_neg, add_comm]

theorem image_neg_uIcc : Neg.neg '' [[a, b]] = [[-a, -b]] := by simp

variable {a b c d}

/-- If `[c, d]` is a subinterval of `[a, b]`, then the distance between `c` and `d` is less than or
equal to that of `a` and `b` -/
theorem abs_sub_le_of_uIcc_subset_uIcc (h : [[c, d]] ⊆ [[a, b]]) : |d - c| ≤ |b - a| := by
  rw [← max_sub_min_eq_abs, ← max_sub_min_eq_abs]
  rw [uIcc_subset_uIcc_iff_le] at h
  exact sub_le_sub h.2 h.1

/-- If `c ∈ [a, b]`, then the distance between `a` and `c` is less than or equal to
that of `a` and `b`  -/
theorem abs_sub_left_of_mem_uIcc (h : c ∈ [[a, b]]) : |c - a| ≤ |b - a| :=
  abs_sub_le_of_uIcc_subset_uIcc <| uIcc_subset_uIcc_left h

/-- If `x ∈ [a, b]`, then the distance between `c` and `b` is less than or equal to
that of `a` and `b`  -/
theorem abs_sub_right_of_mem_uIcc (h : c ∈ [[a, b]]) : |b - c| ≤ |b - a| :=
  abs_sub_le_of_uIcc_subset_uIcc <| uIcc_subset_uIcc_right h

end LinearOrderedAddCommGroup

/-!
### Multiplication and inverse in a field
-/


section LinearOrderedField

variable [LinearOrderedField α] {a : α}

@[simp]
theorem preimage_mul_const_Iio (a : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Iio a = Iio (a / c) :=
  ext fun _x => (lt_div_iff h).symm

@[simp]
theorem preimage_mul_const_Ioi (a : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ioi a = Ioi (a / c) :=
  ext fun _x => (div_lt_iff h).symm

@[simp]
theorem preimage_mul_const_Iic (a : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Iic a = Iic (a / c) :=
  ext fun _x => (le_div_iff₀ h).symm

@[simp]
theorem preimage_mul_const_Ici (a : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ici a = Ici (a / c) :=
  ext fun _x => (div_le_iff₀ h).symm

@[simp]
theorem preimage_mul_const_Ioo (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ioo a b = Ioo (a / c) (b / c) := by simp [← Ioi_inter_Iio, h]

@[simp]
theorem preimage_mul_const_Ioc (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ioc a b = Ioc (a / c) (b / c) := by simp [← Ioi_inter_Iic, h]

@[simp]
theorem preimage_mul_const_Ico (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ico a b = Ico (a / c) (b / c) := by simp [← Ici_inter_Iio, h]

@[simp]
theorem preimage_mul_const_Icc (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Icc a b = Icc (a / c) (b / c) := by simp [← Ici_inter_Iic, h]

@[simp]
theorem preimage_mul_const_Iio_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Iio a = Ioi (a / c) :=
  ext fun _x => (div_lt_iff_of_neg h).symm

@[simp]
theorem preimage_mul_const_Ioi_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioi a = Iio (a / c) :=
  ext fun _x => (lt_div_iff_of_neg h).symm

@[simp]
theorem preimage_mul_const_Iic_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Iic a = Ici (a / c) :=
  ext fun _x => (div_le_iff_of_neg h).symm

@[simp]
theorem preimage_mul_const_Ici_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ici a = Iic (a / c) :=
  ext fun _x => (le_div_iff_of_neg h).symm

@[simp]
theorem preimage_mul_const_Ioo_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioo a b = Ioo (b / c) (a / c) := by simp [← Ioi_inter_Iio, h, inter_comm]

@[simp]
theorem preimage_mul_const_Ioc_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioc a b = Ico (b / c) (a / c) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, h, inter_comm]

@[simp]
theorem preimage_mul_const_Ico_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ico a b = Ioc (b / c) (a / c) := by
  simp [← Ici_inter_Iio, ← Ioi_inter_Iic, h, inter_comm]

@[simp]
theorem preimage_mul_const_Icc_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Icc a b = Icc (b / c) (a / c) := by simp [← Ici_inter_Iic, h, inter_comm]

@[simp]
theorem preimage_const_mul_Iio (a : α) {c : α} (h : 0 < c) : (c * ·) ⁻¹' Iio a = Iio (a / c) :=
  ext fun _x => (lt_div_iff' h).symm

@[simp]
theorem preimage_const_mul_Ioi (a : α) {c : α} (h : 0 < c) : (c * ·) ⁻¹' Ioi a = Ioi (a / c) :=
  ext fun _x => (div_lt_iff' h).symm

@[simp]
theorem preimage_const_mul_Iic (a : α) {c : α} (h : 0 < c) : (c * ·) ⁻¹' Iic a = Iic (a / c) :=
  ext fun _x => (le_div_iff₀' h).symm

@[simp]
theorem preimage_const_mul_Ici (a : α) {c : α} (h : 0 < c) : (c * ·) ⁻¹' Ici a = Ici (a / c) :=
  ext fun _x => (div_le_iff₀' h).symm

@[simp]
theorem preimage_const_mul_Ioo (a b : α) {c : α} (h : 0 < c) :
    (c * ·) ⁻¹' Ioo a b = Ioo (a / c) (b / c) := by simp [← Ioi_inter_Iio, h]

@[simp]
theorem preimage_const_mul_Ioc (a b : α) {c : α} (h : 0 < c) :
    (c * ·) ⁻¹' Ioc a b = Ioc (a / c) (b / c) := by simp [← Ioi_inter_Iic, h]

@[simp]
theorem preimage_const_mul_Ico (a b : α) {c : α} (h : 0 < c) :
    (c * ·) ⁻¹' Ico a b = Ico (a / c) (b / c) := by simp [← Ici_inter_Iio, h]

@[simp]
theorem preimage_const_mul_Icc (a b : α) {c : α} (h : 0 < c) :
    (c * ·) ⁻¹' Icc a b = Icc (a / c) (b / c) := by simp [← Ici_inter_Iic, h]

@[simp]
theorem preimage_const_mul_Iio_of_neg (a : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Iio a = Ioi (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Iio_of_neg a h

@[simp]
theorem preimage_const_mul_Ioi_of_neg (a : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Ioi a = Iio (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioi_of_neg a h

@[simp]
theorem preimage_const_mul_Iic_of_neg (a : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Iic a = Ici (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Iic_of_neg a h

@[simp]
theorem preimage_const_mul_Ici_of_neg (a : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Ici a = Iic (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ici_of_neg a h

@[simp]
theorem preimage_const_mul_Ioo_of_neg (a b : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Ioo a b = Ioo (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioo_of_neg a b h

@[simp]
theorem preimage_const_mul_Ioc_of_neg (a b : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Ioc a b = Ico (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioc_of_neg a b h

@[simp]
theorem preimage_const_mul_Ico_of_neg (a b : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Ico a b = Ioc (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ico_of_neg a b h

@[simp]
theorem preimage_const_mul_Icc_of_neg (a b : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Icc a b = Icc (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Icc_of_neg a b h

@[simp]
theorem preimage_mul_const_uIcc (ha : a ≠ 0) (b c : α) :
    (· * a) ⁻¹' [[b, c]] = [[b / a, c / a]] :=
  (lt_or_gt_of_ne ha).elim
    (fun h => by
      simp [← Icc_min_max, h, h.le, min_div_div_right_of_nonpos, max_div_div_right_of_nonpos])
    fun ha : 0 < a => by simp [← Icc_min_max, ha, ha.le, min_div_div_right, max_div_div_right]

@[simp]
theorem preimage_const_mul_uIcc (ha : a ≠ 0) (b c : α) :
    (a * ·) ⁻¹' [[b, c]] = [[b / a, c / a]] := by
  simp only [← preimage_mul_const_uIcc ha, mul_comm]

@[simp]
theorem preimage_div_const_uIcc (ha : a ≠ 0) (b c : α) :
    (fun x => x / a) ⁻¹' [[b, c]] = [[b * a, c * a]] := by
  simp only [div_eq_mul_inv, preimage_mul_const_uIcc (inv_ne_zero ha), inv_inv]

@[simp]
theorem image_mul_const_uIcc (a b c : α) : (· * a) '' [[b, c]] = [[b * a, c * a]] :=
  if ha : a = 0 then by simp [ha]
  else calc
    (fun x => x * a) '' [[b, c]] = (· * a⁻¹) ⁻¹' [[b, c]] :=
      (Units.mk0 a ha).mulRight.image_eq_preimage _
    _ = (fun x => x / a) ⁻¹' [[b, c]] := by simp only [div_eq_mul_inv]
    _ = [[b * a, c * a]] := preimage_div_const_uIcc ha _ _

@[simp]
theorem image_const_mul_uIcc (a b c : α) : (a * ·) '' [[b, c]] = [[a * b, a * c]] := by
  simpa only [mul_comm] using image_mul_const_uIcc a b c

@[simp]
theorem image_div_const_uIcc (a b c : α) : (fun x => x / a) '' [[b, c]] = [[b / a, c / a]] := by
  simp only [div_eq_mul_inv, image_mul_const_uIcc]

theorem image_mul_right_Icc' (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) '' Icc a b = Icc (a * c) (b * c) :=
  ((Units.mk0 c h.ne').mulRight.image_eq_preimage _).trans (by simp [h, division_def])

theorem image_mul_right_Icc {a b c : α} (hab : a ≤ b) (hc : 0 ≤ c) :
    (fun x => x * c) '' Icc a b = Icc (a * c) (b * c) := by
  cases eq_or_lt_of_le hc
  · subst c
    simp [(nonempty_Icc.2 hab).image_const]
  exact image_mul_right_Icc' a b ‹0 < c›

theorem image_mul_left_Icc' {a : α} (h : 0 < a) (b c : α) :
    (a * ·) '' Icc b c = Icc (a * b) (a * c) := by
  convert image_mul_right_Icc' b c h using 1 <;> simp only [mul_comm _ a]

theorem image_mul_left_Icc {a b c : α} (ha : 0 ≤ a) (hbc : b ≤ c) :
    (a * ·) '' Icc b c = Icc (a * b) (a * c) := by
  convert image_mul_right_Icc hbc ha using 1 <;> simp only [mul_comm _ a]

theorem image_mul_right_Ioo (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) '' Ioo a b = Ioo (a * c) (b * c) :=
  ((Units.mk0 c h.ne').mulRight.image_eq_preimage _).trans (by simp [h, division_def])

theorem image_mul_left_Ioo {a : α} (h : 0 < a) (b c : α) :
    (a * ·) '' Ioo b c = Ioo (a * b) (a * c) := by
  convert image_mul_right_Ioo b c h using 1 <;> simp only [mul_comm _ a]

/-- The (pre)image under `inv` of `Ioo 0 a` is `Ioi a⁻¹`. -/
theorem inv_Ioo_0_left {a : α} (ha : 0 < a) : (Ioo 0 a)⁻¹ = Ioi a⁻¹ := by
  ext x
  exact
    ⟨fun h => inv_inv x ▸ (inv_lt_inv ha h.1).2 h.2, fun h =>
      ⟨inv_pos.2 <| (inv_pos.2 ha).trans h,
        inv_inv a ▸ (inv_lt_inv ((inv_pos.2 ha).trans h)
          (inv_pos.2 ha)).2 h⟩⟩

theorem inv_Ioi {a : α} (ha : 0 < a) : (Ioi a)⁻¹ = Ioo 0 a⁻¹ := by
  rw [inv_eq_iff_eq_inv, inv_Ioo_0_left (inv_pos.2 ha), inv_inv]

theorem image_const_mul_Ioi_zero {k : Type*} [LinearOrderedField k] {x : k} (hx : 0 < x) :
    (fun y => x * y) '' Ioi (0 : k) = Ioi 0 := by
  erw [(Units.mk0 x hx.ne').mulLeft.image_eq_preimage,
    preimage_const_mul_Ioi 0 (inv_pos.mpr hx), zero_div]

/-!
### Images under `x ↦ a * x + b`
-/


@[simp]
theorem image_affine_Icc' {a : α} (h : 0 < a) (b c d : α) :
    (a * · + b) '' Icc c d = Icc (a * c + b) (a * d + b) := by
  suffices (· + b) '' ((a * ·) '' Icc c d) = Icc (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Icc' h, image_add_const_Icc]

end LinearOrderedField

end Set
