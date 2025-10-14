/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Module.Torsion.Free

/-!
# Pointwise operations of sets in a ring

This file proves properties of pointwise operations of sets in a ring.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

assert_not_exists OrderedAddCommMonoid Field

open Function
open scoped Pointwise

variable {α β : Type*}

namespace Set

section Monoid
variable [Monoid α] [AddGroup β] [DistribMulAction α β] (a : α) (s : Set α) (t : Set β)

@[simp]
lemma smul_set_neg : a • -t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg_eq_neg, image_image, smul_neg]

@[simp]
protected lemma smul_neg : s • -t = -(s • t) := by
  simp_rw [← image_neg_eq_neg]
  exact image_image2_right_comm smul_neg

end Monoid

section Semiring
variable [Semiring α] [AddCommMonoid β] [Module α β]

lemma add_smul_subset (a b : α) (s : Set β) : (a + b) • s ⊆ a • s + b • s := by
  rintro _ ⟨x, hx, rfl⟩
  simpa only [add_smul] using add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hx)

variable [Module.IsTorsionFree α β]

lemma zero_mem_smul_set_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t := by
  refine ⟨?_, zero_mem_smul_set⟩
  rintro ⟨b, hb, h⟩
  rwa [(eq_zero_or_eq_zero_of_smul_eq_zero h).resolve_left ha] at hb

end Semiring

section Ring
variable [Ring α] [AddCommGroup β] [Module α β] (a : α) (s : Set α) (t : Set β)

@[simp]
lemma neg_smul_set : -a • t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg_eq_neg, image_image, neg_smul]

@[simp]
protected lemma neg_smul : -s • t = -(s • t) := by
  simp_rw [← image_neg_eq_neg]
  exact image2_image_left_comm neg_smul

end Ring
end Set
