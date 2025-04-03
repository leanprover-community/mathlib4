/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Big operators indexed by intervals

This file proves lemmas about `∏ x ∈ Ixx a b, f x` and `∑ x ∈ Ixx a b, f x`.
-/

variable {α β : Type*} [PartialOrder α] [CommMonoid β] {f : α → β} {a b : α}

namespace Finset
section LocallyFiniteOrder
variable [LocallyFiniteOrder α]

@[to_additive]
lemma left_mul_prod_Ioc (h : a ≤ b) : f a * ∏ x ∈ Ioc a b, f x = ∏ x ∈ Icc a b, f x := by
  rw [Icc_eq_cons_Ioc h, prod_cons]

@[to_additive]
lemma prod_Ioc_mul_left (h : a ≤ b) : (∏ x ∈ Ioc a b, f x) * f a = ∏ x ∈ Icc a b, f x := by
  rw [mul_comm, left_mul_prod_Ioc h]

@[to_additive]
lemma right_mul_prod_Ico (h : a ≤ b) : f b * ∏ x ∈ Ico a b, f x = ∏ x ∈ Icc a b, f x := by
  rw [Icc_eq_cons_Ico h, prod_cons]

@[to_additive]
lemma prod_Ico_mul_right (h : a ≤ b) : (∏ x ∈ Ico a b, f x) * f b = ∏ x ∈ Icc a b, f x := by
  rw [mul_comm, right_mul_prod_Ico h]

@[to_additive]
lemma left_mul_prod_Ioo (h : a < b) : f a * ∏ x ∈ Ioo a b, f x = ∏ x ∈ Ico a b, f x := by
  rw [Ico_eq_cons_Ioo h, prod_cons]

@[to_additive]
lemma prod_Ioo_mul_left (h : a < b) : (∏ x ∈ Ioo a b, f x) * f a = ∏ x ∈ Ico a b, f x := by
  rw [mul_comm, left_mul_prod_Ioo h]

@[to_additive]
lemma right_mul_prod_Ioo (h : a < b) : f b * ∏ x ∈ Ioo a b, f x = ∏ x ∈ Ioc a b, f x := by
  rw [Ioc_eq_cons_Ioo h, prod_cons]

@[to_additive]
lemma prod_Ioo_mul_right (h : a < b) : (∏ x ∈ Ioo a b, f x) * f b = ∏ x ∈ Ioc a b, f x := by
  rw [mul_comm, right_mul_prod_Ioo h]

end LocallyFiniteOrder

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α]

@[to_additive]
lemma left_mul_prod_Ioi (a : α) : f a * ∏ x ∈ Ioi a, f x = ∏ x ∈ Ici a, f x := by
  rw [Ici_eq_cons_Ioi, prod_cons]

@[to_additive]
lemma prod_Ioi_mul_left (a : α) : (∏ x ∈ Ioi a, f x) * f a = ∏ x ∈ Ici a, f x := by
  rw [mul_comm, left_mul_prod_Ioi]

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α]

@[to_additive]
lemma right_mul_prod_Iio (a : α) : f a * ∏ x ∈ Iio a, f x = ∏ x ∈ Iic a, f x := by
  rw [Iic_eq_cons_Iio, prod_cons]

@[to_additive]
lemma prod_Iio_mul_right (a : α) : (∏ x ∈ Iio a, f x) * f a = ∏ x ∈ Iic a, f x := by
  rw [mul_comm, right_mul_prod_Iio]

end LocallyFiniteOrderBot
end Finset
