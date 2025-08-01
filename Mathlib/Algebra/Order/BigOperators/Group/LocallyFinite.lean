/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Interval.Finset.Nat

/-!
# Big operators indexed by intervals

This file proves lemmas about `∏ x ∈ Ixx a b, f x` and `∑ x ∈ Ixx a b, f x`.
-/

open Order

variable {α M : Type*} [CommMonoid M] {f : α → M} {a b : α}

namespace Finset
section PartialOrder
variable [PartialOrder α]

section LocallyFiniteOrder
variable [LocallyFiniteOrder α]

@[to_additive]
lemma mul_prod_Ico_eq_prod_Icc (h : a ≤ b) : f b * ∏ x ∈ Ico a b, f x = ∏ x ∈ Icc a b, f x := by
  rw [Icc_eq_cons_Ico h, prod_cons]

@[deprecated (since := "2025-05-03")] alias right_mul_prod_Ico := mul_prod_Ico_eq_prod_Icc
@[deprecated (since := "2025-05-03")] alias right_add_sum_Ico := add_sum_Ico_eq_sum_Icc

@[to_additive]
lemma prod_Ico_mul_eq_prod_Icc (h : a ≤ b) : (∏ x ∈ Ico a b, f x) * f b = ∏ x ∈ Icc a b, f x := by
  rw [mul_comm, mul_prod_Ico_eq_prod_Icc h]

@[deprecated (since := "2025-05-03")] alias prod_Ico_mul_right := prod_Ico_mul_eq_prod_Icc
@[deprecated (since := "2025-05-03")] alias sum_Ico_add_right := sum_Ico_add_eq_sum_Icc

@[to_additive]
lemma mul_prod_Ioc_eq_prod_Icc (h : a ≤ b) : f a * ∏ x ∈ Ioc a b, f x = ∏ x ∈ Icc a b, f x := by
  rw [Icc_eq_cons_Ioc h, prod_cons]

@[deprecated (since := "2025-05-03")] alias left_mul_prod_Ioc := mul_prod_Ioc_eq_prod_Icc
@[deprecated (since := "2025-05-03")] alias left_add_sum_Ioc := add_sum_Ioc_eq_sum_Icc

@[to_additive]
lemma prod_Ioc_mul_eq_prod_Icc (h : a ≤ b) : (∏ x ∈ Ioc a b, f x) * f a = ∏ x ∈ Icc a b, f x := by
  rw [mul_comm, mul_prod_Ioc_eq_prod_Icc h]

@[deprecated (since := "2025-05-03")] alias prod_Ioc_mul_left := prod_Ioc_mul_eq_prod_Icc
@[deprecated (since := "2025-05-03")] alias sum_Ioc_add_left := sum_Ioc_add_eq_sum_Icc

@[to_additive]
lemma mul_prod_Ioo_eq_prod_Ico (h : a < b) : f a * ∏ x ∈ Ioo a b, f x = ∏ x ∈ Ico a b, f x := by
  rw [Ico_eq_cons_Ioo h, prod_cons]

@[deprecated (since := "2025-05-03")] alias left_mul_prod_Ioo := mul_prod_Ioo_eq_prod_Ico
@[deprecated (since := "2025-05-03")] alias left_add_sum_Ioo := add_sum_Ioo_eq_sum_Ico

@[to_additive]
lemma prod_Ioo_mul_eq_prod_Ico (h : a < b) : (∏ x ∈ Ioo a b, f x) * f a = ∏ x ∈ Ico a b, f x := by
  rw [mul_comm, mul_prod_Ioo_eq_prod_Ico h]

@[deprecated (since := "2025-05-03")] alias prod_Ioo_mul_left := prod_Ioo_mul_eq_prod_Ico
@[deprecated (since := "2025-05-03")] alias sum_Ioo_add_left := sum_Ioo_add_eq_sum_Ico

@[to_additive]
lemma mul_prod_Ioo_eq_prod_Ioc (h : a < b) : f b * ∏ x ∈ Ioo a b, f x = ∏ x ∈ Ioc a b, f x := by
  rw [Ioc_eq_cons_Ioo h, prod_cons]

@[deprecated (since := "2025-05-03")] alias right_mul_prod_Ioo := mul_prod_Ioo_eq_prod_Ioc
@[deprecated (since := "2025-05-03")] alias right_add_sum_Ioo := add_sum_Ioo_eq_sum_Ioc

@[to_additive]
lemma prod_Ioo_mul_eq_prod_Ioc (h : a < b) : (∏ x ∈ Ioo a b, f x) * f b = ∏ x ∈ Ioc a b, f x := by
  rw [mul_comm, mul_prod_Ioo_eq_prod_Ioc h]

@[deprecated (since := "2025-05-03")] alias prod_Ioo_mul_right := prod_Ioo_mul_eq_prod_Ioc
@[deprecated (since := "2025-05-03")] alias sum_Ioo_add_right := sum_Ioo_add_eq_sum_Ioc

variable [AddMonoidWithOne α] [SuccAddOrder α]

@[to_additive]
theorem prod_eq_prod_Ico_succ_bot {a b : ℕ} (hab : a < b) (f : ℕ → M) :
    ∏ k ∈ Ico a b, f k = f a * ∏ k ∈ Ico (a + 1) b, f k := by
  have ha : a ∉ Ico (a + 1) b := by simp
  rw [← prod_insert ha, Finset.insert_Ico_add_one_left_eq_Ico hab]

end LocallyFiniteOrder

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α]

@[to_additive]
lemma mul_prod_Ioi_eq_prod_Ici (a : α) : f a * ∏ x ∈ Ioi a, f x = ∏ x ∈ Ici a, f x := by
  rw [Ici_eq_cons_Ioi, prod_cons]

@[deprecated (since := "2025-05-03")] alias left_mul_prod_Ioi := mul_prod_Ioi_eq_prod_Ici
@[deprecated (since := "2025-05-03")] alias left_add_sum_Ioi := add_sum_Ioi_eq_sum_Ici

@[to_additive]
lemma prod_Ioi_mul_eq_prod_Ici (a : α) : (∏ x ∈ Ioi a, f x) * f a = ∏ x ∈ Ici a, f x := by
  rw [mul_comm, mul_prod_Ioi_eq_prod_Ici]

@[deprecated (since := "2025-05-03")] alias prod_Ioi_mul_left := prod_Ioi_mul_eq_prod_Ici
@[deprecated (since := "2025-05-03")] alias sum_Ioi_add_left := sum_Ioi_add_eq_sum_Ici

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α]

@[to_additive]
lemma mul_prod_Iio_eq_prod_Iic (a : α) : f a * ∏ x ∈ Iio a, f x = ∏ x ∈ Iic a, f x := by
  rw [Iic_eq_cons_Iio, prod_cons]

@[deprecated (since := "2025-05-03")] alias right_mul_prod_Iio := mul_prod_Iio_eq_prod_Iic
@[deprecated (since := "2025-05-03")] alias right_add_sum_Iio := add_sum_Iio_eq_sum_Iic

@[to_additive]
lemma prod_Iio_mul_eq_prod_Iic (a : α) : (∏ x ∈ Iio a, f x) * f a = ∏ x ∈ Iic a, f x := by
  rw [mul_comm, mul_prod_Iio_eq_prod_Iic]

@[deprecated (since := "2025-05-03")] alias prod_Iio_mul_right := prod_Iio_mul_eq_prod_Iic
@[deprecated (since := "2025-05-03")] alias sum_Iio_add_right := sum_Iio_add_eq_sum_Iic

end LocallyFiniteOrderBot

end PartialOrder

section LinearOrder
variable [LinearOrder α]

section LocallyFiniteOrder
variable [LocallyFiniteOrder α] [AddMonoidWithOne α] [SuccAddOrder α] [NoMaxOrder α]

-- we can't use `to_additive`, because it tries to translate `1` into `0`

lemma sum_Ico_add_eq_sum_Ico_add_one {M : Type*} [AddCommMonoid M] (hab : a ≤ b) (f : α → M) :
    ∑ x ∈ Ico a b, f x + f b = ∑ x ∈ Ico a (b + 1), f x := by
  rw [← Finset.insert_Ico_right_eq_Ico_add_one hab, sum_insert right_notMem_Ico, add_comm]

lemma prod_Ico_mul_eq_prod_Ico_add_one (hab : a ≤ b) (f : α → M) :
    (∏ x ∈ Ico a b, f x) * f b = ∏ x ∈ Ico a (b + 1), f x := by
  rw [← Finset.insert_Ico_right_eq_Ico_add_one hab, prod_insert right_notMem_Ico, mul_comm]

end LocallyFiniteOrder

variable [Fintype α] [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]

@[to_additive]
lemma prod_prod_Ioi_mul_eq_prod_prod_off_diag (f : α → α → M) :
    ∏ i, ∏ j ∈ Ioi i, f j i * f i j = ∏ i, ∏ j ∈ {i}ᶜ, f j i := by
  simp_rw [← Ioi_disjUnion_Iio, prod_disjUnion, prod_mul_distrib]
  congr 1
  rw [prod_sigma', prod_sigma']
  refine prod_nbij' (fun i ↦ ⟨i.2, i.1⟩) (fun i ↦ ⟨i.2, i.1⟩) ?_ ?_ ?_ ?_ ?_ <;> simp

end LinearOrder
end Finset
