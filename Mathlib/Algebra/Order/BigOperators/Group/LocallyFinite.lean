/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.Disjointed
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Big operators indexed by intervals

This file proves lemmas about `∏ x ∈ Ixx a b, f x` and `∑ x ∈ Ixx a b, f x`.
-/

public section

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

@[to_additive]
lemma prod_Ico_mul_eq_prod_Icc (h : a ≤ b) : (∏ x ∈ Ico a b, f x) * f b = ∏ x ∈ Icc a b, f x := by
  rw [mul_comm, mul_prod_Ico_eq_prod_Icc h]

@[to_additive]
lemma mul_prod_Ioc_eq_prod_Icc (h : a ≤ b) : f a * ∏ x ∈ Ioc a b, f x = ∏ x ∈ Icc a b, f x := by
  rw [Icc_eq_cons_Ioc h, prod_cons]

@[to_additive]
lemma prod_Ioc_mul_eq_prod_Icc (h : a ≤ b) : (∏ x ∈ Ioc a b, f x) * f a = ∏ x ∈ Icc a b, f x := by
  rw [mul_comm, mul_prod_Ioc_eq_prod_Icc h]

@[to_additive]
lemma mul_prod_Ioo_eq_prod_Ico (h : a < b) : f a * ∏ x ∈ Ioo a b, f x = ∏ x ∈ Ico a b, f x := by
  rw [Ico_eq_cons_Ioo h, prod_cons]

@[to_additive]
lemma prod_Ioo_mul_eq_prod_Ico (h : a < b) : (∏ x ∈ Ioo a b, f x) * f a = ∏ x ∈ Ico a b, f x := by
  rw [mul_comm, mul_prod_Ioo_eq_prod_Ico h]

@[to_additive]
lemma mul_prod_Ioo_eq_prod_Ioc (h : a < b) : f b * ∏ x ∈ Ioo a b, f x = ∏ x ∈ Ioc a b, f x := by
  rw [Ioc_eq_cons_Ioo h, prod_cons]

@[to_additive]
lemma prod_Ioo_mul_eq_prod_Ioc (h : a < b) : (∏ x ∈ Ioo a b, f x) * f b = ∏ x ∈ Ioc a b, f x := by
  rw [mul_comm, mul_prod_Ioo_eq_prod_Ioc h]

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

@[to_additive]
lemma prod_Ioi_mul_eq_prod_Ici (a : α) : (∏ x ∈ Ioi a, f x) * f a = ∏ x ∈ Ici a, f x := by
  rw [mul_comm, mul_prod_Ioi_eq_prod_Ici]

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α]

@[to_additive]
lemma mul_prod_Iio_eq_prod_Iic (a : α) : f a * ∏ x ∈ Iio a, f x = ∏ x ∈ Iic a, f x := by
  rw [Iic_eq_cons_Iio, prod_cons]

@[to_additive]
lemma prod_Iio_mul_eq_prod_Iic (a : α) : (∏ x ∈ Iio a, f x) * f a = ∏ x ∈ Iic a, f x := by
  rw [mul_comm, mul_prod_Iio_eq_prod_Iic]

end LocallyFiniteOrderBot

end PartialOrder

section LinearOrder
variable [LinearOrder α]

section LocallyFiniteOrder
variable [LocallyFiniteOrder α] [AddMonoidWithOne α] [SuccAddOrder α] [NoMaxOrder α]

@[to_additive (dont_translate := α) sum_Ico_add_eq_sum_Ico_add_one]
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

/-- Given a sequence of finite sets `s₀ ⊆ s₁ ⊆ s₂ ⋯`, the product of `gᵢ` over `i ∈ sₙ` is equal
to `∏_{i ∈ s₀} gᵢ` * `∏_{j < n, i ∈ sⱼ₊₁ \ sⱼ} gᵢ`. -/
@[to_additive /-- Given a sequence of finite sets `s₀ ⊆ s₁ ⊆ s₂ ⋯`, the sum of `gᵢ` over `i ∈ sₙ` is
equal to `∑_{i ∈ s₀} gᵢ` + `∑_{j < n, i ∈ sⱼ₊₁ \ sⱼ} gᵢ`.-/]
lemma prod_eq_prod_range_sdiff
    {α β : Type*} [DecidableEq α] [CommMonoid β] (s : ℕ → Finset α) (hs : Monotone s)
    (g : α → β) (n : ℕ) :
    ∏ i ∈ s n, g i = (∏ i ∈ s 0, g i) * ∏ i ∈ range n, ∏ j ∈ s (i + 1) \ s i, g j := by
  conv_lhs => rw [← hs.partialSups_eq, ← disjiUnion_Iic_disjointed, Iic_eq_Icc,
    prod_disjiUnion, Nat.bot_eq_zero, ← Nat.range_succ_eq_Icc_zero, prod_range_succ', mul_comm]
  congrm (∏ x ∈ ?_, g x) * ∏ k ∈ range n, ∏ x ∈ s (k + 1) \ ?_, g x
  · simp
  · change (Iic k).sup (s ∘ id) = s k
    rw [← comp_sup_eq_sup_comp_of_nonempty hs nonempty_Iic, sup_Iic]

end Finset
