/-
Copyright (c) 2026 Snir Broshi, Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi, Justus Springer
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# More lemmas on self-inverse elements

This file collects results about `IsSelfInv`/`IsSelfNeg` that need more algebraic structures.
-/

public section

@[simp]
protected theorem IsSelfInv.zero {α : Type*} [GroupWithZero α] : IsSelfInv (0 : α) :=
  inv_zero

@[simp]
protected theorem IsSelfNeg.one {α : Type*} [AddGroupWithOne α] [CharP α 2] :
    IsSelfNeg (1 : α) := by
  rw [isSelfNeg_iff, neg_eq_iff_add_eq_zero, one_add_one_eq_two, CharTwo.two_eq_zero]

protected theorem IsSelfInv.neg {α : Type*} [DivisionMonoid α] [HasDistribNeg α] {a : α}
    (h : IsSelfInv a) : IsSelfInv (-a) := by
  rw [isSelfInv_iff, inv_neg, h.inv_eq]

protected theorem IsSelfNeg.inv {α : Type*} [DivisionMonoid α] [HasDistribNeg α] {a : α}
    (h : IsSelfNeg a) : IsSelfNeg a⁻¹ := by
  rw [isSelfNeg_iff, neg_inv, h.neg_eq]

@[to_additive]
theorem isSelfInv_iff_isOfFinOrder_and_orderOf_le_two {G : Type*} [Group G] {a : G} :
    IsSelfInv a ↔ IsOfFinOrder a ∧ orderOf a ≤ 2 := by
  rw [isSelfInv_iff_sq_eq_one]
  refine ⟨fun h ↦ ⟨isOfFinOrder_iff_pow_eq_one.mpr ⟨2, zero_lt_two, h⟩,
    orderOf_le_of_pow_eq_one zero_lt_two h⟩, fun ⟨hfin, _⟩ ↦ ?_⟩
  have : orderOf a = 1 ∨ orderOf a = 2 := by grind [hfin.orderOf_pos]
  rcases this with h₁ | h₂
  · simp [orderOf_eq_one_iff.mp h₁]
  · rw [← h₂, pow_orderOf_eq_one a]

@[to_additive]
theorem IsOfFinOrder.isSelfInv_iff {G : Type*} [Group G] {a : G} (h : IsOfFinOrder a) :
    IsSelfInv a ↔ orderOf a ≤ 2 := by
  rw [isSelfInv_iff_isOfFinOrder_and_orderOf_le_two, and_iff_right h]

@[to_additive]
theorem isSelfInv_iff_eq_one {G : Type*} [Group G] [IsMulTorsionFree G] {a : G} :
    IsSelfInv a ↔ a = 1 :=
  inv_eq_self

theorem isSelfNeg_of_isSMulRegular_two {R : Type*} [NonAssocRing R] (h : IsSMulRegular R 2)
    {a : R} : IsSelfNeg a ↔ a = 0 :=
  isSelfNeg_iff_two_nsmul_eq_zero.trans ⟨(h <| by simpa using ·), (by simp [·])⟩

theorem isSelfInv_iff_eq_neg_one_or_eq_zero_or_eq_one {K : Type*} [DivisionRing K] {a : K} :
    IsSelfInv a ↔ a = -1 ∨ a = 0 ∨ a = 1 :=
  inv_eq_self₀
