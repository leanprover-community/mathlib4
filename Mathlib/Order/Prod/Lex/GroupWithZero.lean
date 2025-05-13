/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Data.Prod.Lex

/-!
# Order homomorphisms for products of linearly ordered groups with zero

This file defines order homomorphisms for products of linearly ordered groups with zero,
which is identified with the `WithZero` of the lexicographic product of the units of the groups.

The product of linearly ordered groups with zero `WithZero (αˣ ×ₗ βˣ)` is a
linearly ordered group with zero itself with natural inclusions but only one projection.
One has to work with the lexicographic product of the units `αˣ ×ₗ βˣ` since otherwise,
the plain product `αˣ × βˣ` would not be linearly ordered.

TODO: Create the "LinOrdCommGrpWithZero" category.

-/

namespace LinearOrderedCommGroupWithZero

variable (α β : Type*) [LinearOrderedCommGroupWithZero α] [LinearOrderedCommGroupWithZero β]

/-- Given linearly ordered groups with zero M, N, the natural inclusion ordered homomorphism from
M to `WithZero (Mˣ ×ₗ Nˣ)`, which is the linearly ordered group with zero that can be identified
as their product. -/
@[simps!]
def inl : α →*₀o WithZero (αˣ ×ₗ βˣ) where
  toFun a := if ha : a = 0 then 0 else WithZero.coe (toLex ⟨Units.mk0 _ ha, 1⟩)
  map_one' := by simp
  map_mul' x y := by
    simp only [mul_eq_zero, Units.mk0_mul, mul_dite, mul_zero, dite_mul, zero_mul]
    split_ifs with hxy
    · simp
    · simp_all
    · simp_all
    · simp [*] at hxy
    · simp [*] at hxy
    · simp [← WithZero.coe_mul, ← toLex_mul]
  map_zero' := by simp
  monotone' x y hxy := by
    dsimp only
    split_ifs
    · exact WithZero.zero_le _
    · exact WithZero.zero_le _
    · simp [*] at hxy
    · simp [Prod.Lex.toLex_le_toLex, ← Units.val_lt_val, lt_or_eq_of_le hxy]

/-- Given linearly ordered groups with zero M, N, the natural inclusion ordered homomorphism from
N to `WithZero (Mˣ ×ₗ Nˣ)`, which is the linearly ordered group with zero that can be identified
as their product. -/
@[simps!]
def inr : β →*₀o WithZero (αˣ ×ₗ βˣ) where
  toFun a := if ha : a = 0 then 0 else WithZero.coe (toLex ⟨1, Units.mk0 _ ha⟩)
  map_one' := by simp
  map_mul' x y := by
    simp only [mul_eq_zero, Units.mk0_mul, mul_dite, mul_zero, dite_mul, zero_mul]
    split_ifs with hxy
    · simp
    · simp_all
    · simp_all
    · simp [*] at hxy
    · simp [*] at hxy
    · simp [← WithZero.coe_mul, ← toLex_mul]
  map_zero' := by simp
  monotone' x y hxy := by
    dsimp only
    split_ifs
    · exact WithZero.zero_le _
    · exact WithZero.zero_le _
    · simp [*] at hxy
    · simp [Prod.Lex.toLex_le_toLex, ← Units.val_le_val, hxy]

/-- Given linearly ordered groups with zero M, N, the natural projection ordered homomorphism from
`WithZero (Mˣ ×ₗ Nˣ)` to M, which is the linearly ordered group with zero that can be identified
as their product. -/
@[simps!]
def fst : WithZero (αˣ ×ₗ βˣ) →*₀o α where
  toFun a := WithZero.recZeroCoe 0 (fun p ↦ (ofLex p).fst) a
  map_one' := by simp [← WithZero.coe_one]
  map_mul' x y := by cases x <;> cases y <;> simp [← WithZero.coe_mul]
  map_zero' := by simp
  monotone' x y hxy := by
    cases x <;> cases y
    · simp
    · simp
    · simp [(WithZero.zero_lt_coe _).not_le] at hxy
    · simp only [WithZero.coe_le_coe, Prod.Lex.le_iff] at hxy
      simp only [WithZero.recZeroCoe_coe, le_iff_lt_or_eq, Units.val_lt_val]
      exact hxy.imp_right (by simp +contextual)

@[simp]
theorem fst_comp_inl : (fst _ _).comp (inl α β) = .id α := by
  ext x
  simp only [OrderMonoidWithZeroHom.comp_apply, inl_apply, fst_apply]
  split_ifs <;>
  simp_all

theorem inlₗ_mul_inrₗ_eq_coe_toLex {m : α} {n : β} (hm : m ≠ 0) (hn : n ≠ 0) :
    (inl α β m * inr α β n) = toLex (Units.mk0 _ hm, Units.mk0 _ hn) := by
  simp [← WithZero.coe_mul, ← toLex_mul, hm, hn]

end LinearOrderedCommGroupWithZero
