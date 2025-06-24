/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.GaloisConnection.Basic

/-!
# Bounds on scalar multiplication of set

This file proves order properties of pointwise operations of sets.
-/

open scoped Pointwise

variable {α β : Type*}

section PosSMulMono
variable [SMul α β] [Preorder α] [Preorder β] [Zero α] [PosSMulMono α β] {a : α} {s : Set β}

lemma smul_lowerBounds_subset_lowerBounds_smul_of_nonneg (ha : 0 ≤ a) :
    a • lowerBounds s ⊆ lowerBounds (a • s) :=
  (monotone_smul_left_of_nonneg ha).image_lowerBounds_subset_lowerBounds_image

lemma smul_upperBounds_subset_upperBounds_smul_of_nonneg (ha : 0 ≤ a) :
    a • upperBounds s ⊆ upperBounds (a • s) :=
  (monotone_smul_left_of_nonneg ha).image_upperBounds_subset_upperBounds_image

lemma BddBelow.smul_of_nonneg (hs : BddBelow s) (ha : 0 ≤ a) : BddBelow (a • s) :=
  (monotone_smul_left_of_nonneg ha).map_bddBelow hs

lemma BddAbove.smul_of_nonneg (hs : BddAbove s) (ha : 0 ≤ a) : BddAbove (a • s) :=
  (monotone_smul_left_of_nonneg ha).map_bddAbove hs

end PosSMulMono


section
variable [Preorder α] [Preorder β] [GroupWithZero α] [Zero β] [MulActionWithZero α β]
  [PosSMulMono α β] [PosSMulReflectLE α β] {s : Set β} {a : α}

@[simp] lemma lowerBounds_smul_of_pos (ha : 0 < a) : lowerBounds (a • s) = a • lowerBounds s :=
  (OrderIso.smulRight ha).lowerBounds_image

@[simp] lemma upperBounds_smul_of_pos (ha : 0 < a) : upperBounds (a • s) = a • upperBounds s :=
  (OrderIso.smulRight ha).upperBounds_image

@[simp] lemma bddBelow_smul_iff_of_pos (ha : 0 < a) : BddBelow (a • s) ↔ BddBelow s :=
  (OrderIso.smulRight ha).bddBelow_image

@[simp] lemma bddAbove_smul_iff_of_pos (ha : 0 < a) : BddAbove (a • s) ↔ BddAbove s :=
  (OrderIso.smulRight ha).bddAbove_image

end

section OrderedRing

variable [Ring α] [PartialOrder α] [IsOrderedRing α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [Module α β] [PosSMulMono α β] {s : Set β} {a : α}

lemma smul_lowerBounds_subset_upperBounds_smul (ha : a ≤ 0) :
    a • lowerBounds s ⊆ upperBounds (a • s) :=
  (antitone_smul_left ha).image_lowerBounds_subset_upperBounds_image

lemma smul_upperBounds_subset_lowerBounds_smul (ha : a ≤ 0) :
    a • upperBounds s ⊆ lowerBounds (a • s) :=
  (antitone_smul_left ha).image_upperBounds_subset_lowerBounds_image

lemma BddBelow.smul_of_nonpos (ha : a ≤ 0) (hs : BddBelow s) : BddAbove (a • s) :=
  (antitone_smul_left ha).map_bddBelow hs

lemma BddAbove.smul_of_nonpos (ha : a ≤ 0) (hs : BddAbove s) : BddBelow (a • s) :=
  (antitone_smul_left ha).map_bddAbove hs

end OrderedRing

section LinearOrderedField
variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [Module α β] [PosSMulMono α β] {s : Set β}
  {a : α}

@[simp] lemma lowerBounds_smul_of_neg (ha : a < 0) : lowerBounds (a • s) = a • upperBounds s :=
  (OrderIso.smulRightDual β ha).upperBounds_image

@[simp] lemma upperBounds_smul_of_neg (ha : a < 0) : upperBounds (a • s) = a • lowerBounds s :=
  (OrderIso.smulRightDual β ha).lowerBounds_image

@[simp] lemma bddBelow_smul_iff_of_neg (ha : a < 0) : BddBelow (a • s) ↔ BddAbove s :=
  (OrderIso.smulRightDual β ha).bddAbove_image

@[simp] lemma bddAbove_smul_iff_of_neg (ha : a < 0) : BddAbove (a • s) ↔ BddBelow s :=
  (OrderIso.smulRightDual β ha).bddBelow_image

end LinearOrderedField
