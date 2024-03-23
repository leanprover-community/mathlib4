/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Order.Bounds.OrderIso

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
#align smul_lower_bounds_subset_lower_bounds_smul smul_lowerBounds_subset_lowerBounds_smul_of_nonneg

lemma smul_upperBounds_subset_upperBounds_smul_of_nonneg (ha : 0 ≤ a) :
    a • upperBounds s ⊆ upperBounds (a • s) :=
  (monotone_smul_left_of_nonneg ha).image_upperBounds_subset_upperBounds_image
#align smul_upper_bounds_subset_upper_bounds_smul smul_upperBounds_subset_upperBounds_smul_of_nonneg

lemma BddBelow.smul_of_nonneg (hs : BddBelow s) (ha : 0 ≤ a) : BddBelow (a • s) :=
  (monotone_smul_left_of_nonneg ha).map_bddBelow hs
#align bdd_below.smul_of_nonneg BddBelow.smul_of_nonneg

lemma BddAbove.smul_of_nonneg (hs : BddAbove s) (ha : 0 ≤ a) : BddAbove (a • s) :=
  (monotone_smul_left_of_nonneg ha).map_bddAbove hs
#align bdd_above.smul_of_nonneg BddAbove.smul_of_nonneg

end PosSMulMono


section
variable [Preorder α] [Preorder β] [GroupWithZero α] [Zero β] [MulActionWithZero α β]
  [PosSMulMono α β] [PosSMulReflectLE α β] {s : Set β} {a : α}

@[simp] lemma lowerBounds_smul_of_pos (ha : 0 < a) : lowerBounds (a • s) = a • lowerBounds s :=
  (OrderIso.smulRight ha).lowerBounds_image
#align lower_bounds_smul_of_pos lowerBounds_smul_of_pos

@[simp] lemma upperBounds_smul_of_pos (ha : 0 < a) : upperBounds (a • s) = a • upperBounds s :=
  (OrderIso.smulRight ha).upperBounds_image
#align upper_bounds_smul_of_pos upperBounds_smul_of_pos

@[simp] lemma bddBelow_smul_iff_of_pos (ha : 0 < a) : BddBelow (a • s) ↔ BddBelow s :=
  (OrderIso.smulRight ha).bddBelow_image
#align bdd_below_smul_iff_of_pos bddBelow_smul_iff_of_pos

@[simp] lemma bddAbove_smul_iff_of_pos (ha : 0 < a) : BddAbove (a • s) ↔ BddAbove s :=
  (OrderIso.smulRight ha).bddAbove_image
#align bdd_above_smul_iff_of_pos bddAbove_smul_iff_of_pos

end

section OrderedRing

variable [OrderedRing α] [OrderedAddCommGroup β] [Module α β] [PosSMulMono α β] {s : Set β} {a : α}

lemma smul_lowerBounds_subset_upperBounds_smul (ha : a ≤ 0) :
    a • lowerBounds s ⊆ upperBounds (a • s) :=
  (antitone_smul_left ha).image_lowerBounds_subset_upperBounds_image
#align smul_lower_bounds_subset_upper_bounds_smul smul_lowerBounds_subset_upperBounds_smul

lemma smul_upperBounds_subset_lowerBounds_smul (ha : a ≤ 0) :
    a • upperBounds s ⊆ lowerBounds (a • s) :=
  (antitone_smul_left ha).image_upperBounds_subset_lowerBounds_image
#align smul_upper_bounds_subset_lower_bounds_smul smul_upperBounds_subset_lowerBounds_smul

lemma BddBelow.smul_of_nonpos (ha : a ≤ 0) (hs : BddBelow s) : BddAbove (a • s) :=
  (antitone_smul_left ha).map_bddBelow hs
#align bdd_below.smul_of_nonpos BddBelow.smul_of_nonpos

lemma BddAbove.smul_of_nonpos (ha : a ≤ 0) (hs : BddAbove s) : BddBelow (a • s) :=
  (antitone_smul_left ha).map_bddAbove hs
#align bdd_above.smul_of_nonpos BddAbove.smul_of_nonpos

end OrderedRing

section LinearOrderedField
variable [LinearOrderedField α] [OrderedAddCommGroup β] [Module α β] [PosSMulMono α β] {s : Set β}
  {a : α}

@[simp] lemma lowerBounds_smul_of_neg (ha : a < 0) : lowerBounds (a • s) = a • upperBounds s :=
  (OrderIso.smulRightDual β ha).upperBounds_image
#align lower_bounds_smul_of_neg lowerBounds_smul_of_neg

@[simp] lemma upperBounds_smul_of_neg (ha : a < 0) : upperBounds (a • s) = a • lowerBounds s :=
  (OrderIso.smulRightDual β ha).lowerBounds_image
#align upper_bounds_smul_of_neg upperBounds_smul_of_neg

@[simp] lemma bddBelow_smul_iff_of_neg (ha : a < 0) : BddBelow (a • s) ↔ BddAbove s :=
  (OrderIso.smulRightDual β ha).bddAbove_image
#align bdd_below_smul_iff_of_neg bddBelow_smul_iff_of_neg

@[simp] lemma bddAbove_smul_iff_of_neg (ha : a < 0) : BddAbove (a • s) ↔ BddBelow s :=
  (OrderIso.smulRightDual β ha).bddBelow_image
#align bdd_above_smul_iff_of_neg bddAbove_smul_iff_of_neg

end LinearOrderedField
