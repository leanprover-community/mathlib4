/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot
-/
import Mathlib.Data.Set.Intervals.UnorderedInterval
import Mathlib.Data.Set.Intervals.Monoid
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.MinMax

#align_import data.set.pointwise.interval from "leanprover-community/mathlib"@"2196ab363eb097c008d4497125e0dde23fb36db2"

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

section OrderedAddCommGroup

variable [OrderedAddCommGroup α] (a b c : α)

/-!
### Preimages under `x ↦ a + x`
-/


@[simp]
theorem preimage_const_add_Ici : (fun x => a + x) ⁻¹' Ici b = Ici (b - a) :=
  ext fun _x => sub_le_iff_le_add'.symm
#align set.preimage_const_add_Ici Set.preimage_const_add_Ici

@[simp]
theorem preimage_const_add_Ioi : (fun x => a + x) ⁻¹' Ioi b = Ioi (b - a) :=
  ext fun _x => sub_lt_iff_lt_add'.symm
#align set.preimage_const_add_Ioi Set.preimage_const_add_Ioi

@[simp]
theorem preimage_const_add_Iic : (fun x => a + x) ⁻¹' Iic b = Iic (b - a) :=
  ext fun _x => le_sub_iff_add_le'.symm
#align set.preimage_const_add_Iic Set.preimage_const_add_Iic

@[simp]
theorem preimage_const_add_Iio : (fun x => a + x) ⁻¹' Iio b = Iio (b - a) :=
  ext fun _x => lt_sub_iff_add_lt'.symm
#align set.preimage_const_add_Iio Set.preimage_const_add_Iio

@[simp]
theorem preimage_const_add_Icc : (fun x => a + x) ⁻¹' Icc b c = Icc (b - a) (c - a) := by
  simp [← Ici_inter_Iic]
  -- 🎉 no goals
#align set.preimage_const_add_Icc Set.preimage_const_add_Icc

@[simp]
theorem preimage_const_add_Ico : (fun x => a + x) ⁻¹' Ico b c = Ico (b - a) (c - a) := by
  simp [← Ici_inter_Iio]
  -- 🎉 no goals
#align set.preimage_const_add_Ico Set.preimage_const_add_Ico

@[simp]
theorem preimage_const_add_Ioc : (fun x => a + x) ⁻¹' Ioc b c = Ioc (b - a) (c - a) := by
  simp [← Ioi_inter_Iic]
  -- 🎉 no goals
#align set.preimage_const_add_Ioc Set.preimage_const_add_Ioc

@[simp]
theorem preimage_const_add_Ioo : (fun x => a + x) ⁻¹' Ioo b c = Ioo (b - a) (c - a) := by
  simp [← Ioi_inter_Iio]
  -- 🎉 no goals
#align set.preimage_const_add_Ioo Set.preimage_const_add_Ioo

/-!
### Preimages under `x ↦ x + a`
-/


@[simp]
theorem preimage_add_const_Ici : (fun x => x + a) ⁻¹' Ici b = Ici (b - a) :=
  ext fun _x => sub_le_iff_le_add.symm
#align set.preimage_add_const_Ici Set.preimage_add_const_Ici

@[simp]
theorem preimage_add_const_Ioi : (fun x => x + a) ⁻¹' Ioi b = Ioi (b - a) :=
  ext fun _x => sub_lt_iff_lt_add.symm
#align set.preimage_add_const_Ioi Set.preimage_add_const_Ioi

@[simp]
theorem preimage_add_const_Iic : (fun x => x + a) ⁻¹' Iic b = Iic (b - a) :=
  ext fun _x => le_sub_iff_add_le.symm
#align set.preimage_add_const_Iic Set.preimage_add_const_Iic

@[simp]
theorem preimage_add_const_Iio : (fun x => x + a) ⁻¹' Iio b = Iio (b - a) :=
  ext fun _x => lt_sub_iff_add_lt.symm
#align set.preimage_add_const_Iio Set.preimage_add_const_Iio

@[simp]
theorem preimage_add_const_Icc : (fun x => x + a) ⁻¹' Icc b c = Icc (b - a) (c - a) := by
  simp [← Ici_inter_Iic]
  -- 🎉 no goals
#align set.preimage_add_const_Icc Set.preimage_add_const_Icc

@[simp]
theorem preimage_add_const_Ico : (fun x => x + a) ⁻¹' Ico b c = Ico (b - a) (c - a) := by
  simp [← Ici_inter_Iio]
  -- 🎉 no goals
#align set.preimage_add_const_Ico Set.preimage_add_const_Ico

@[simp]
theorem preimage_add_const_Ioc : (fun x => x + a) ⁻¹' Ioc b c = Ioc (b - a) (c - a) := by
  simp [← Ioi_inter_Iic]
  -- 🎉 no goals
#align set.preimage_add_const_Ioc Set.preimage_add_const_Ioc

@[simp]
theorem preimage_add_const_Ioo : (fun x => x + a) ⁻¹' Ioo b c = Ioo (b - a) (c - a) := by
  simp [← Ioi_inter_Iio]
  -- 🎉 no goals
#align set.preimage_add_const_Ioo Set.preimage_add_const_Ioo

/-!
### Preimages under `x ↦ -x`
-/


@[simp]
theorem preimage_neg_Ici : -Ici a = Iic (-a) :=
  ext fun _x => le_neg
#align set.preimage_neg_Ici Set.preimage_neg_Ici

@[simp]
theorem preimage_neg_Iic : -Iic a = Ici (-a) :=
  ext fun _x => neg_le
#align set.preimage_neg_Iic Set.preimage_neg_Iic

@[simp]
theorem preimage_neg_Ioi : -Ioi a = Iio (-a) :=
  ext fun _x => lt_neg
#align set.preimage_neg_Ioi Set.preimage_neg_Ioi

@[simp]
theorem preimage_neg_Iio : -Iio a = Ioi (-a) :=
  ext fun _x => neg_lt
#align set.preimage_neg_Iio Set.preimage_neg_Iio

@[simp]
theorem preimage_neg_Icc : -Icc a b = Icc (-b) (-a) := by simp [← Ici_inter_Iic, inter_comm]
                                                          -- 🎉 no goals
#align set.preimage_neg_Icc Set.preimage_neg_Icc

@[simp]
theorem preimage_neg_Ico : -Ico a b = Ioc (-b) (-a) := by
  simp [← Ici_inter_Iio, ← Ioi_inter_Iic, inter_comm]
  -- 🎉 no goals
#align set.preimage_neg_Ico Set.preimage_neg_Ico

@[simp]
theorem preimage_neg_Ioc : -Ioc a b = Ico (-b) (-a) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]
  -- 🎉 no goals
#align set.preimage_neg_Ioc Set.preimage_neg_Ioc

@[simp]
theorem preimage_neg_Ioo : -Ioo a b = Ioo (-b) (-a) := by simp [← Ioi_inter_Iio, inter_comm]
                                                          -- 🎉 no goals
#align set.preimage_neg_Ioo Set.preimage_neg_Ioo

/-!
### Preimages under `x ↦ x - a`
-/


@[simp]
theorem preimage_sub_const_Ici : (fun x => x - a) ⁻¹' Ici b = Ici (b + a) := by
  simp [sub_eq_add_neg]
  -- 🎉 no goals
#align set.preimage_sub_const_Ici Set.preimage_sub_const_Ici

@[simp]
theorem preimage_sub_const_Ioi : (fun x => x - a) ⁻¹' Ioi b = Ioi (b + a) := by
  simp [sub_eq_add_neg]
  -- 🎉 no goals
#align set.preimage_sub_const_Ioi Set.preimage_sub_const_Ioi

@[simp]
theorem preimage_sub_const_Iic : (fun x => x - a) ⁻¹' Iic b = Iic (b + a) := by
  simp [sub_eq_add_neg]
  -- 🎉 no goals
#align set.preimage_sub_const_Iic Set.preimage_sub_const_Iic

@[simp]
theorem preimage_sub_const_Iio : (fun x => x - a) ⁻¹' Iio b = Iio (b + a) := by
  simp [sub_eq_add_neg]
  -- 🎉 no goals
#align set.preimage_sub_const_Iio Set.preimage_sub_const_Iio

@[simp]
theorem preimage_sub_const_Icc : (fun x => x - a) ⁻¹' Icc b c = Icc (b + a) (c + a) := by
  simp [sub_eq_add_neg]
  -- 🎉 no goals
#align set.preimage_sub_const_Icc Set.preimage_sub_const_Icc

@[simp]
theorem preimage_sub_const_Ico : (fun x => x - a) ⁻¹' Ico b c = Ico (b + a) (c + a) := by
  simp [sub_eq_add_neg]
  -- 🎉 no goals
#align set.preimage_sub_const_Ico Set.preimage_sub_const_Ico

@[simp]
theorem preimage_sub_const_Ioc : (fun x => x - a) ⁻¹' Ioc b c = Ioc (b + a) (c + a) := by
  simp [sub_eq_add_neg]
  -- 🎉 no goals
#align set.preimage_sub_const_Ioc Set.preimage_sub_const_Ioc

@[simp]
theorem preimage_sub_const_Ioo : (fun x => x - a) ⁻¹' Ioo b c = Ioo (b + a) (c + a) := by
  simp [sub_eq_add_neg]
  -- 🎉 no goals
#align set.preimage_sub_const_Ioo Set.preimage_sub_const_Ioo

/-!
### Preimages under `x ↦ a - x`
-/


@[simp]
theorem preimage_const_sub_Ici : (fun x => a - x) ⁻¹' Ici b = Iic (a - b) :=
  ext fun _x => le_sub_comm
#align set.preimage_const_sub_Ici Set.preimage_const_sub_Ici

@[simp]
theorem preimage_const_sub_Iic : (fun x => a - x) ⁻¹' Iic b = Ici (a - b) :=
  ext fun _x => sub_le_comm
#align set.preimage_const_sub_Iic Set.preimage_const_sub_Iic

@[simp]
theorem preimage_const_sub_Ioi : (fun x => a - x) ⁻¹' Ioi b = Iio (a - b) :=
  ext fun _x => lt_sub_comm
#align set.preimage_const_sub_Ioi Set.preimage_const_sub_Ioi

@[simp]
theorem preimage_const_sub_Iio : (fun x => a - x) ⁻¹' Iio b = Ioi (a - b) :=
  ext fun _x => sub_lt_comm
#align set.preimage_const_sub_Iio Set.preimage_const_sub_Iio

@[simp]
theorem preimage_const_sub_Icc : (fun x => a - x) ⁻¹' Icc b c = Icc (a - c) (a - b) := by
  simp [← Ici_inter_Iic, inter_comm]
  -- 🎉 no goals
#align set.preimage_const_sub_Icc Set.preimage_const_sub_Icc

@[simp]
theorem preimage_const_sub_Ico : (fun x => a - x) ⁻¹' Ico b c = Ioc (a - c) (a - b) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]
  -- 🎉 no goals
#align set.preimage_const_sub_Ico Set.preimage_const_sub_Ico

@[simp]
theorem preimage_const_sub_Ioc : (fun x => a - x) ⁻¹' Ioc b c = Ico (a - c) (a - b) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]
  -- 🎉 no goals
#align set.preimage_const_sub_Ioc Set.preimage_const_sub_Ioc

@[simp]
theorem preimage_const_sub_Ioo : (fun x => a - x) ⁻¹' Ioo b c = Ioo (a - c) (a - b) := by
  simp [← Ioi_inter_Iio, inter_comm]
  -- 🎉 no goals
#align set.preimage_const_sub_Ioo Set.preimage_const_sub_Ioo

/-!
### Images under `x ↦ a + x`
-/


-- @[simp] -- Porting note: simp can prove this modulo `add_comm`
theorem image_const_add_Iic : (fun x => a + x) '' Iic b = Iic (a + b) := by simp [add_comm]
                                                                            -- 🎉 no goals
#align set.image_const_add_Iic Set.image_const_add_Iic

-- @[simp] -- Porting note: simp can prove this modulo `add_comm`
theorem image_const_add_Iio : (fun x => a + x) '' Iio b = Iio (a + b) := by simp [add_comm]
                                                                            -- 🎉 no goals
#align set.image_const_add_Iio Set.image_const_add_Iio

/-!
### Images under `x ↦ x + a`
-/


-- @[simp] -- Porting note: simp can prove this
theorem image_add_const_Iic : (fun x => x + a) '' Iic b = Iic (b + a) := by simp
                                                                            -- 🎉 no goals
#align set.image_add_const_Iic Set.image_add_const_Iic

-- @[simp] -- Porting note: simp can prove this
theorem image_add_const_Iio : (fun x => x + a) '' Iio b = Iio (b + a) := by simp
                                                                            -- 🎉 no goals
#align set.image_add_const_Iio Set.image_add_const_Iio

/-!
### Images under `x ↦ -x`
-/


theorem image_neg_Ici : Neg.neg '' Ici a = Iic (-a) := by simp
                                                          -- 🎉 no goals
#align set.image_neg_Ici Set.image_neg_Ici

theorem image_neg_Iic : Neg.neg '' Iic a = Ici (-a) := by simp
                                                          -- 🎉 no goals
#align set.image_neg_Iic Set.image_neg_Iic

theorem image_neg_Ioi : Neg.neg '' Ioi a = Iio (-a) := by simp
                                                          -- 🎉 no goals
#align set.image_neg_Ioi Set.image_neg_Ioi

theorem image_neg_Iio : Neg.neg '' Iio a = Ioi (-a) := by simp
                                                          -- 🎉 no goals
#align set.image_neg_Iio Set.image_neg_Iio

theorem image_neg_Icc : Neg.neg '' Icc a b = Icc (-b) (-a) := by simp
                                                                 -- 🎉 no goals
#align set.image_neg_Icc Set.image_neg_Icc

theorem image_neg_Ico : Neg.neg '' Ico a b = Ioc (-b) (-a) := by simp
                                                                 -- 🎉 no goals
#align set.image_neg_Ico Set.image_neg_Ico

theorem image_neg_Ioc : Neg.neg '' Ioc a b = Ico (-b) (-a) := by simp
                                                                 -- 🎉 no goals
#align set.image_neg_Ioc Set.image_neg_Ioc

theorem image_neg_Ioo : Neg.neg '' Ioo a b = Ioo (-b) (-a) := by simp
                                                                 -- 🎉 no goals
#align set.image_neg_Ioo Set.image_neg_Ioo

/-!
### Images under `x ↦ a - x`
-/


@[simp]
theorem image_const_sub_Ici : (fun x => a - x) '' Ici b = Iic (a - b) := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp] at this
  -- ⊢ (fun x => a - x) '' Ici b = Iic (a - b)
                                                   -- ⊢ (fun x => a - x) '' Ici b = Iic (a - b)
  simp [sub_eq_add_neg, this, add_comm]
  -- 🎉 no goals
#align set.image_const_sub_Ici Set.image_const_sub_Ici

@[simp]
theorem image_const_sub_Iic : (fun x => a - x) '' Iic b = Ici (a - b) := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp] at this
  -- ⊢ (fun x => a - x) '' Iic b = Ici (a - b)
                                                   -- ⊢ (fun x => a - x) '' Iic b = Ici (a - b)
  simp [sub_eq_add_neg, this, add_comm]
  -- 🎉 no goals
#align set.image_const_sub_Iic Set.image_const_sub_Iic

@[simp]
theorem image_const_sub_Ioi : (fun x => a - x) '' Ioi b = Iio (a - b) := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp] at this
  -- ⊢ (fun x => a - x) '' Ioi b = Iio (a - b)
                                                   -- ⊢ (fun x => a - x) '' Ioi b = Iio (a - b)
  simp [sub_eq_add_neg, this, add_comm]
  -- 🎉 no goals
#align set.image_const_sub_Ioi Set.image_const_sub_Ioi

@[simp]
theorem image_const_sub_Iio : (fun x => a - x) '' Iio b = Ioi (a - b) := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp] at this
  -- ⊢ (fun x => a - x) '' Iio b = Ioi (a - b)
                                                   -- ⊢ (fun x => a - x) '' Iio b = Ioi (a - b)
  simp [sub_eq_add_neg, this, add_comm]
  -- 🎉 no goals
#align set.image_const_sub_Iio Set.image_const_sub_Iio

@[simp]
theorem image_const_sub_Icc : (fun x => a - x) '' Icc b c = Icc (a - c) (a - b) := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp] at this
  -- ⊢ (fun x => a - x) '' Icc b c = Icc (a - c) (a - b)
                                                   -- ⊢ (fun x => a - x) '' Icc b c = Icc (a - c) (a - b)
  simp [sub_eq_add_neg, this, add_comm]
  -- 🎉 no goals
#align set.image_const_sub_Icc Set.image_const_sub_Icc

@[simp]
theorem image_const_sub_Ico : (fun x => a - x) '' Ico b c = Ioc (a - c) (a - b) := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp] at this
  -- ⊢ (fun x => a - x) '' Ico b c = Ioc (a - c) (a - b)
                                                   -- ⊢ (fun x => a - x) '' Ico b c = Ioc (a - c) (a - b)
  simp [sub_eq_add_neg, this, add_comm]
  -- 🎉 no goals
#align set.image_const_sub_Ico Set.image_const_sub_Ico

@[simp]
theorem image_const_sub_Ioc : (fun x => a - x) '' Ioc b c = Ico (a - c) (a - b) := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp] at this
  -- ⊢ (fun x => a - x) '' Ioc b c = Ico (a - c) (a - b)
                                                   -- ⊢ (fun x => a - x) '' Ioc b c = Ico (a - c) (a - b)
  simp [sub_eq_add_neg, this, add_comm]
  -- 🎉 no goals
#align set.image_const_sub_Ioc Set.image_const_sub_Ioc

@[simp]
theorem image_const_sub_Ioo : (fun x => a - x) '' Ioo b c = Ioo (a - c) (a - b) := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp] at this
  -- ⊢ (fun x => a - x) '' Ioo b c = Ioo (a - c) (a - b)
                                                   -- ⊢ (fun x => a - x) '' Ioo b c = Ioo (a - c) (a - b)
  simp [sub_eq_add_neg, this, add_comm]
  -- 🎉 no goals
#align set.image_const_sub_Ioo Set.image_const_sub_Ioo

/-!
### Images under `x ↦ x - a`
-/


@[simp]
theorem image_sub_const_Ici : (fun x => x - a) '' Ici b = Ici (b - a) := by simp [sub_eq_neg_add]
                                                                            -- 🎉 no goals
#align set.image_sub_const_Ici Set.image_sub_const_Ici

@[simp]
theorem image_sub_const_Iic : (fun x => x - a) '' Iic b = Iic (b - a) := by simp [sub_eq_neg_add]
                                                                            -- 🎉 no goals
#align set.image_sub_const_Iic Set.image_sub_const_Iic

@[simp]
theorem image_sub_const_Ioi : (fun x => x - a) '' Ioi b = Ioi (b - a) := by simp [sub_eq_neg_add]
                                                                            -- 🎉 no goals
#align set.image_sub_const_Ioi Set.image_sub_const_Ioi

@[simp]
theorem image_sub_const_Iio : (fun x => x - a) '' Iio b = Iio (b - a) := by simp [sub_eq_neg_add]
                                                                            -- 🎉 no goals
#align set.image_sub_const_Iio Set.image_sub_const_Iio

@[simp]
theorem image_sub_const_Icc : (fun x => x - a) '' Icc b c = Icc (b - a) (c - a) := by
  simp [sub_eq_neg_add]
  -- 🎉 no goals
#align set.image_sub_const_Icc Set.image_sub_const_Icc

@[simp]
theorem image_sub_const_Ico : (fun x => x - a) '' Ico b c = Ico (b - a) (c - a) := by
  simp [sub_eq_neg_add]
  -- 🎉 no goals
#align set.image_sub_const_Ico Set.image_sub_const_Ico

@[simp]
theorem image_sub_const_Ioc : (fun x => x - a) '' Ioc b c = Ioc (b - a) (c - a) := by
  simp [sub_eq_neg_add]
  -- 🎉 no goals
#align set.image_sub_const_Ioc Set.image_sub_const_Ioc

@[simp]
theorem image_sub_const_Ioo : (fun x => x - a) '' Ioo b c = Ioo (b - a) (c - a) := by
  simp [sub_eq_neg_add]
  -- 🎉 no goals
#align set.image_sub_const_Ioo Set.image_sub_const_Ioo

/-!
### Bijections
-/


theorem Iic_add_bij : BijOn (· + a) (Iic b) (Iic (b + a)) :=
  image_add_const_Iic a b ▸ ((add_left_injective _).injOn _).bijOn_image
#align set.Iic_add_bij Set.Iic_add_bij

theorem Iio_add_bij : BijOn (· + a) (Iio b) (Iio (b + a)) :=
  image_add_const_Iio a b ▸ ((add_left_injective _).injOn _).bijOn_image
#align set.Iio_add_bij Set.Iio_add_bij

end OrderedAddCommGroup

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] (a b c d : α)

@[simp]
theorem preimage_const_add_uIcc : (fun x => a + x) ⁻¹' [[b, c]] = [[b - a, c - a]] := by
  simp only [← Icc_min_max, preimage_const_add_Icc, min_sub_sub_right, max_sub_sub_right]
  -- 🎉 no goals
#align set.preimage_const_add_uIcc Set.preimage_const_add_uIcc

@[simp]
theorem preimage_add_const_uIcc : (fun x => x + a) ⁻¹' [[b, c]] = [[b - a, c - a]] := by
  simpa only [add_comm] using preimage_const_add_uIcc a b c
  -- 🎉 no goals
#align set.preimage_add_const_uIcc Set.preimage_add_const_uIcc

-- TODO: Why is the notation `-[[a, b]]` broken?
@[simp]
theorem preimage_neg_uIcc : @Neg.neg (Set α) Set.neg [[a, b]] = [[-a, -b]] := by
  simp only [← Icc_min_max, preimage_neg_Icc, min_neg_neg, max_neg_neg]
  -- 🎉 no goals
#align set.preimage_neg_uIcc Set.preimage_neg_uIcc

@[simp]
theorem preimage_sub_const_uIcc : (fun x => x - a) ⁻¹' [[b, c]] = [[b + a, c + a]] := by
  simp [sub_eq_add_neg]
  -- 🎉 no goals
#align set.preimage_sub_const_uIcc Set.preimage_sub_const_uIcc

@[simp]
theorem preimage_const_sub_uIcc : (fun x => a - x) ⁻¹' [[b, c]] = [[a - b, a - c]] := by
  simp_rw [← Icc_min_max, preimage_const_sub_Icc]
  -- ⊢ Icc (a - max b c) (a - min b c) = Icc (min (a - b) (a - c)) (max (a - b) (a  …
  simp only [sub_eq_add_neg, min_add_add_left, max_add_add_left, min_neg_neg, max_neg_neg]
  -- 🎉 no goals
#align set.preimage_const_sub_uIcc Set.preimage_const_sub_uIcc

-- @[simp] -- Porting note: simp can prove this module `add_comm`
theorem image_const_add_uIcc : (fun x => a + x) '' [[b, c]] = [[a + b, a + c]] := by simp [add_comm]
                                                                                     -- 🎉 no goals
#align set.image_const_add_uIcc Set.image_const_add_uIcc

-- @[simp] -- Porting note: simp can prove this
theorem image_add_const_uIcc : (fun x => x + a) '' [[b, c]] = [[b + a, c + a]] := by simp
                                                                                     -- 🎉 no goals
#align set.image_add_const_uIcc Set.image_add_const_uIcc

@[simp]
theorem image_const_sub_uIcc : (fun x => a - x) '' [[b, c]] = [[a - b, a - c]] := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp] at this
  -- ⊢ (fun x => a - x) '' [[b, c]] = [[a - b, a - c]]
                                                   -- ⊢ (fun x => a - x) '' [[b, c]] = [[a - b, a - c]]
  simp [sub_eq_add_neg, this, add_comm]
  -- 🎉 no goals
#align set.image_const_sub_uIcc Set.image_const_sub_uIcc

@[simp]
theorem image_sub_const_uIcc : (fun x => x - a) '' [[b, c]] = [[b - a, c - a]] := by
  simp [sub_eq_add_neg, add_comm]
  -- 🎉 no goals
#align set.image_sub_const_uIcc Set.image_sub_const_uIcc

theorem image_neg_uIcc : Neg.neg '' [[a, b]] = [[-a, -b]] := by simp
                                                                -- 🎉 no goals
#align set.image_neg_uIcc Set.image_neg_uIcc

variable {a b c d}

/-- If `[c, d]` is a subinterval of `[a, b]`, then the distance between `c` and `d` is less than or
equal to that of `a` and `b` -/
theorem abs_sub_le_of_uIcc_subset_uIcc (h : [[c, d]] ⊆ [[a, b]]) : |d - c| ≤ |b - a| := by
  rw [← max_sub_min_eq_abs, ← max_sub_min_eq_abs]
  -- ⊢ max c d - min c d ≤ max a b - min a b
  rw [uIcc_subset_uIcc_iff_le] at h
  -- ⊢ max c d - min c d ≤ max a b - min a b
  exact sub_le_sub h.2 h.1
  -- 🎉 no goals
#align set.abs_sub_le_of_uIcc_subset_uIcc Set.abs_sub_le_of_uIcc_subset_uIcc

/-- If `c ∈ [a, b]`, then the distance between `a` and `c` is less than or equal to
that of `a` and `b`  -/
theorem abs_sub_left_of_mem_uIcc (h : c ∈ [[a, b]]) : |c - a| ≤ |b - a| :=
  abs_sub_le_of_uIcc_subset_uIcc <| uIcc_subset_uIcc_left h
#align set.abs_sub_left_of_mem_uIcc Set.abs_sub_left_of_mem_uIcc

/-- If `x ∈ [a, b]`, then the distance between `c` and `b` is less than or equal to
that of `a` and `b`  -/
theorem abs_sub_right_of_mem_uIcc (h : c ∈ [[a, b]]) : |b - c| ≤ |b - a| :=
  abs_sub_le_of_uIcc_subset_uIcc <| uIcc_subset_uIcc_right h
#align set.abs_sub_right_of_mem_uIcc Set.abs_sub_right_of_mem_uIcc

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
#align set.preimage_mul_const_Iio Set.preimage_mul_const_Iio

@[simp]
theorem preimage_mul_const_Ioi (a : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ioi a = Ioi (a / c) :=
  ext fun _x => (div_lt_iff h).symm
#align set.preimage_mul_const_Ioi Set.preimage_mul_const_Ioi

@[simp]
theorem preimage_mul_const_Iic (a : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Iic a = Iic (a / c) :=
  ext fun _x => (le_div_iff h).symm
#align set.preimage_mul_const_Iic Set.preimage_mul_const_Iic

@[simp]
theorem preimage_mul_const_Ici (a : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ici a = Ici (a / c) :=
  ext fun _x => (div_le_iff h).symm
#align set.preimage_mul_const_Ici Set.preimage_mul_const_Ici

@[simp]
theorem preimage_mul_const_Ioo (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ioo a b = Ioo (a / c) (b / c) := by simp [← Ioi_inter_Iio, h]
                                                             -- 🎉 no goals
#align set.preimage_mul_const_Ioo Set.preimage_mul_const_Ioo

@[simp]
theorem preimage_mul_const_Ioc (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ioc a b = Ioc (a / c) (b / c) := by simp [← Ioi_inter_Iic, h]
                                                             -- 🎉 no goals
#align set.preimage_mul_const_Ioc Set.preimage_mul_const_Ioc

@[simp]
theorem preimage_mul_const_Ico (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ico a b = Ico (a / c) (b / c) := by simp [← Ici_inter_Iio, h]
                                                             -- 🎉 no goals
#align set.preimage_mul_const_Ico Set.preimage_mul_const_Ico

@[simp]
theorem preimage_mul_const_Icc (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Icc a b = Icc (a / c) (b / c) := by simp [← Ici_inter_Iic, h]
                                                             -- 🎉 no goals
#align set.preimage_mul_const_Icc Set.preimage_mul_const_Icc

@[simp]
theorem preimage_mul_const_Iio_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Iio a = Ioi (a / c) :=
  ext fun _x => (div_lt_iff_of_neg h).symm
#align set.preimage_mul_const_Iio_of_neg Set.preimage_mul_const_Iio_of_neg

@[simp]
theorem preimage_mul_const_Ioi_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioi a = Iio (a / c) :=
  ext fun _x => (lt_div_iff_of_neg h).symm
#align set.preimage_mul_const_Ioi_of_neg Set.preimage_mul_const_Ioi_of_neg

@[simp]
theorem preimage_mul_const_Iic_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Iic a = Ici (a / c) :=
  ext fun _x => (div_le_iff_of_neg h).symm
#align set.preimage_mul_const_Iic_of_neg Set.preimage_mul_const_Iic_of_neg

@[simp]
theorem preimage_mul_const_Ici_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ici a = Iic (a / c) :=
  ext fun _x => (le_div_iff_of_neg h).symm
#align set.preimage_mul_const_Ici_of_neg Set.preimage_mul_const_Ici_of_neg

@[simp]
theorem preimage_mul_const_Ioo_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioo a b = Ioo (b / c) (a / c) := by simp [← Ioi_inter_Iio, h, inter_comm]
                                                             -- 🎉 no goals
#align set.preimage_mul_const_Ioo_of_neg Set.preimage_mul_const_Ioo_of_neg

@[simp]
theorem preimage_mul_const_Ioc_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioc a b = Ico (b / c) (a / c) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, h, inter_comm]
  -- 🎉 no goals
#align set.preimage_mul_const_Ioc_of_neg Set.preimage_mul_const_Ioc_of_neg

@[simp]
theorem preimage_mul_const_Ico_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ico a b = Ioc (b / c) (a / c) := by
  simp [← Ici_inter_Iio, ← Ioi_inter_Iic, h, inter_comm]
  -- 🎉 no goals
#align set.preimage_mul_const_Ico_of_neg Set.preimage_mul_const_Ico_of_neg

@[simp]
theorem preimage_mul_const_Icc_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Icc a b = Icc (b / c) (a / c) := by simp [← Ici_inter_Iic, h, inter_comm]
                                                             -- 🎉 no goals
#align set.preimage_mul_const_Icc_of_neg Set.preimage_mul_const_Icc_of_neg

@[simp]
theorem preimage_const_mul_Iio (a : α) {c : α} (h : 0 < c) : (· * ·) c ⁻¹' Iio a = Iio (a / c) :=
  ext fun _x => (lt_div_iff' h).symm
#align set.preimage_const_mul_Iio Set.preimage_const_mul_Iio

@[simp]
theorem preimage_const_mul_Ioi (a : α) {c : α} (h : 0 < c) : (· * ·) c ⁻¹' Ioi a = Ioi (a / c) :=
  ext fun _x => (div_lt_iff' h).symm
#align set.preimage_const_mul_Ioi Set.preimage_const_mul_Ioi

@[simp]
theorem preimage_const_mul_Iic (a : α) {c : α} (h : 0 < c) : (· * ·) c ⁻¹' Iic a = Iic (a / c) :=
  ext fun _x => (le_div_iff' h).symm
#align set.preimage_const_mul_Iic Set.preimage_const_mul_Iic

@[simp]
theorem preimage_const_mul_Ici (a : α) {c : α} (h : 0 < c) : (· * ·) c ⁻¹' Ici a = Ici (a / c) :=
  ext fun _x => (div_le_iff' h).symm
#align set.preimage_const_mul_Ici Set.preimage_const_mul_Ici

@[simp]
theorem preimage_const_mul_Ioo (a b : α) {c : α} (h : 0 < c) :
    (· * ·) c ⁻¹' Ioo a b = Ioo (a / c) (b / c) := by simp [← Ioi_inter_Iio, h]
                                                      -- 🎉 no goals
#align set.preimage_const_mul_Ioo Set.preimage_const_mul_Ioo

@[simp]
theorem preimage_const_mul_Ioc (a b : α) {c : α} (h : 0 < c) :
    (· * ·) c ⁻¹' Ioc a b = Ioc (a / c) (b / c) := by simp [← Ioi_inter_Iic, h]
                                                      -- 🎉 no goals
#align set.preimage_const_mul_Ioc Set.preimage_const_mul_Ioc

@[simp]
theorem preimage_const_mul_Ico (a b : α) {c : α} (h : 0 < c) :
    (· * ·) c ⁻¹' Ico a b = Ico (a / c) (b / c) := by simp [← Ici_inter_Iio, h]
                                                      -- 🎉 no goals
#align set.preimage_const_mul_Ico Set.preimage_const_mul_Ico

@[simp]
theorem preimage_const_mul_Icc (a b : α) {c : α} (h : 0 < c) :
    (· * ·) c ⁻¹' Icc a b = Icc (a / c) (b / c) := by simp [← Ici_inter_Iic, h]
                                                      -- 🎉 no goals
#align set.preimage_const_mul_Icc Set.preimage_const_mul_Icc

@[simp]
theorem preimage_const_mul_Iio_of_neg (a : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' Iio a = Ioi (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Iio_of_neg a h
  -- 🎉 no goals
#align set.preimage_const_mul_Iio_of_neg Set.preimage_const_mul_Iio_of_neg

@[simp]
theorem preimage_const_mul_Ioi_of_neg (a : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' Ioi a = Iio (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioi_of_neg a h
  -- 🎉 no goals
#align set.preimage_const_mul_Ioi_of_neg Set.preimage_const_mul_Ioi_of_neg

@[simp]
theorem preimage_const_mul_Iic_of_neg (a : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' Iic a = Ici (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Iic_of_neg a h
  -- 🎉 no goals
#align set.preimage_const_mul_Iic_of_neg Set.preimage_const_mul_Iic_of_neg

@[simp]
theorem preimage_const_mul_Ici_of_neg (a : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' Ici a = Iic (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ici_of_neg a h
  -- 🎉 no goals
#align set.preimage_const_mul_Ici_of_neg Set.preimage_const_mul_Ici_of_neg

@[simp]
theorem preimage_const_mul_Ioo_of_neg (a b : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' Ioo a b = Ioo (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioo_of_neg a b h
  -- 🎉 no goals
#align set.preimage_const_mul_Ioo_of_neg Set.preimage_const_mul_Ioo_of_neg

@[simp]
theorem preimage_const_mul_Ioc_of_neg (a b : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' Ioc a b = Ico (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioc_of_neg a b h
  -- 🎉 no goals
#align set.preimage_const_mul_Ioc_of_neg Set.preimage_const_mul_Ioc_of_neg

@[simp]
theorem preimage_const_mul_Ico_of_neg (a b : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' Ico a b = Ioc (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ico_of_neg a b h
  -- 🎉 no goals
#align set.preimage_const_mul_Ico_of_neg Set.preimage_const_mul_Ico_of_neg

@[simp]
theorem preimage_const_mul_Icc_of_neg (a b : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' Icc a b = Icc (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Icc_of_neg a b h
  -- 🎉 no goals
#align set.preimage_const_mul_Icc_of_neg Set.preimage_const_mul_Icc_of_neg

@[simp]
theorem preimage_mul_const_uIcc (ha : a ≠ 0) (b c : α) :
    (fun x => x * a) ⁻¹' [[b, c]] = [[b / a, c / a]] :=
  (lt_or_gt_of_ne ha).elim
    (fun h => by
      simp [← Icc_min_max, h, h.le, min_div_div_right_of_nonpos, max_div_div_right_of_nonpos])
      -- 🎉 no goals
    fun ha : 0 < a => by simp [← Icc_min_max, ha, ha.le, min_div_div_right, max_div_div_right]
                         -- 🎉 no goals
#align set.preimage_mul_const_uIcc Set.preimage_mul_const_uIcc

@[simp]
theorem preimage_const_mul_uIcc (ha : a ≠ 0) (b c : α) :
    (fun x => a * x) ⁻¹' [[b, c]] = [[b / a, c / a]] := by
  simp only [← preimage_mul_const_uIcc ha, mul_comm]
  -- 🎉 no goals
#align set.preimage_const_mul_uIcc Set.preimage_const_mul_uIcc

@[simp]
theorem preimage_div_const_uIcc (ha : a ≠ 0) (b c : α) :
    (fun x => x / a) ⁻¹' [[b, c]] = [[b * a, c * a]] := by
  simp only [div_eq_mul_inv, preimage_mul_const_uIcc (inv_ne_zero ha), inv_inv]
  -- 🎉 no goals
#align set.preimage_div_const_uIcc Set.preimage_div_const_uIcc

@[simp]
theorem image_mul_const_uIcc (a b c : α) : (fun x => x * a) '' [[b, c]] = [[b * a, c * a]] :=
  if ha : a = 0 then by simp [ha]
                        -- 🎉 no goals
  else calc
    (fun x => x * a) '' [[b, c]] = (fun x => x * a⁻¹) ⁻¹' [[b, c]] :=
      (Units.mk0 a ha).mulRight.image_eq_preimage _
    _ = (fun x => x / a) ⁻¹' [[b, c]] := by simp only [div_eq_mul_inv]
                                            -- 🎉 no goals
    _ = [[b * a, c * a]] := preimage_div_const_uIcc ha _ _
#align set.image_mul_const_uIcc Set.image_mul_const_uIcc

@[simp]
theorem image_const_mul_uIcc (a b c : α) : (fun x => a * x) '' [[b, c]] = [[a * b, a * c]] := by
  simpa only [mul_comm] using image_mul_const_uIcc a b c
  -- 🎉 no goals
#align set.image_const_mul_uIcc Set.image_const_mul_uIcc

@[simp]
theorem image_div_const_uIcc (a b c : α) : (fun x => x / a) '' [[b, c]] = [[b / a, c / a]] := by
  simp only [div_eq_mul_inv, image_mul_const_uIcc]
  -- 🎉 no goals
#align set.image_div_const_uIcc Set.image_div_const_uIcc

theorem image_mul_right_Icc' (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) '' Icc a b = Icc (a * c) (b * c) :=
  ((Units.mk0 c h.ne').mulRight.image_eq_preimage _).trans (by simp [h, division_def])
                                                               -- 🎉 no goals
#align set.image_mul_right_Icc' Set.image_mul_right_Icc'

theorem image_mul_right_Icc {a b c : α} (hab : a ≤ b) (hc : 0 ≤ c) :
    (fun x => x * c) '' Icc a b = Icc (a * c) (b * c) := by
  cases eq_or_lt_of_le hc
  -- ⊢ (fun x => x * c) '' Icc a b = Icc (a * c) (b * c)
  · subst c
    -- ⊢ (fun x => x * 0) '' Icc a b = Icc (a * 0) (b * 0)
    simp [(nonempty_Icc.2 hab).image_const]
    -- 🎉 no goals
  exact image_mul_right_Icc' a b ‹0 < c›
  -- 🎉 no goals
#align set.image_mul_right_Icc Set.image_mul_right_Icc

theorem image_mul_left_Icc' {a : α} (h : 0 < a) (b c : α) :
    (· * ·) a '' Icc b c = Icc (a * b) (a * c) := by
  convert image_mul_right_Icc' b c h using 1 <;> simp only [mul_comm _ a]
  -- ⊢ (fun x x_1 => x * x_1) a '' Icc b c = (fun x => x * a) '' Icc b c
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
#align set.image_mul_left_Icc' Set.image_mul_left_Icc'

theorem image_mul_left_Icc {a b c : α} (ha : 0 ≤ a) (hbc : b ≤ c) :
    (· * ·) a '' Icc b c = Icc (a * b) (a * c) := by
  convert image_mul_right_Icc hbc ha using 1 <;> simp only [mul_comm _ a]
  -- ⊢ (fun x x_1 => x * x_1) a '' Icc b c = (fun x => x * a) '' Icc b c
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
#align set.image_mul_left_Icc Set.image_mul_left_Icc

theorem image_mul_right_Ioo (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) '' Ioo a b = Ioo (a * c) (b * c) :=
  ((Units.mk0 c h.ne').mulRight.image_eq_preimage _).trans (by simp [h, division_def])
                                                               -- 🎉 no goals
#align set.image_mul_right_Ioo Set.image_mul_right_Ioo

theorem image_mul_left_Ioo {a : α} (h : 0 < a) (b c : α) :
    (· * ·) a '' Ioo b c = Ioo (a * b) (a * c) := by
  convert image_mul_right_Ioo b c h using 1 <;> simp only [mul_comm _ a]
  -- ⊢ (fun x x_1 => x * x_1) a '' Ioo b c = (fun x => x * a) '' Ioo b c
                                                -- 🎉 no goals
                                                -- 🎉 no goals
#align set.image_mul_left_Ioo Set.image_mul_left_Ioo

/-- The (pre)image under `inv` of `Ioo 0 a` is `Ioi a⁻¹`. -/
theorem inv_Ioo_0_left {a : α} (ha : 0 < a) : (Ioo 0 a)⁻¹ = Ioi a⁻¹ := by
  ext x
  -- ⊢ x ∈ (Ioo 0 a)⁻¹ ↔ x ∈ Ioi a⁻¹
  exact
    ⟨fun h => inv_inv x ▸ (inv_lt_inv ha h.1).2 h.2, fun h =>
      ⟨inv_pos.2 <| (inv_pos.2 ha).trans h,
        inv_inv a ▸ (inv_lt_inv ((inv_pos.2 ha).trans h) (inv_pos.2 ha)).2 h⟩⟩
#align set.inv_Ioo_0_left Set.inv_Ioo_0_left

theorem inv_Ioi {a : α} (ha : 0 < a) : (Ioi a)⁻¹ = Ioo 0 a⁻¹ := by
  rw [inv_eq_iff_eq_inv, inv_Ioo_0_left (inv_pos.2 ha), inv_inv]
  -- 🎉 no goals
#align set.inv_Ioi Set.inv_Ioi

theorem image_const_mul_Ioi_zero {k : Type*} [LinearOrderedField k] {x : k} (hx : 0 < x) :
    (fun y => x * y) '' Ioi (0 : k) = Ioi 0 := by
  erw [(Units.mk0 x hx.ne').mulLeft.image_eq_preimage, preimage_const_mul_Ioi 0 (inv_pos.mpr hx),
    zero_div]
#align set.image_const_mul_Ioi_zero Set.image_const_mul_Ioi_zero

/-!
### Images under `x ↦ a * x + b`
-/


@[simp]
theorem image_affine_Icc' {a : α} (h : 0 < a) (b c d : α) :
    (fun x => a * x + b) '' Icc c d = Icc (a * c + b) (a * d + b) := by
  suffices (fun x => x + b) '' ((fun x => a * x) '' Icc c d) = Icc (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Icc' h, image_add_const_Icc]
  -- 🎉 no goals
#align set.image_affine_Icc' Set.image_affine_Icc'

end LinearOrderedField

end Set
