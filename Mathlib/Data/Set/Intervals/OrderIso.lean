/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
! This file was ported from Lean 3 source module data.set.intervals.order_iso
! leanprover-community/mathlib commit d012cd09a9b256d870751284dd6a29882b0be105
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Order.Hom.Set

/-!
# Lemmas about images of intervals under order isomorphisms.
-/


variable {α β : Type _}

open Set

namespace OrderIso

section Preorder

variable [Preorder α] [Preorder β]

@[simp]
theorem preimage_Iic (e : α ≃o β) (b : β) : e ⁻¹' iic b = iic (e.symm b) := by
  ext x
  simp [← e.le_iff_le]
#align order_iso.preimage_Iic OrderIso.preimage_Iic

@[simp]
theorem preimage_Ici (e : α ≃o β) (b : β) : e ⁻¹' ici b = ici (e.symm b) := by
  ext x
  simp [← e.le_iff_le]
#align order_iso.preimage_Ici OrderIso.preimage_Ici

@[simp]
theorem preimage_Iio (e : α ≃o β) (b : β) : e ⁻¹' iio b = iio (e.symm b) := by
  ext x
  simp [← e.lt_iff_lt]
#align order_iso.preimage_Iio OrderIso.preimage_Iio

@[simp]
theorem preimage_Ioi (e : α ≃o β) (b : β) : e ⁻¹' ioi b = ioi (e.symm b) := by
  ext x
  simp [← e.lt_iff_lt]
#align order_iso.preimage_Ioi OrderIso.preimage_Ioi

@[simp]
theorem preimage_Icc (e : α ≃o β) (a b : β) : e ⁻¹' icc a b = icc (e.symm a) (e.symm b) := by
  simp [← Ici_inter_Iic]
#align order_iso.preimage_Icc OrderIso.preimage_Icc

@[simp]
theorem preimage_Ico (e : α ≃o β) (a b : β) : e ⁻¹' ico a b = ico (e.symm a) (e.symm b) := by
  simp [← Ici_inter_Iio]
#align order_iso.preimage_Ico OrderIso.preimage_Ico

@[simp]
theorem preimage_Ioc (e : α ≃o β) (a b : β) : e ⁻¹' ioc a b = ioc (e.symm a) (e.symm b) := by
  simp [← Ioi_inter_Iic]
#align order_iso.preimage_Ioc OrderIso.preimage_Ioc

@[simp]
theorem preimage_Ioo (e : α ≃o β) (a b : β) : e ⁻¹' ioo a b = ioo (e.symm a) (e.symm b) := by
  simp [← Ioi_inter_Iio]
#align order_iso.preimage_Ioo OrderIso.preimage_Ioo

@[simp]
theorem image_Iic (e : α ≃o β) (a : α) : e '' iic a = iic (e a) := by
  rw [e.image_eq_preimage, e.symm.preimage_Iic, e.symm_symm]
#align order_iso.image_Iic OrderIso.image_Iic

@[simp]
theorem image_Ici (e : α ≃o β) (a : α) : e '' ici a = ici (e a) :=
  e.dual.image_Iic a
#align order_iso.image_Ici OrderIso.image_Ici

@[simp]
theorem image_Iio (e : α ≃o β) (a : α) : e '' iio a = iio (e a) := by
  rw [e.image_eq_preimage, e.symm.preimage_Iio, e.symm_symm]
#align order_iso.image_Iio OrderIso.image_Iio

@[simp]
theorem image_Ioi (e : α ≃o β) (a : α) : e '' ioi a = ioi (e a) :=
  e.dual.image_Iio a
#align order_iso.image_Ioi OrderIso.image_Ioi

@[simp]
theorem image_Ioo (e : α ≃o β) (a b : α) : e '' ioo a b = ioo (e a) (e b) := by
  rw [e.image_eq_preimage, e.symm.preimage_Ioo, e.symm_symm]
#align order_iso.image_Ioo OrderIso.image_Ioo

@[simp]
theorem image_Ioc (e : α ≃o β) (a b : α) : e '' ioc a b = ioc (e a) (e b) := by
  rw [e.image_eq_preimage, e.symm.preimage_Ioc, e.symm_symm]
#align order_iso.image_Ioc OrderIso.image_Ioc

@[simp]
theorem image_Ico (e : α ≃o β) (a b : α) : e '' ico a b = ico (e a) (e b) := by
  rw [e.image_eq_preimage, e.symm.preimage_Ico, e.symm_symm]
#align order_iso.image_Ico OrderIso.image_Ico

@[simp]
theorem image_Icc (e : α ≃o β) (a b : α) : e '' icc a b = icc (e a) (e b) := by
  rw [e.image_eq_preimage, e.symm.preimage_Icc, e.symm_symm]
#align order_iso.image_Icc OrderIso.image_Icc

end Preorder

/-- Order isomorphism between `Iic (⊤ : α)` and `α` when `α` has a top element -/
def iicTop [Preorder α] [OrderTop α] : Set.iic (⊤ : α) ≃o α :=
  { @Equiv.subtypeUnivEquiv α (Set.iic (⊤ : α)) fun x => le_top with
    map_rel_iff' := fun x y => by rfl }
#align order_iso.Iic_top OrderIso.iicTop

/-- Order isomorphism between `Ici (⊥ : α)` and `α` when `α` has a bottom element -/
def iciBot [Preorder α] [OrderBot α] : Set.ici (⊥ : α) ≃o α :=
  { @Equiv.subtypeUnivEquiv α (Set.ici (⊥ : α)) fun x => bot_le with
    map_rel_iff' := fun x y => by rfl }
#align order_iso.Ici_bot OrderIso.iciBot

end OrderIso
