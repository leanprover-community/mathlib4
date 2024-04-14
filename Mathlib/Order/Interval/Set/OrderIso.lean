/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Hom.Set

#align_import data.set.intervals.order_iso from "leanprover-community/mathlib"@"d012cd09a9b256d870751284dd6a29882b0be105"

/-!
# Lemmas about images of intervals under order isomorphisms.
-/

open Set

namespace OrderIso

section Preorder

variable {α β : Type*} [Preorder α] [Preorder β]

@[simp]
theorem preimage_Iic (e : α ≃o β) (b : β) : e ⁻¹' Iic b = Iic (e.symm b) := by
  ext x
  simp [← e.le_iff_le]
#align order_iso.preimage_Iic OrderIso.preimage_Iic

@[simp]
theorem preimage_Ici (e : α ≃o β) (b : β) : e ⁻¹' Ici b = Ici (e.symm b) := by
  ext x
  simp [← e.le_iff_le]
#align order_iso.preimage_Ici OrderIso.preimage_Ici

@[simp]
theorem preimage_Iio (e : α ≃o β) (b : β) : e ⁻¹' Iio b = Iio (e.symm b) := by
  ext x
  simp [← e.lt_iff_lt]
#align order_iso.preimage_Iio OrderIso.preimage_Iio

@[simp]
theorem preimage_Ioi (e : α ≃o β) (b : β) : e ⁻¹' Ioi b = Ioi (e.symm b) := by
  ext x
  simp [← e.lt_iff_lt]
#align order_iso.preimage_Ioi OrderIso.preimage_Ioi

@[simp]
theorem preimage_Icc (e : α ≃o β) (a b : β) : e ⁻¹' Icc a b = Icc (e.symm a) (e.symm b) := by
  simp [← Ici_inter_Iic]
#align order_iso.preimage_Icc OrderIso.preimage_Icc

@[simp]
theorem preimage_Ico (e : α ≃o β) (a b : β) : e ⁻¹' Ico a b = Ico (e.symm a) (e.symm b) := by
  simp [← Ici_inter_Iio]
#align order_iso.preimage_Ico OrderIso.preimage_Ico

@[simp]
theorem preimage_Ioc (e : α ≃o β) (a b : β) : e ⁻¹' Ioc a b = Ioc (e.symm a) (e.symm b) := by
  simp [← Ioi_inter_Iic]
#align order_iso.preimage_Ioc OrderIso.preimage_Ioc

@[simp]
theorem preimage_Ioo (e : α ≃o β) (a b : β) : e ⁻¹' Ioo a b = Ioo (e.symm a) (e.symm b) := by
  simp [← Ioi_inter_Iio]
#align order_iso.preimage_Ioo OrderIso.preimage_Ioo

@[simp]
theorem image_Iic (e : α ≃o β) (a : α) : e '' Iic a = Iic (e a) := by
  rw [e.image_eq_preimage, e.symm.preimage_Iic, e.symm_symm]
#align order_iso.image_Iic OrderIso.image_Iic

@[simp]
theorem image_Ici (e : α ≃o β) (a : α) : e '' Ici a = Ici (e a) :=
  e.dual.image_Iic a
#align order_iso.image_Ici OrderIso.image_Ici

@[simp]
theorem image_Iio (e : α ≃o β) (a : α) : e '' Iio a = Iio (e a) := by
  rw [e.image_eq_preimage, e.symm.preimage_Iio, e.symm_symm]
#align order_iso.image_Iio OrderIso.image_Iio

@[simp]
theorem image_Ioi (e : α ≃o β) (a : α) : e '' Ioi a = Ioi (e a) :=
  e.dual.image_Iio a
#align order_iso.image_Ioi OrderIso.image_Ioi

@[simp]
theorem image_Ioo (e : α ≃o β) (a b : α) : e '' Ioo a b = Ioo (e a) (e b) := by
  rw [e.image_eq_preimage, e.symm.preimage_Ioo, e.symm_symm]
#align order_iso.image_Ioo OrderIso.image_Ioo

@[simp]
theorem image_Ioc (e : α ≃o β) (a b : α) : e '' Ioc a b = Ioc (e a) (e b) := by
  rw [e.image_eq_preimage, e.symm.preimage_Ioc, e.symm_symm]
#align order_iso.image_Ioc OrderIso.image_Ioc

@[simp]
theorem image_Ico (e : α ≃o β) (a b : α) : e '' Ico a b = Ico (e a) (e b) := by
  rw [e.image_eq_preimage, e.symm.preimage_Ico, e.symm_symm]
#align order_iso.image_Ico OrderIso.image_Ico

@[simp]
theorem image_Icc (e : α ≃o β) (a b : α) : e '' Icc a b = Icc (e a) (e b) := by
  rw [e.image_eq_preimage, e.symm.preimage_Icc, e.symm_symm]
#align order_iso.image_Icc OrderIso.image_Icc

end Preorder

/-- Order isomorphism between `Iic (⊤ : α)` and `α` when `α` has a top element -/
def IicTop {α : Type*} [Preorder α] [OrderTop α] : Iic (⊤ : α) ≃o α :=
  { @Equiv.subtypeUnivEquiv α (Iic (⊤ : α)) fun x => le_top with
    map_rel_iff' := @fun x y => by rfl }
#align order_iso.Iic_top OrderIso.IicTop

/-- Order isomorphism between `Ici (⊥ : α)` and `α` when `α` has a bottom element -/
def IciBot {α : Type*} [Preorder α] [OrderBot α] : Ici (⊥ : α) ≃o α :=
  { @Equiv.subtypeUnivEquiv α (Ici (⊥ : α)) fun x => bot_le with
    map_rel_iff' := @fun x y => by rfl }
#align order_iso.Ici_bot OrderIso.IciBot

end OrderIso
