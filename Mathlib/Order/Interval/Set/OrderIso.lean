/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
module

public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Hom.Set

/-!
# Lemmas about images of intervals under order isomorphisms.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open Set

namespace OrderIso

section Preorder

variable {α β : Type*} [Preorder α] [Preorder β]

@[to_dual (attr := simp)]
theorem preimage_Iic (e : α ≃o β) (b : β) : e ⁻¹' Iic b = Iic (e.symm b) := by
  ext x
  simp [← e.le_iff_le]

@[to_dual (attr := simp)]
theorem preimage_Iio (e : α ≃o β) (b : β) : e ⁻¹' Iio b = Iio (e.symm b) := by
  ext x
  simp [← e.lt_iff_lt]

@[simp, to_dual self]
theorem preimage_Icc (e : α ≃o β) (a b : β) : e ⁻¹' Icc a b = Icc (e.symm a) (e.symm b) := by
  simp [← Ici_inter_Iic]

@[to_dual (attr := simp) (reorder := a b)]
theorem preimage_Ico (e : α ≃o β) (a b : β) : e ⁻¹' Ico a b = Ico (e.symm a) (e.symm b) := by
  simp [← Ici_inter_Iio]

@[simp, to_dual self]
theorem preimage_Ioo (e : α ≃o β) (a b : β) : e ⁻¹' Ioo a b = Ioo (e.symm a) (e.symm b) := by
  simp [← Ioi_inter_Iio]

@[to_dual (attr := simp)]
theorem image_Iic (e : α ≃o β) (a : α) : e '' Iic a = Iic (e a) := by
  rw [e.image_eq_preimage_symm, e.symm.preimage_Iic, e.symm_symm]

@[to_dual (attr := simp)]
theorem image_Iio (e : α ≃o β) (a : α) : e '' Iio a = Iio (e a) := by
  rw [e.image_eq_preimage_symm, e.symm.preimage_Iio, e.symm_symm]

@[simp, to_dual self]
theorem image_Ioo (e : α ≃o β) (a b : α) : e '' Ioo a b = Ioo (e a) (e b) := by
  rw [e.image_eq_preimage_symm, e.symm.preimage_Ioo, e.symm_symm]

@[to_dual (attr := simp) (reorder := a b)]
theorem image_Ioc (e : α ≃o β) (a b : α) : e '' Ioc a b = Ioc (e a) (e b) := by
  rw [e.image_eq_preimage_symm, e.symm.preimage_Ioc, e.symm_symm]

@[simp, to_dual self]
theorem image_Icc (e : α ≃o β) (a b : α) : e '' Icc a b = Icc (e a) (e b) := by
  rw [e.image_eq_preimage_symm, e.symm.preimage_Icc, e.symm_symm]

end Preorder

/-- Order isomorphism between `Iic (⊤ : α)` and `α` when `α` has a top element -/
@[to_dual
/-- Order isomorphism between `Ici (⊥ : α)` and `α` when `α` has a bottom element -/]
def IicTop {α : Type*} [Preorder α] [OrderTop α] : Iic (⊤ : α) ≃o α :=
  { @Equiv.subtypeUnivEquiv α (· ∈ Iic (⊤ : α)) fun _ => le_top with
    map_rel_iff' := @fun x y => by rfl }

end OrderIso
