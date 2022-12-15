/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
! This file was ported from Lean 3 source module order.bounds.order_iso
! leanprover-community/mathlib commit a59dad53320b73ef180174aae867addd707ef00e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Hom.Set

/-!
# Order isomorhpisms and bounds.
-/


variable {α β : Type _}

open Set

namespace OrderIso

variable [Preorder α] [Preorder β] (f : α ≃o β)

theorem upper_bounds_image {s : Set α} : upperBounds (f '' s) = f '' upperBounds s :=
  Subset.antisymm
    (fun x hx =>
      ⟨f.symm x, fun y hy => f.le_symm_apply.2 (hx <| mem_image_of_mem _ hy), f.apply_symm_apply x⟩)
    f.Monotone.image_upper_bounds_subset_upper_bounds_image
#align order_iso.upper_bounds_image OrderIso.upper_bounds_image

theorem lower_bounds_image {s : Set α} : lowerBounds (f '' s) = f '' lowerBounds s :=
  @upper_bounds_image αᵒᵈ βᵒᵈ _ _ f.dual _
#align order_iso.lower_bounds_image OrderIso.lower_bounds_image

@[simp]
theorem is_lub_image {s : Set α} {x : β} : IsLub (f '' s) x ↔ IsLub s (f.symm x) :=
  ⟨fun h => IsLub.of_image (fun _ _ => f.le_iff_le) ((f.apply_symm_apply x).symm ▸ h), fun h =>
    (IsLub.of_image fun _ _ => f.symm.le_iff_le) <| (f.symm_image_image s).symm ▸ h⟩
#align order_iso.is_lub_image OrderIso.is_lub_image

theorem is_lub_image' {s : Set α} {x : α} : IsLub (f '' s) (f x) ↔ IsLub s x := by
  rw [is_lub_image, f.symm_apply_apply]
#align order_iso.is_lub_image' OrderIso.is_lub_image'

@[simp]
theorem is_glb_image {s : Set α} {x : β} : IsGlb (f '' s) x ↔ IsGlb s (f.symm x) :=
  f.dual.is_lub_image
#align order_iso.is_glb_image OrderIso.is_glb_image

theorem is_glb_image' {s : Set α} {x : α} : IsGlb (f '' s) (f x) ↔ IsGlb s x :=
  f.dual.is_lub_image'
#align order_iso.is_glb_image' OrderIso.is_glb_image'

@[simp]
theorem is_lub_preimage {s : Set β} {x : α} : IsLub (f ⁻¹' s) x ↔ IsLub s (f x) := by
  rw [← f.symm_symm, ← image_eq_preimage, is_lub_image]
#align order_iso.is_lub_preimage OrderIso.is_lub_preimage

theorem is_lub_preimage' {s : Set β} {x : β} : IsLub (f ⁻¹' s) (f.symm x) ↔ IsLub s x := by
  rw [is_lub_preimage, f.apply_symm_apply]
#align order_iso.is_lub_preimage' OrderIso.is_lub_preimage'

@[simp]
theorem is_glb_preimage {s : Set β} {x : α} : IsGlb (f ⁻¹' s) x ↔ IsGlb s (f x) :=
  f.dual.is_lub_preimage
#align order_iso.is_glb_preimage OrderIso.is_glb_preimage

theorem is_glb_preimage' {s : Set β} {x : β} : IsGlb (f ⁻¹' s) (f.symm x) ↔ IsGlb s x :=
  f.dual.is_lub_preimage'
#align order_iso.is_glb_preimage' OrderIso.is_glb_preimage'

end OrderIso
