/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Hom.Set

#align_import order.bounds.order_iso from "leanprover-community/mathlib"@"a59dad53320b73ef180174aae867addd707ef00e"

/-!
# Order isomorphisms and bounds.
-/

set_option autoImplicit true

open Set

namespace OrderIso

variable [Preorder α] [Preorder β] (f : α ≃o β)

theorem upperBounds_image {s : Set α} : upperBounds (f '' s) = f '' upperBounds s :=
  Subset.antisymm
    (fun x hx =>
      ⟨f.symm x, fun _ hy => f.le_symm_apply.2 (hx <| mem_image_of_mem _ hy), f.apply_symm_apply x⟩)
    f.monotone.image_upperBounds_subset_upperBounds_image
#align order_iso.upper_bounds_image OrderIso.upperBounds_image

theorem lowerBounds_image {s : Set α} : lowerBounds (f '' s) = f '' lowerBounds s :=
  @upperBounds_image αᵒᵈ βᵒᵈ _ _ f.dual _
#align order_iso.lower_bounds_image OrderIso.lowerBounds_image

-- Porting note: by simps were `fun _ _ => f.le_iff_le` and `fun _ _ => f.symm.le_iff_le`
@[simp]
theorem isLUB_image {s : Set α} {x : β} : IsLUB (f '' s) x ↔ IsLUB s (f.symm x) :=
  ⟨fun h => IsLUB.of_image (by simp) ((f.apply_symm_apply x).symm ▸ h), fun h =>
                               -- 🎉 no goals
    (IsLUB.of_image (by simp)) <| (f.symm_image_image s).symm ▸ h⟩
                        -- 🎉 no goals
#align order_iso.is_lub_image OrderIso.isLUB_image

theorem isLUB_image' {s : Set α} {x : α} : IsLUB (f '' s) (f x) ↔ IsLUB s x := by
  rw [isLUB_image, f.symm_apply_apply]
  -- 🎉 no goals
#align order_iso.is_lub_image' OrderIso.isLUB_image'

@[simp]
theorem isGLB_image {s : Set α} {x : β} : IsGLB (f '' s) x ↔ IsGLB s (f.symm x) :=
  f.dual.isLUB_image
#align order_iso.is_glb_image OrderIso.isGLB_image

theorem isGLB_image' {s : Set α} {x : α} : IsGLB (f '' s) (f x) ↔ IsGLB s x :=
  f.dual.isLUB_image'
#align order_iso.is_glb_image' OrderIso.isGLB_image'

@[simp]
theorem isLUB_preimage {s : Set β} {x : α} : IsLUB (f ⁻¹' s) x ↔ IsLUB s (f x) := by
  rw [← f.symm_symm, ← image_eq_preimage, isLUB_image]
  -- 🎉 no goals
#align order_iso.is_lub_preimage OrderIso.isLUB_preimage

theorem isLUB_preimage' {s : Set β} {x : β} : IsLUB (f ⁻¹' s) (f.symm x) ↔ IsLUB s x := by
  rw [isLUB_preimage, f.apply_symm_apply]
  -- 🎉 no goals
#align order_iso.is_lub_preimage' OrderIso.isLUB_preimage'

@[simp]
theorem isGLB_preimage {s : Set β} {x : α} : IsGLB (f ⁻¹' s) x ↔ IsGLB s (f x) :=
  f.dual.isLUB_preimage
#align order_iso.is_glb_preimage OrderIso.isGLB_preimage

theorem isGLB_preimage' {s : Set β} {x : β} : IsGLB (f ⁻¹' s) (f.symm x) ↔ IsGLB s x :=
  f.dual.isLUB_preimage'
#align order_iso.is_glb_preimage' OrderIso.isGLB_preimage'

end OrderIso
