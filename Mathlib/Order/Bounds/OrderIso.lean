/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Order.Bounds.Image
public import Mathlib.Order.Hom.Set

/-!
# Order isomorphisms and bounds.
-/

public section

open Set

namespace OrderIso

variable {α β : Type*} [Preorder α] [Preorder β] (f : α ≃o β)

@[to_dual]
theorem upperBounds_image {s : Set α} : upperBounds (f '' s) = f '' upperBounds s :=
  Subset.antisymm
    (fun x hx =>
      ⟨f.symm x, fun _ hy => f.le_symm_apply.2 (hx <| mem_image_of_mem _ hy), f.apply_symm_apply x⟩)
    f.monotone.image_upperBounds_subset_upperBounds_image

@[to_dual (attr := simp)]
theorem isLUB_image {s : Set α} {x : β} : IsLUB (f '' s) x ↔ IsLUB s (f.symm x) :=
  ⟨fun h => IsLUB.of_image (by simp) ((f.apply_symm_apply x).symm ▸ h), fun h =>
    (IsLUB.of_image (by simp)) <| (f.symm_image_image s).symm ▸ h⟩

@[to_dual]
theorem isLUB_image' {s : Set α} {x : α} : IsLUB (f '' s) (f x) ↔ IsLUB s x := by
  rw [isLUB_image, f.symm_apply_apply]

@[to_dual (attr := simp)]
theorem isLUB_preimage {s : Set β} {x : α} : IsLUB (f ⁻¹' s) x ↔ IsLUB s (f x) := by
  rw [← f.symm_symm, ← image_eq_preimage_symm, isLUB_image]

@[to_dual]
theorem isLUB_preimage' {s : Set β} {x : β} : IsLUB (f ⁻¹' s) (f.symm x) ↔ IsLUB s x := by
  rw [isLUB_preimage, f.apply_symm_apply]

end OrderIso
