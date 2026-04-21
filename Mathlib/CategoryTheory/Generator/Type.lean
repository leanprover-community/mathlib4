/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Generator.Basic

/-!
# Generator of Type

In this file, we show that `PUnit` is a separator of the category `Type u`.

-/
set_option backward.defeqAttrib.useBackward true

public section

universe u

namespace CategoryTheory

lemma Types.isSeparator_punit : IsSeparator (PUnit.{u + 1}) := by
  intro X Y f g h
  ext x
  exact ConcreteCategory.congr_hom (h PUnit (by simp) (TypeCat.ofHom (fun _ ↦ x)))
    .unit

end CategoryTheory
