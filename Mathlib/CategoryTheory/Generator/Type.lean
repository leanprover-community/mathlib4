/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Generator.Basic

/-!
# Generator of Type

In this file, we show that `PUnit` is a separator of the category `Type u`.

-/

universe u

namespace CategoryTheory

lemma Types.isSeparator_punit : IsSeparator (PUnit.{u + 1}) := by
  intro X Y f g h
  ext x
  exact congr_fun (h PUnit (by simp) (fun _ ↦ x)) .unit

end CategoryTheory
