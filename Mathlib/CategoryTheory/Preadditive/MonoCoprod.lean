/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.MonoCoprod

/-!
# Preadditive categories satisfy `MonoCoprod`

In a preadditive category, the canonical maps `A ⟶ A ⨿ B` are monomorphisms
(when `HasBinaryCoproduct A B` hold).

-/

namespace CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
instance {C : Type*} [Category* C] [Preadditive C] : MonoCoprod C where
  binaryCofan_inl A B c hc := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro P g hg
    simpa using hg =≫ BinaryCofan.IsColimit.desc hc (𝟙 A) 0

end CategoryTheory.Limits
