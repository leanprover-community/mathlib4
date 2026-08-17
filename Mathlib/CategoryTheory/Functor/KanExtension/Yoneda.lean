/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# ...

-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [LocallySmall.{w} C] [LocallySmall.{w} D]

namespace Presheaf

open Limits Opposite

variable (F : C ⥤ D) [∀ (P : Cᵒᵖ ⥤ Type w), F.op.HasLeftKanExtension P]

/-- `F ⋙ shrinkYoneda` is naturally isomorphic to `shrinkYoneda ⋙ F.op.lan`. -/
noncomputable def compShrinkYonedaIsoShrinkYonedaCompLan :
    F ⋙ shrinkYoneda.{w} ≅ shrinkYoneda.{w} ⋙ F.op.lan := by
  have (P : Cᵒᵖ ⥤ Type w) : F.op.HasLeftKanExtension P := inferInstance
  sorry

end Presheaf

end CategoryTheory
