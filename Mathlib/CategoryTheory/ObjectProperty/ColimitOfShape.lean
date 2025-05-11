/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Colimits

-/

namespace CategoryTheory

variable {C : Type*} [Category C]

namespace Limits

variable (J : Type*) [Category J]

structure ColimitOfShape (X : C) where
  F : J ⥤ C
  ι : F ⟶ (Functor.const J).obj X
  isColimit : IsColimit (Cocone.mk X ι)

variable {J} in
@[simps]
def ColimitOfShape.ofIsColimit {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) :
    ColimitOfShape J c.pt where
  F := F
  ι := c.ι
  isColimit := hc

variable {J} in
noncomputable def ColimitOfShape.colimit (F : J ⥤ C) [HasColimit F] :
    ColimitOfShape J (colimit F) :=
  .ofIsColimit (colimit.isColimit F)

end Limits

namespace ObjectProperty

variable (P : ObjectProperty C) (J : Type*) [Category J]

structure ColimitOfShape (X : C) extends Limits.ColimitOfShape J X where
  hF (j : J) : P (F.obj j)

variable {P J} in
@[simps toColimitOfShape]
def ColimitOfShape.ofLE {X : C} (hX : P.ColimitOfShape J X) {Q : ObjectProperty C}
    (h : P ≤ Q) :
    Q.ColimitOfShape J X where
  toColimitOfShape := hX.toColimitOfShape
  hF j := h _ (hX.hF j)

def colimitOfShape : ObjectProperty C :=
  fun X ↦ Nonempty (P.ColimitOfShape J X)

end ObjectProperty

end CategoryTheory
