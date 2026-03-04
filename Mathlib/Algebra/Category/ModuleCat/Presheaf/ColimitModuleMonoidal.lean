/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitModule
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# The colimit module functor is a monoidal functor

-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

attribute [local instance] hasColimitsOfShape_of_finallySmall
  IsFiltered.isSifted FinallySmall.preservesColimitsOfShape_of_isFiltered

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  [IsCofiltered C] [InitiallySmall.{w} C]
  {R : Cᵒᵖ ⥤ CommRingCat.{w}} {cR : Cocone R} (hcR : IsColimit cR)

variable (A : Type w) [CommRing A]

noncomputable def colimitFunctorOfCommRing :
    PresheafOfModules.{w} (R ⋙ forget₂ _ _) ⥤ ModuleCat.{w} cR.pt :=
  colimitFunctor.{w} (isColimitOfPreserves (forget₂ _ RingCat) hcR)

--instance : (colimitFunctorOfCommRing hcR).Monoidal := sorry

end PresheafOfModules
