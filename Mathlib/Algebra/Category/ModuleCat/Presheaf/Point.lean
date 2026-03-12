/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Fiber functors on presheaves of modules

Let `Φ` be a point of a site `(C, J)`. We define a fiber functor
`Φ.presheafOfModulesFiberOfRing R : PresheafOfModules R ⥤ ModuleCat (Φ.presheafFiber.obj R`.
for presheaves of modules over a presheaf of rings `R`.
(In the case `R` is a presheaf of commutative rings, we also provide a definition
`Φ.presheafOfModulesFiber` for which the colimit ring is computed in the
category of commutative rings instead of the category of rings.)

-/

@[expose] public section

universe w v u

open CategoryTheory Limits GrothendieckTopology MonoidalCategory

attribute [local instance] hasColimitsOfShape_of_finallySmall
  IsFiltered.isSifted FinallySmall.preservesColimitsOfShape_of_isFiltered

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C} (Φ : Point.{w} J)

section

variable {R : Cᵒᵖ ⥤ RingCat.{w}} {c : Cocone ((CategoryOfElements.π Φ.fiber).op ⋙ R)}
  (hc : IsColimit c)

/-- Given a point `Φ` of a site `(C, J)`, a presheaf of modules `R` on `C`
and a colimit cocone `c` for the diagram which computes the fiber of `R`, this is
the fiber functor `PresheafOfModules R ⥤ ModuleCat c.pt` for presheaves
of modules. -/
noncomputable def presheafOfModulesFiberOfIsColimit : PresheafOfModules.{w} R ⥤ ModuleCat c.pt :=
  PresheafOfModules.pushforward₀ _ _ ⋙ PresheafOfModules.colimitFunctor hc

/-- The composition of a fiber functor on a category of presheaves of modules
and the forgetful functor to the category of abelian groups is
induced by the fiber functor acting on presheaves of abelian groups. -/
noncomputable def presheafOfModulesFiberOfIsColimitCompForget₂Iso :
    Φ.presheafOfModulesFiberOfIsColimit hc ⋙ forget₂ _ AddCommGrpCat ≅
      PresheafOfModules.toPresheaf _ ⋙ Φ.presheafFiber :=
  Iso.refl _

end

/-- The fiber functor for presheaves of modules over a presheaf of rings `R`
that is induced by a point of a site. In case `R` is commutative,
it is advisable to use `presheafOfModulesFiber` instead. -/
noncomputable def presheafOfModulesFiberOfRing (R : Cᵒᵖ ⥤ RingCat.{w}) :
    PresheafOfModules.{w} R ⥤ ModuleCat.{w} (Φ.presheafFiber.obj R :) :=
  Φ.presheafOfModulesFiberOfIsColimit (colimit.isColimit _)

/-- The fiber functor for presheaves of modules over a presheaf of
commutative rings `R` that is induced by a point of a site. -/
noncomputable def presheafOfModulesFiber (R : Cᵒᵖ ⥤ CommRingCat.{w}) :
    PresheafOfModules.{w} (R ⋙ forget₂ _ _) ⥤
      ModuleCat.{w} (Φ.presheafFiber.obj R :) :=
  Φ.presheafOfModulesFiberOfIsColimit (R := R ⋙ forget₂ _ _ )
    (isColimitOfPreserves (forget₂ _ RingCat)
      (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ R)))

end CategoryTheory.GrothendieckTopology.Point
