/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Point
public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# Fiber functors on sheaves of modules

-/

@[expose] public section

universe w v u

open CategoryTheory Limits GrothendieckTopology MonoidalCategory

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C} (Φ : Point.{w} J)

/-- Given a point `Φ` of a site `(C, J)`, a sheaf of modules `R` on `(C, J)`
and a colimit cocone `c` for the diagram which computes the fiber of `R`, this is
the fiber functor `SheafOfModules R ⥤ ModuleCat c.pt` for sheaves
of modules. -/
noncomputable abbrev sheafOfModulesFiberOfIsColimit
    {R : Sheaf J RingCat.{w}} {c : Cocone ((CategoryOfElements.π Φ.fiber).op ⋙ R.obj)}
    (hc : IsColimit c) : SheafOfModules.{w} R ⥤ ModuleCat c.pt :=
  SheafOfModules.forget R ⋙ Φ.presheafOfModulesFiberOfIsColimit hc

/-- The fiber functor for sheaves of modules over a sheaf of rings `R`
that is induced by a point of a site. In case `R` is commutative,
it is advisable to use `sheafOfModulesFiber` instead. -/
noncomputable abbrev sheafOfModulesFiberOfRing (R : Sheaf J RingCat.{w}) :
    SheafOfModules.{w} R ⥤ ModuleCat.{w} (Φ.presheafFiber.obj R.obj :) :=
  SheafOfModules.forget R ⋙ Φ.presheafOfModulesFiberOfRing R.obj

/-- The fiber functor for sheaves of modules over a sheaf of
commutative rings `R` that is induced by a point of a site. -/
noncomputable def sheafOfModulesFiber
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat)] (R : Sheaf J CommRingCat.{w}) :
    SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤
      ModuleCat.{w} (Φ.presheafFiber.obj R.obj :) :=
  SheafOfModules.forget _ ⋙ Φ.presheafOfModulesFiber R.obj

end CategoryTheory.GrothendieckTopology.Point
