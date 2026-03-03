/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Colimits in categories of sheaves of modules

In this file, we show that colimits of shape `J` exist in a category
of sheaves of modules if it exists in the corresponding category
of presheaves of modules.

-/

@[expose] public section

universe w' w v v' u' u

namespace SheafOfModules

open CategoryTheory Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

variable (R : Sheaf J RingCat.{u}) [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] (K : Type w) [Category.{w'} K]

instance [HasColimitsOfShape K (PresheafOfModules.{v} R.val)] :
    HasColimitsOfShape K (SheafOfModules.{v} R) where
  has_colimit F := by
    let e : F ≅ (F ⋙ forget R) ⋙ PresheafOfModules.sheafification (𝟙 R.val) :=
      Functor.isoWhiskerLeft F
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.val)).counit).symm
    exact hasColimit_of_iso e

instance [HasColimitsOfSize.{w', w} (PresheafOfModules.{v} R.val)] :
    HasColimitsOfSize.{w', w} (SheafOfModules.{v} R) where

end SheafOfModules
