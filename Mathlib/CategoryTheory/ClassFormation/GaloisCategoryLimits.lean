/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Galois.ContAction
public import Mathlib.CategoryTheory.Galois.Equivalence

/-!
# Galois categories have finite limits

-/

-- to be moved to `CategoryTheory/Galois`

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open PreGaloisCategory

namespace GaloisCategory

variable (F : C ⥤ FintypeCat.{w}) [GaloisCategory C] [FiberFunctor F]

instance : HasFiniteColimits C where
  out _ _ _ :=
    Adjunction.hasColimitsOfShape_of_equivalence
      (functorToContAction (getFiberFunctor C))

instance : PreservesFiniteColimits F := by
  change (PreservesFiniteColimits
    (functorToContAction F ⋙ ObjectProperty.ι _ ⋙ Action.forget _ _))
  infer_instance

end GaloisCategory

end CategoryTheory
