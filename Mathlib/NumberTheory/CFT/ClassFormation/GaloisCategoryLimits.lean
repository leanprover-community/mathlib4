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

variable [GaloisCategory C]

instance : HasFiniteColimits C where
  out _ _ _ :=
    Adjunction.hasColimitsOfShape_of_equivalence
      (functorToContAction (getFiberFunctor C))

instance (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] : PreservesFiniteColimits F := by
  change (PreservesFiniteColimits
    (functorToContAction F ⋙ ObjectProperty.ι _ ⋙ Action.forget _ _))
  infer_instance

instance : Balanced C where
  isIso_of_mono_of_epi f _ _ := by
    let F := getFiberFunctor C
    rw [← isIso_iff_of_reflects_iso _ (F ⋙ forget _)]
    apply isIso_of_mono_of_epi

end GaloisCategory

end CategoryTheory
