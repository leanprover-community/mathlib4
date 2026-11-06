/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.IsoCat

/-!
# ...

-/

@[expose] public section

namespace CategoryTheory.IsoCat

variable {C D : Type*} [Category* C] [Category* D] (e : IsoCat C D)

attribute [local simp] IsoCat.toEquivalence Arrow.eqToHom_left Arrow.eqToHom_right in
@[simps]
def arrow : IsoCat (Arrow C) (Arrow D) where
  functor := e.functor.mapArrow
  inverse := e.inverse.mapArrow
  unit_eq :=
    Functor.ext_of_iso ((Functor.mapArrowFunctor _ _).mapIso (e.toEquivalence.unitIso))
      (fun f ↦ congr((Functor.mapArrow $(e.unit_eq)).obj f))
  counit_eq :=
    Functor.ext_of_iso ((Functor.mapArrowFunctor _ _).mapIso (e.toEquivalence.counitIso))
      (fun f ↦ congr((Functor.mapArrow $(e.counit_eq)).obj f))

abbrev arrowEquiv : Arrow C ≃ Arrow D := e.arrow.objEquiv

end CategoryTheory.IsoCat
