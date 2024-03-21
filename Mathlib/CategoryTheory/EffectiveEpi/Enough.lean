/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.EffectiveEpi.Basic
/-!

# Effectively enough objects in the image of a functor

We define the class `F.EffectivelyEnough` on a functor `F : C ⥤ D` which says that for every object
in `D`, there exists an effective epi to it from an object in the image of `F`.
-/

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

namespace Functor

structure EffectivePresentation (X : D) where
  p : C
  f : F.obj p ⟶ X
  effectiveEpi : EffectiveEpi f

class EffectivelyEnough : Prop where
  presentation : ∀ (X : D), Nonempty (F.EffectivePresentation X)

variable [F.EffectivelyEnough]

/--
`F.over X` provides an arbitrarily chosen object in the image of `F` equipped with an effective
epimorphism `F.π : F.over X ⟶ X`.
-/
noncomputable def over (X : D) : D :=
  F.obj (EffectivelyEnough.presentation (F := F) X).some.p

/--
The epimorphism `F.π : F.over X ⟶ X` from the arbitrarily chosen object in the image of `F`
over `X`.
-/
noncomputable def π (X : D) : over F X ⟶ X :=
  (EffectivelyEnough.presentation (F := F) X).some.f

instance (X : D) : EffectiveEpi (F.π X) :=
  (EffectivelyEnough.presentation X).some.effectiveEpi

def isEquivalenceEffectivePresentation (e : C ≌ D) (X : D) :
    EffectivePresentation e.functor X where
      p := e.inverse.obj X
      f := e.counit.app _
      effectiveEpi := inferInstance

instance [IsEquivalence F] : EffectivelyEnough F where
  presentation X := ⟨isEquivalenceEffectivePresentation F.asEquivalence X⟩

end Functor
