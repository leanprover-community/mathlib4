/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# Properties of functors

TODO: reconcile this with `CategoryTheory.Limits.ExactFunctor`
-/

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category C] [Category D]

namespace ObjectProperty

def exactFunctor : ObjectProperty (C ⥤ D) :=
  fun F ↦ PreservesFiniteLimits F ∧ PreservesFiniteColimits F

variable {F : C ⥤ D}

lemma exactFunctor.preservesFiniteLimits (hF : exactFunctor F) :
    PreservesFiniteLimits F := hF.1

lemma exactFunctor.preservesFiniteColimits (hF : exactFunctor F) :
    PreservesFiniteColimits F := hF.2

instance : (exactFunctor (C := C) (D := D)).IsClosedUnderIsomorphisms where
  of_iso e := by
    rintro ⟨_, _⟩
    exact ⟨preservesFiniteLimits_of_natIso e,
      preservesFiniteColimits_of_natIso e⟩

end ObjectProperty

end CategoryTheory
