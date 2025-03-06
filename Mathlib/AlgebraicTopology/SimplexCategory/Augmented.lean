/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/

import Mathlib.CategoryTheory.WithTerminal
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# The Augmented simplex category

This file defines the `AugmentedSimplexCategory` as the category obtained by adding an initial 
object to `SimplexCategory`. We furthermore show that functors `AugmentedSimplexCategory ⥤ C`
are equivalent to `SimplicialObject.Augmented C`.

## TODOs
* Define a monoidal structure on `AugmentedSimplexCategory`.
-/

universe u

open CategoryTheory

/-- The `AugmentedSimplexCategory` is the category obtained from `SimplexCategory` by adjoining an
initial object. -/
def AugmentedSimplexCategory := WithInitial SimplexCategory
  deriving SmallCategory

namespace AugmentedSimplexCategory

/-- The canonical inclusion from `SimplexCategory` to `AugmentedSimplexCategory`. -/
def inclusion : SimplexCategory ⥤ AugmentedSimplexCategory := WithInitial.incl

def toAugmentedSimplicialObject {C : Type*} [Category C] (F : AugmentedSimplexCategory ⥤ C) :
    CosimplicialObject.Augmented C :=
  CosimplicialObject.augment (inclusion ⋙ F) (F.obj .star) (F.map <| WithInitial.starInitial.to _)
    (fun i g₁ g₂ ↦ by 
      rw [Functor.comp_map, Functor.comp_map, ← F.map_comp, ← F.map_comp]
      congr 1)


end AugmentedSimplexCategory
