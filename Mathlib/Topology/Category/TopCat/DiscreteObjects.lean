/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.CategoryTheory.Adjunction.DiscreteObjects
/-!

# Discrete objects in the category of topological spaces.

This file provides an example demonstrating that our categorical definition of a discrete object
(see `CategoryTheory/Adjunction/DiscreteObjects)` is sensible, by showing that in `TopCat`, it is
equivalent to being discrete as a topological space.
-/

open CategoryTheory Functor

namespace TopCat

instance : (forget TopCat).HasDiscreteObjects := HasDiscreteObjects.mk' _ adj₁

/-- A discrete topological space is in the essential image of the functor `TopCat.discrete`. -/
def isoDiscreteOfDiscreteTopology (X : TopCat) [DiscreteTopology X] : X ≅ discrete.obj X where
  hom := { toFun := id }
  inv := { toFun := id }

/-- A topological space is discrete in the categorical sense if and only if it is discret in the
topological sense. -/
lemma isDiscrete_iff_discreteTopology (X : TopCat) :
    IsDiscrete (forget _) X ↔ DiscreteTopology X := by
  rw [isDiscrete_iff_mem_essImage (adj := adj₁)]
  constructor
  · intro ⟨_, ⟨i⟩⟩
    exact DiscreteTopology.of_continuous_injective i.inv.continuous
      ((TopCat.mono_iff_injective _).mp inferInstance)
  · intro
    exact ⟨X, ⟨(isoDiscreteOfDiscreteTopology X).symm⟩⟩

end TopCat
