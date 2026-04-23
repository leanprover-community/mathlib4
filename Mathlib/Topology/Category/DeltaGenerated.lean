/-
Copyright (c) 2024 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Compactness.DeltaGeneratedSpace
public import Mathlib.Topology.Convenient.Category

/-!
# Delta-generated topological spaces

The category of delta-generated spaces.

See https://ncatlab.org/nlab/show/Delta-generated+topological+space.

Adapted from `Mathlib/Topology/Category/CompactlyGenerated.lean`.

## TODO
* `DeltaGenerated` is Cartesian closed.
-/

@[expose] public section

universe u

open CategoryTheory

/-- The category of delta-generated topological spaces. -/
abbrev DeltaGenerated := GeneratedByTopCat.{u} (fun n ↦ (Fin n) → ℝ)

/-- The faithful (but not full) functor taking each topological space to its delta-generated
  coreflection. -/
abbrev TopCat.toDeltaGenerated : TopCat.{u} ⥤ DeltaGenerated.{u} :=
  TopCat.toGeneratedByTopCat

namespace DeltaGenerated

/-- Constructor for objects of the category `DeltaGenerated` -/
abbrev of (X : Type u) [TopologicalSpace X] [DeltaGeneratedSpace X] : DeltaGenerated.{u} :=
  GeneratedByTopCat.of X

/-- The forgetful functor `DeltaGenerated ⥤ TopCat` -/
abbrev deltaGeneratedToTop : DeltaGenerated.{u} ⥤ TopCat.{u} :=
  GeneratedByTopCat.toTopCat

/-- `deltaGeneratedToTop` is fully faithful. -/
def fullyFaithfulDeltaGeneratedToTop : deltaGeneratedToTop.{u}.FullyFaithful :=
  GeneratedByTopCat.fullyFaithfulToTopCat _

@[deprecated (since := "2026-04-23")] alias topToDeltaGenerated := TopCat.toDeltaGenerated

/-- The adjunction between the forgetful functor `DeltaGenerated ⥤ TopCat` and its coreflector. -/
abbrev coreflectorAdjunction : deltaGeneratedToTop ⊣ TopCat.toDeltaGenerated :=
  GeneratedByTopCat.adj

end DeltaGenerated
