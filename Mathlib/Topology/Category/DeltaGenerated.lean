/-
Copyright (c) 2024 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Topology.Compactness.DeltaGeneratedSpace
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Adjunction.Reflective

/-!
# Delta-generated topological spaces

The category of delta-generated spaces.

See https://ncatlab.org/nlab/show/Delta-generated+topological+space.

Adapted from `Mathlib.Topology.Category.CompactlyGenerated`.

## TODO
* `DeltaGenerated` has all limits and colimits.
* `DeltaGenerated` is a coreflective subcategory of `CompactlyGenerated`.
* `DeltaGenerated` is cartesian-closed.
-/

universe u

open CategoryTheory

/-- The type of delta-generated topological spaces. -/
structure DeltaGenerated where
  toTop : TopCat.{u}
  deltaGenerated : DeltaGeneratedSpace toTop := by infer_instance

namespace DeltaGenerated

instance : CoeSort DeltaGenerated Type* :=
  ⟨fun X => X.toTop⟩

attribute [instance] deltaGenerated

instance : LargeCategory.{u} DeltaGenerated.{u} :=
  InducedCategory.category toTop

instance : ConcreteCategory.{u} DeltaGenerated.{u} :=
  InducedCategory.concreteCategory _

/-- Constructor for objects of the category `DeltaGenerated`. -/
def of (X : Type u) [TopologicalSpace X] [DeltaGeneratedSpace X] : DeltaGenerated.{u} where
  toTop := TopCat.of X
  deltaGenerated := ‹_›

/-- The forgetful functor `DeltaGenerated ⥤ TopCat`. -/
@[simps!]
def deltaGeneratedToTop : DeltaGenerated.{u} ⥤ TopCat.{u} :=
  inducedFunctor _

-- TODO: show that this is fully faithful
/-- The functor taking each topological space to its delta-generification. -/
@[simps!]
def topToDeltaGenerated : TopCat.{u} ⥤ DeltaGenerated.{u} where
  obj X := of (DeltaGeneratedSpace.of X)
  map {_ Y} f := ⟨f,(continuous_to_deltaGenerated (Y := Y)).mpr <|
    continuous_le_dom deltaGenerated_le f.continuous⟩

/-- The adjunction between the forgetful functor `DeltaGenerated ⥤ TopCat` and
  its coreflector.
  TODO: conclude that `DeltaGenerated` is coreflective in `TopCat`. Requires mathlib bump. -/
def coreflectorAdjunction : deltaGeneratedToTop ⊣ topToDeltaGenerated :=
  Adjunction.mkOfUnitCounit {
    unit := {
      app := fun X => ⟨id,continuous_iff_coinduced_le.mpr (eq_deltaGenerated (X := X)).le⟩ }
    counit := {
      app := fun X => ⟨DeltaGeneratedSpace.counit,DeltaGeneratedSpace.continuous_counit⟩ }}

end DeltaGenerated
