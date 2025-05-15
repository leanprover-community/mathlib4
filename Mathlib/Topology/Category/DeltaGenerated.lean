/-
Copyright (c) 2024 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Compactness.DeltaGeneratedSpace

/-!
# Delta-generated topological spaces

The category of delta-generated spaces.

See https://ncatlab.org/nlab/show/Delta-generated+topological+space.

Adapted from `Mathlib/Topology/Category/CompactlyGenerated.lean`.

## TODO
* `DeltaGenerated` is cartesian-closed.
-/

universe u

open CategoryTheory

/-- The type of delta-generated topological spaces. -/
structure DeltaGenerated where
  /-- the underlying topological space -/
  toTop : TopCat.{u}
  /-- The underlying topological space is delta-generated. -/
  deltaGenerated : DeltaGeneratedSpace toTop := by infer_instance

namespace DeltaGenerated

instance : CoeSort DeltaGenerated Type* :=
  ⟨fun X ↦ X.toTop⟩

attribute [instance] deltaGenerated

instance : LargeCategory.{u} DeltaGenerated.{u} :=
  InducedCategory.category toTop

instance : ConcreteCategory.{u} DeltaGenerated.{u} (C(·, ·)) :=
  InducedCategory.concreteCategory toTop

/-- Constructor for objects of the category `DeltaGenerated` -/
abbrev of (X : Type u) [TopologicalSpace X] [DeltaGeneratedSpace X] : DeltaGenerated.{u} where
  toTop := TopCat.of X
  deltaGenerated := ‹_›

/-- The forgetful functor `DeltaGenerated ⥤ TopCat` -/
@[simps!]
def deltaGeneratedToTop : DeltaGenerated.{u} ⥤ TopCat.{u} :=
  inducedFunctor _

/-- `deltaGeneratedToTop` is fully faithful. -/
def fullyFaithfulDeltaGeneratedToTop : deltaGeneratedToTop.{u}.FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : deltaGeneratedToTop.{u}.Full := fullyFaithfulDeltaGeneratedToTop.full

instance : deltaGeneratedToTop.{u}.Faithful := fullyFaithfulDeltaGeneratedToTop.faithful

/-- The faithful (but not full) functor taking each topological space to its delta-generated
  coreflection. -/
@[simps!]
def topToDeltaGenerated : TopCat.{u} ⥤ DeltaGenerated.{u} where
  obj X := of (DeltaGeneratedSpace.of X)
  map {_ Y} f := TopCat.ofHom ⟨f, (continuous_to_deltaGenerated (Y := Y)).mpr <|
    continuous_le_dom deltaGenerated_le f.hom.continuous⟩

instance : topToDeltaGenerated.{u}.Faithful :=
  ⟨fun h ↦ by ext x; exact CategoryTheory.congr_fun h x⟩

/-- The adjunction between the forgetful functor `DeltaGenerated ⥤ TopCat` and its coreflector. -/
def coreflectorAdjunction : deltaGeneratedToTop ⊣ topToDeltaGenerated :=
  Adjunction.mkOfUnitCounit {
    unit := {
      app X := TopCat.ofHom ⟨id, continuous_iff_coinduced_le.mpr (eq_deltaGenerated (X := X)).le⟩ }
    counit := {
      app X := TopCat.ofHom ⟨DeltaGeneratedSpace.counit, DeltaGeneratedSpace.continuous_counit⟩ }}

/-- The category of delta-generated spaces is coreflective in the category of topological spaces. -/
instance deltaGeneratedToTop.coreflective : Coreflective deltaGeneratedToTop where
  R := topToDeltaGenerated
  adj := coreflectorAdjunction

noncomputable instance deltaGeneratedToTop.createsColimits : CreatesColimits deltaGeneratedToTop :=
  comonadicCreatesColimits deltaGeneratedToTop

instance hasLimits : Limits.HasLimits DeltaGenerated :=
  hasLimits_of_coreflective deltaGeneratedToTop

instance hasColimits : Limits.HasColimits DeltaGenerated :=
  hasColimits_of_hasColimits_createsColimits deltaGeneratedToTop

end DeltaGenerated
