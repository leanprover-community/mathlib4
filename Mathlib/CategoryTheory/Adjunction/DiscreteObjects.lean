/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Unique
/-!

# Discrete objects

This file defines the property of a functor of having discrete objects. This simply means that it
has a fully faithful left adjoint.

We also define a predicate `IsDiscrete` on objects saying that the counit of the adjunction applied
to `X` is an isomorphism. This is equivalent to being in the essential image of the left adjoint
(see `isDiscrete_iff_mem_essImage`).
-/

open CategoryTheory

variable {C D : Type*} [Category C] [Category D] (U : C ⥤ D)

namespace CategoryTheory.Functor

/-- A functor is said to have discrete objects if it has a fully faithful left adjoint. -/
class HasDiscreteObjects : Prop where
  isRightAdjoint : IsRightAdjoint U := by infer_instance
  faithful : (leftAdjoint U).Faithful := by infer_instance
  full : (leftAdjoint U).Full := by infer_instance

attribute [instance] HasDiscreteObjects.isRightAdjoint
attribute [instance] HasDiscreteObjects.faithful
attribute [instance] HasDiscreteObjects.full

variable {U} in
/-- The property of having discrete objects is invariant under natural isomorphism. -/
lemma hasDiscreteObjectsOfNatIso {U' : C ⥤ D} (i : U ≅ U') [HasDiscreteObjects U] :
    HasDiscreteObjects U' where
  isRightAdjoint := ⟨leftAdjoint U,
    ⟨Adjunction.ofNatIsoRight (Adjunction.ofIsRightAdjoint U) i⟩⟩
  faithful := Faithful.of_iso (leftAdjointCongr i)
  full := Full.of_iso (leftAdjointCongr i)

variable {U} in
lemma hasDiscreteObjects_iff_of_natIso {U' : C ⥤ D} (i : U ≅ U') :
    HasDiscreteObjects U ↔ HasDiscreteObjects U' :=
  ⟨fun _ ↦ hasDiscreteObjectsOfNatIso i,  fun _ ↦ hasDiscreteObjectsOfNatIso i.symm⟩

/-- A constructor for `HasDiscreteObjects` given an explicit adjunction. -/
lemma HasDiscreteObjects.mk' {L : D ⥤ C} (adj : L ⊣ U) [L.Full] [L.Faithful] :
    HasDiscreteObjects U where
  isRightAdjoint := adj.isRightAdjoint
  faithful := Faithful.of_iso (adj.leftAdjointCongr)
  full := Full.of_iso (adj.leftAdjointCongr)

end Functor

/--
Given a functor `U` which has discrete objects, `IsDiscrete U X` is the predicate on objects saying
that the counit of the adjunction applied to `X` is an isomorphism.

In fact, it is enough that the object `X` is in the essential image of the left adjoint, see e.g.
`isDiscrete_iff_mem_essImage`.
-/
class IsDiscrete [U.HasDiscreteObjects] (X : C) : Prop where
  isIso_counit : IsIso <| (Adjunction.ofIsRightAdjoint U).counit.app X := by infer_instance

attribute [instance] IsDiscrete.isIso_counit

open Adjunction

theorem isDiscrete_of_iso [U.HasDiscreteObjects] {X : C} {Y : D}
    (i : X ≅ U.leftAdjoint.obj Y) : IsDiscrete U X where
  isIso_counit := isIso_counit_app_of_iso _ i

theorem isDiscrete_iff_mem_essImage {L : D ⥤ C} (adj : L ⊣ U) [L.Full] [L.Faithful] (X : C) :
    haveI : U.HasDiscreteObjects := Functor.HasDiscreteObjects.mk' _ adj
    IsDiscrete U X ↔ X ∈ L.essImage := by
  haveI := Functor.HasDiscreteObjects.mk' _ adj
  refine ⟨fun h ↦ ⟨U.obj X, ⟨?_⟩⟩, fun ⟨Y, ⟨i⟩⟩ ↦ ?_⟩
  · refine adj.leftAdjointCongr.app _ ≪≫
      asIso ((Adjunction.ofIsRightAdjoint _).counit.app _)
  · exact isDiscrete_of_iso U (i.symm ≪≫ adj.leftAdjointCongr.app _)

theorem isDiscrete_iff_isIso_counit_app {L : D ⥤ C} (adj : L ⊣ U) [L.Full] [L.Faithful] (X : C) :
    haveI : U.HasDiscreteObjects := Functor.HasDiscreteObjects.mk' _ adj
    IsDiscrete U X ↔ IsIso (adj.counit.app X) := by
  rw [isIso_counit_app_iff_mem_essImage]
  exact isDiscrete_iff_mem_essImage _ adj _

theorem isDiscrete_congr [U.HasDiscreteObjects] {X Y : C} (i : X ≅ Y) [IsDiscrete U X] :
    IsDiscrete U Y :=
  isDiscrete_of_iso U (i.symm ≪≫ (asIso ((Adjunction.ofIsRightAdjoint U).counit.app X)).symm)

theorem isDiscrete_of_natIso [U.HasDiscreteObjects] (U' : C ⥤ D) (i : U ≅ U') (X : C)
    [IsDiscrete U X] :
    haveI : U'.HasDiscreteObjects := Functor.hasDiscreteObjectsOfNatIso i
    IsDiscrete U' X :=
  haveI : U'.HasDiscreteObjects := Functor.hasDiscreteObjectsOfNatIso i
  isDiscrete_of_iso U' ((asIso ((Adjunction.ofIsRightAdjoint U).counit.app X)).symm ≪≫
    ((Functor.leftAdjointCongr i)).app _)

end CategoryTheory
