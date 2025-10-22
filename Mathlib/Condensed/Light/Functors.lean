/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Light.CartesianClosed
import Mathlib.Condensed.Light.TopCatAdjunction
import Mathlib.Topology.Category.LightProfinite.Cartesian

/-!
# Functors from categories of topological spaces to light condensed sets

This file defines the embedding of the test objects (light profinite sets) into light condensed
sets.

## Main definitions

* `lightProfiniteToLightCondSet : LightProfinite.{u} ⥤ LightCondSet.{u}`
  is the yoneda sheaf functor.

-/

universe u v

open CategoryTheory Limits Functor

/-- The functor from `LightProfinite.{u}` to `LightCondSet.{u}` given by the Yoneda sheaf. -/
def lightProfiniteToLightCondSet : LightProfinite.{u} ⥤ LightCondSet.{u} :=
  (coherentTopology LightProfinite).yoneda

/-- Dot notation for the value of `lightProfiniteToLightCondSet`. -/
abbrev LightProfinite.toCondensed (S : LightProfinite.{u}) : LightCondSet.{u} :=
  lightProfiniteToLightCondSet.obj S

/-- `lightProfiniteToLightCondSet` is fully faithful. -/
abbrev lightProfiniteToLightCondSetFullyFaithful :
    lightProfiniteToLightCondSet.FullyFaithful :=
  (coherentTopology LightProfinite).yonedaFullyFaithful

instance : lightProfiniteToLightCondSet.Full :=
  inferInstanceAs ((coherentTopology LightProfinite).yoneda).Full

instance : lightProfiniteToLightCondSet.Faithful :=
  inferInstanceAs ((coherentTopology LightProfinite).yoneda).Faithful

/--
The functor from `LightProfinite` to `LightCondSet` factors through `TopCat`.
-/
@[simps!]
noncomputable def lightProfiniteToLightCondSetIsoTopCatToLightCondSet :
    lightProfiniteToLightCondSet.{u} ≅ LightProfinite.toTopCat.{u} ⋙ topCatToLightCondSet.{u} :=
  NatIso.ofComponents fun X ↦ FullyFaithful.preimageIso (fullyFaithfulSheafToPresheaf _ _) <|
    NatIso.ofComponents fun S ↦ {
      hom f := { toFun := f.hom }
      inv f := TopCat.ofHom f }

/--
The functor from light profinite sets to condensed sets preserves countable limits.
-/
instance {J : Type} [SmallCategory J] [CountableCategory J] : PreservesLimitsOfShape J
    lightProfiniteToLightCondSet.{u} :=
  haveI : Functor.IsRightAdjoint topCatToLightCondSet.{u} :=
    LightCondSet.topCatAdjunction.isRightAdjoint
  haveI : PreservesLimitsOfShape J LightProfinite.toTopCat.{u} :=
    inferInstanceAs (PreservesLimitsOfShape J (lightToProfinite ⋙ Profinite.toTopCat))
  preservesLimitsOfShape_of_natIso lightProfiniteToLightCondSetIsoTopCatToLightCondSet.symm

/--
The functor from light profinite sets to condensed sets preserves finite limits.
-/
instance : PreservesFiniteLimits lightProfiniteToLightCondSet.{u} where
  preservesFiniteLimits _ := inferInstance

/--
The functor from light profinite sets to condensed sets is monoidal with respect to the cartesian
monoidal structure.
-/
noncomputable instance : lightProfiniteToLightCondSet.Monoidal := by
  have : Nonempty lightProfiniteToLightCondSet.Monoidal := by
    rw [Functor.Monoidal.nonempty_monoidal_iff_preservesFiniteProducts]
    infer_instance
  exact this.some
