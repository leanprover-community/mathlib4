/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.CoherentSheaves
import Mathlib.Condensed.Light.Basic

/-!
# Functors from categories of topological spaces to light condensed sets

This file defines the embedding of the test objects (light profinite sets) into light condensed
sets.

## Main definitions

* `lightProfiniteToLightCondSet : LightProfinite.{u} ⥤ LightCondSet.{u}` 
  is the yoneda presheaf functor.

TODO (Dagur):

* Add the functor `TopCat.{u} ⥤ LightCondSet.{u}`.

* Define the functor `Type u ⥤ LightCondSet.{u}` which takes a set `X` to the presheaf given by
  mapping a light profinite space `S` to `LocallyConstant S X`, along with the isomorphism with
  the functor that goes through `TopCat.{u+1}`.

-/

universe u v

open CategoryTheory Limits

/-- The functor from `LightProfinite.{u}` to `LightCondSet.{u}` given by the Yoneda sheaf. -/
def lightProfiniteToLightCondSet : LightProfinite.{u} ⥤ LightCondSet.{u} :=
  (coherentTopology.subcanonical LightProfinite).yoneda

/-- Dot notation for the value of `lightProfiniteToLightCondSet`. -/
abbrev LightProfinite.toCondensed (S : LightProfinite.{u}) : LightCondSet.{u} :=
  lightProfiniteToLightCondSet.obj S

/-- `lightProfiniteToLightCondSet` is fully faithful. -/
abbrev lightProfiniteToLightCondSetFullyFaithful :
    lightProfiniteToLightCondSet.FullyFaithful :=
  Sheaf.Subcanonical.yonedaFullyFaithful _

instance : lightProfiniteToLightCondSet.Full :=
  show (Sheaf.Subcanonical.yoneda _).Full from inferInstance

instance : lightProfiniteToLightCondSet.Faithful :=
  show (Sheaf.Subcanonical.yoneda _).Faithful from inferInstance
