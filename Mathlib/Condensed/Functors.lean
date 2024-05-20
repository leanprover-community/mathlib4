/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Sites.Coherent.CoherentSheaves
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Condensed.Basic
import Mathlib.Topology.Category.Stonean.Basic

/-!
# Functors from categories of topological spaces to condensed sets

This file defines the various functors from categories of topological spaces to condensed sets.

## Main definitions

* `compHausToCondensed : CompHaus.{u} ⥤ CondensedSet.{u}` is essentially the yoneda presheaf
  functor. We also define `profiniteToCondensed` and `stoneanToCondensed`.

TODO (Dagur):

* Add the functor `TopCat.{u+1} ⥤ CondensedSet.{u}`. This is done in a draft PR which
  depends on the explicit sheaf condition for condensed sets.

* Define the analogues of `compHausToCondensed` for sheaves on `Profinite` and `Stonean` and provide
  the relevant isomorphisms with `profiniteToCondensed` and `stoneanToCondensed`.

* Define the functor `Type (u+1) ⥤ CondensedSet.{u}` which takes a set `X` to the presheaf given by
  mapping a compact Hausdorff space `S` to `LocallyConstant S X`, along with the isomorphism with
  the functor that goes through `TopCat.{u+1}`.

-/

universe u v

open CategoryTheory Limits

section Universes

/-- Increase the size of the target category of condensed sets. -/
def Condensed.ulift : Condensed.{u} (Type u) ⥤ CondensedSet.{u} :=
  sheafCompose (coherentTopology CompHaus) uliftFunctor.{u+1, u}

end Universes

section Topology

/-- The functor from `CompHaus` to `Condensed.{u} (Type u)` given by the Yoneda sheaf. -/
def compHausToCondensed' : CompHaus.{u} ⥤ Condensed.{u} (Type u) where
  obj S := {
    val := yoneda.obj S
    cond := by
      rw [isSheaf_iff_isSheaf_of_type]
      exact coherentTopology.isSheaf_yoneda_obj S }
  map f := ⟨yoneda.map f⟩

/-- The yoneda presheaf as an actual condensed set. -/
def compHausToCondensed : CompHaus.{u} ⥤ CondensedSet.{u} :=
  compHausToCondensed' ⋙ Condensed.ulift

/-- Dot notation for the value of `compHausToCondensed`. -/
abbrev CompHaus.toCondensed (S : CompHaus.{u}) : CondensedSet.{u} := compHausToCondensed.obj S

/-- The yoneda presheaf as a condensed set, restricted to profinite spaces. -/
def profiniteToCondensed : Profinite.{u} ⥤ CondensedSet.{u} :=
  profiniteToCompHaus ⋙ compHausToCondensed

/-- Dot notation for the value of `profiniteToCondensed`. -/
abbrev Profinite.toCondensed (S : Profinite.{u}) : CondensedSet.{u} := profiniteToCondensed.obj S

/-- The yoneda presheaf as a condensed set, restricted to Stonean spaces. -/
def stoneanToCondensed : Stonean.{u} ⥤ CondensedSet.{u} :=
  Stonean.toCompHaus ⋙ compHausToCondensed

/-- Dot notation for the value of `stoneanToCondensed`. -/
abbrev Stonean.toCondensed (S : Stonean.{u}) : CondensedSet.{u} := stoneanToCondensed.obj S

end Topology
