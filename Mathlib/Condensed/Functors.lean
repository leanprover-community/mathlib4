/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Sites.Coherent.CoherentSheaves
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Condensed.Basic
public import Mathlib.Topology.Category.Stonean.Basic

/-!
# Functors from categories of topological spaces to condensed sets

This file defines the embedding of the test objects (compact Hausdorff spaces) into condensed
sets.

## Main definitions

* `compHausToCondensed : CompHaus.{u} ⥤ CondensedSet.{u}` is essentially the yoneda presheaf
  functor. We also define `profiniteToCondensed` and `stoneanToCondensed`.

-/

@[expose] public section

universe u v

open CategoryTheory Limits

section Universes

/-- Increase the size of the target category of condensed sets. -/
def Condensed.ulift : Condensed.{u} (Type u) ⥤ CondensedSet.{u} :=
  sheafCompose (coherentTopology CompHaus) uliftFunctor.{u + 1, u}

instance : Condensed.ulift.Full := show (sheafCompose _ _).Full from inferInstance

instance : Condensed.ulift.Faithful := show (sheafCompose _ _).Faithful from inferInstance

end Universes

section Topology

/-- The functor from `CompHaus` to `Condensed.{u} (Type u)` given by the Yoneda sheaf. -/
def compHausToCondensed' : CompHaus.{u} ⥤ Condensed.{u} (Type u) :=
  (coherentTopology CompHaus).yoneda

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

instance : compHausToCondensed'.Full :=
  inferInstanceAs ((coherentTopology CompHaus).yoneda).Full

instance : compHausToCondensed'.Faithful :=
  inferInstanceAs ((coherentTopology CompHaus).yoneda).Faithful

instance : compHausToCondensed.Full := inferInstanceAs (_ ⋙ _).Full

instance : compHausToCondensed.Faithful := inferInstanceAs (_ ⋙ _).Faithful

end Topology
