/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.KanExtension
import Mathlib.Condensed.Adjunctions
import Mathlib.Condensed.Functors
import Mathlib.Condensed.Limits

/-!

# Solid abelian groups

This file contains the definition of a solid abelian group: `CondensedAb.isSolid`. Solid abelian
groups were introduced in [scholze2019condensed], Definition 5.1.

## Main definition

* `CondensedAb.IsSolid`: the predicate on condensed abelian groups describing the property of being
  solid.

TODO (hard): prove that `(profiniteSolid.obj S).IsSolid` for `S : Profinite`.
-/

universe u

open CategoryTheory Limits Profinite Condensed

noncomputable section

namespace Condensed

/-- The free condensed abelian group on a finite set. -/
abbrev finFree : FintypeCat.{u} ⥤ CondensedAb.{u} :=
  FintypeCat.toProfinite ⋙ profiniteToCondensed ⋙ freeAb.{u}

/-- The free condensed abelian group on a profinite space. -/
abbrev profiniteFree : Profinite.{u} ⥤ CondensedAb.{u} :=
  profiniteToCondensed ⋙ freeAb.{u}

/-- The functor sending a profinite space `S` to the condensed abelian group `ℤ[S]^\solid`. -/
def profiniteSolid : Profinite.{u} ⥤ CondensedAb.{u} :=
  Ran.loc FintypeCat.toProfinite finFree

/-- The natural transformation `ℤ[S] ⟶ ℤ[S]^\solid`. -/
def profiniteSolidification : profiniteFree ⟶ profiniteSolid :=
  (Ran.equiv FintypeCat.toProfinite finFree profiniteFree).symm (NatTrans.id _)

end Condensed

/-- The predicate on condensed abelian groups describing the property of being solid. -/
class CondensedAb.IsSolid (A : CondensedAb.{u}) : Prop where
  isIso_solidification_map : ∀ X : Profinite.{u}, IsIso ((yoneda.obj A).map
    (profiniteSolidification.app X).op)
