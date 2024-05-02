/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.KanExtension
import Mathlib.Condensed.Functors
import Mathlib.Condensed.Limits

/-!

# Solid modules

This file contains the definition of a solid `R`-module: `CondensedMod.isSolid R`. Solid modules
groups were introduced in [scholze2019condensed], Definition 5.1.

## Main definition

* `CondensedMod.IsSolid R`: the predicate on condensed abelian groups describing the property of
  being solid.

TODO (hard): prove that `((profiniteSolid ℤ).obj S).IsSolid` for `S : Profinite`.
TODO (slightly easier): prove that `((profiniteSolid 𝔽ₚ).obj S).IsSolid` for `S : Profinite`.
-/

universe u

variable (R : Type (u+1)) [Ring R]

open CategoryTheory Limits Profinite Condensed

noncomputable section

namespace Condensed

/-- The free condensed abelian group on a finite set. -/
abbrev finFree : FintypeCat.{u} ⥤ CondensedMod.{u} R :=
  FintypeCat.toProfinite ⋙ profiniteToCondensed ⋙ free R

/-- The free condensed abelian group on a profinite space. -/
abbrev profiniteFree : Profinite.{u} ⥤ CondensedMod.{u} R :=
  profiniteToCondensed ⋙ free R

/-- The functor sending a profinite space `S` to the condensed abelian group `R[S]^\solid`. -/
def profiniteSolid : Profinite.{u} ⥤ CondensedMod.{u} R :=
  Ran.loc FintypeCat.toProfinite (finFree R)

/-- The natural transformation `R[S] ⟶ R[S]^\solid`. -/
def profiniteSolidification : profiniteFree R ⟶ profiniteSolid.{u} R :=
  (Ran.equiv FintypeCat.toProfinite (finFree R) (profiniteFree R)).symm (NatTrans.id _)

end Condensed

/-- The predicate on condensed abelian groups describing the property of being solid. -/
class CondensedMod.IsSolid (A : CondensedMod.{u} R) : Prop where
  isIso_solidification_map : ∀ X : Profinite.{u}, IsIso ((yoneda.obj A).map
    ((profiniteSolidification R).app X).op)
