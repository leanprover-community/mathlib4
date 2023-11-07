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

This file contains the definitioin of a solid abelian group: `CondensedAb.isSolid`. Solid abelian
groups were introduced in [scholze2019condensed], Definition 5.1.
-/

universe u

open CategoryTheory Limits Profinite Condensed

noncomputable section

/-- The free condensed abelian group on a finite set. -/
abbrev Condensed.finFree : FintypeCat.{u} ⥤ CondensedAb.{u} :=
  FintypeCat.toProfinite ⋙ profiniteToCondensed ⋙ freeAb.{u}

/-- The free condensed abelian group on a profinite space. -/
abbrev Condensed.profiniteFree : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
  profiniteToCondensed ⋙ freeAb.{u}

/-- The functor sending a profinite space `S` to the condensed abelian group `ℤ[S]^\solid`. -/
def profiniteSolid : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
  Ran.loc FintypeCat.toProfinite finFree

/-- The natural transformation `ℤ[S] ⟶ ℤ[S]^\solid`. -/
def profiniteSolidification : profiniteFree ⟶ profiniteSolid :=
  (Ran.equiv FintypeCat.toProfinite finFree profiniteFree).symm (NatTrans.id _)

/-- The predicate on condensed abelian groups describing the property of being solid. -/
def CondensedAb.isSolid (A : CondensedAb.{u}) : Prop :=
  ∀ X : Profinite.{u}, IsIso ((yoneda.obj A).map (profiniteSolidification.app X).op)
