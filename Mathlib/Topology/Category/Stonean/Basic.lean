/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.CategoryTheory.Sites.Coherent
import Mathlib.Topology.Category.CompHaus.Projective
import Mathlib.Topology.Category.Profinite.Basic
/-!
# Extremally disconnected sets

This file develops some of the basic theory of extremally disconnected sets.

## Overview

This file defines the type `Stonean` of all extremally (note: not "extremely"!)
disconnected compact Hausdorff spaces, gives it the structure of a large category,
and proves some basic observations about this category and various functors from it.

The Lean implementation: a term of type `Stonean` is a pair, considering of
a term of type `CompHaus` (i.e. a compact Hausdorff topological space) plus
a proof that the space is extremally disconnected.
This is equivalent to the assertion that the term is projective in `CompHaus`,
in the sense of category theory (i.e., such that morphisms out of the object
can be lifted along epimorphisms).

## Main definitions

* `Stonean` : the category of extremally disconnected compact Hausdorff spaces.
* `Stonean.toCompHaus` : the forgetful functor `Stonean ⥤ CompHaus` from Stonean
  spaces to compact Hausdorff spaces
* `Stonean.toProfinite` : the functor from Stonean spaces to profinite spaces.

-/
universe u

open CategoryTheory

/-- `Stonean` is the category of extremally disconnected compact Hausdorff spaces. -/
structure Stonean where
  /-- The underlying compact Hausdorff space of a Stonean space. -/
  compHaus : CompHaus.{u}
  /-- A Stonean space is extremally disconnected -/
  [extrDisc : ExtremallyDisconnected compHaus]

namespace CompHaus

/-- `Projective` implies `ExtremallyDisconnected`. -/
instance (X : CompHaus.{u}) [Projective X] : ExtremallyDisconnected X := by
  apply CompactT2.Projective.extremallyDisconnected
  intro A B _ _ _ _ _ _ f g hf hg hsurj
  have : CompactSpace (TopCat.of A) := by assumption
  have : T2Space (TopCat.of A) := by assumption
  have : CompactSpace (TopCat.of B) := by assumption
  have : T2Space (TopCat.of B) := by assumption
  let A' : CompHaus := ⟨TopCat.of A⟩
  let B' : CompHaus := ⟨TopCat.of B⟩
  let f' : X ⟶ B' := ⟨f, hf⟩
  let g' : A' ⟶ B' := ⟨g,hg⟩
  have : Epi g' := by
    rw [CompHaus.epi_iff_surjective]
    assumption
  obtain ⟨h,hh⟩ := Projective.factors f' g'
  refine ⟨h,h.2,?_⟩
  ext t
  apply_fun (fun e => e t) at hh
  exact hh

/-- `Projective` implies `Stonean`. -/
@[simps!]
def toStonean (X : CompHaus.{u}) [Projective X] :
    Stonean where
  compHaus := X

end CompHaus

namespace Stonean

/-- Stonean spaces form a large category. -/
instance : LargeCategory Stonean.{u} :=
  show Category (InducedCategory CompHaus (·.compHaus)) from inferInstance

/-- The (forgetful) functor from Stonean spaces to compact Hausdorff spaces. -/
@[simps!]
def toCompHaus : Stonean.{u} ⥤ CompHaus.{u} :=
  inducedFunctor _

/-- Construct a term of `Stonean` from a type endowed with the structure of a
compact, Hausdorff and extremally disconnected topological space.
-/
def of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ExtremallyDisconnected X] : Stonean :=
  ⟨⟨⟨X, inferInstance⟩⟩⟩

/-- The forgetful functor `Stonean ⥤ CompHaus` is full. -/
instance : Full toCompHaus where
  preimage := fun f => f


/-- The forgetful functor `Stonean ⥤ CompHaus` is faithful. -/
instance : Faithful toCompHaus := {}

/-- Stonean spaces are a concrete category. -/
instance : ConcreteCategory Stonean where
  forget := toCompHaus ⋙ forget _

instance : CoeSort Stonean.{u} (Type u) := ConcreteCategory.hasCoeToSort _
instance {X Y : Stonean.{u}} : FunLike (X ⟶ Y) X (fun _ => Y) := ConcreteCategory.funLike

/-- Stonean spaces are topological spaces. -/
instance instTopologicalSpace (X : Stonean.{u}) : TopologicalSpace X :=
  show TopologicalSpace X.compHaus from inferInstance

/-- Stonean spaces are compact. -/
instance (X : Stonean.{u}) : CompactSpace X :=
  show CompactSpace X.compHaus from inferInstance

/-- Stonean spaces are Hausdorff. -/
instance (X : Stonean.{u}) : T2Space X :=
  show T2Space X.compHaus from inferInstance

instance (X : Stonean.{u}) : ExtremallyDisconnected X :=
  X.2

/-- The functor from Stonean spaces to profinite spaces. -/
@[simps]
def toProfinite : Stonean.{u} ⥤ Profinite.{u} where
  obj X :=
  { toCompHaus := X.compHaus,
    IsTotallyDisconnected := show TotallyDisconnectedSpace X from inferInstance }
  map f := f

/-- The functor from Stonean spaces to profinite spaces is full. -/
instance : Full toProfinite where
  preimage f := f

/-- The functor from Stonean spaces to profinite spaces is faithful. -/
instance : Faithful toProfinite := {}

/-- The functor from Stonean spaces to compact Hausdorff spaces
    factors through profinite spaces. -/
example : toProfinite ⋙ profiniteToCompHaus = toCompHaus :=
  rfl

end Stonean
