/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Pairs of simplicial sets

In this file, we define the category `SSetPair` of pairs of simplicial
sets, which consist of monomorphisms `i : X ⟶ Y` of simplicial sets.

-/

@[expose] public section

open Simplicial CategoryTheory

universe u

/-- The category `SSetPair` is the category of pairs of simplicial sets,
i.e. monomorphisms `i : X ⟶ Y`, see `SSetPair.of`. -/
abbrev SSetPair : Type (u + 1) := MorphismProperty.Arrow (.monomorphisms SSet.{u}) ⊤ ⊤

namespace SSetPair

instance (P : SSetPair.{u}) : Mono P.hom := P.prop

/-- Constructor for `SSetPair`. -/
abbrev of {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] : SSetPair.{u} :=
  MorphismProperty.Arrow.mk i (by assumption)

/-- The forget functor from `SSetPair` to the category `Arrow SSet`. -/
abbrev forget : SSetPair.{u} ⥤ Arrow SSet.{u} :=
  MorphismProperty.Arrow.forget _ _ _

/-- Constructor for morphisms in `SSetPair`. -/
abbrev homMk {X Y : SSetPair.{u}} (left : X.left ⟶ Y.left) (right : X.right ⟶ Y.right)
    (w : left ≫ Y.hom = X.hom ≫ right := by cat_disch) : X ⟶ Y :=
  MorphismProperty.Arrow.Hom.mk (Arrow.homMk left right w) (by simp) (by simp)

end SSetPair

/-- Given a subcomplex `A` of a simplical set `X`, this is the pair in `SSetPair`
corresponding to the inclusion `A.ι : (A : SSet) ⟶ X`. -/
abbrev SSet.Subcomplex.pair {X : SSet.{u}} (A : X.Subcomplex) : SSetPair.{u} := .of A.ι

/-- Given `X : SSet`, this is the functor `X.Subcomplex ⥤ SSetPair` which sends
`A : X.Subcomplex` to the pair corresponding to the inclusion `A.ι : (A : SSet) ⟶ X`. -/
@[implicit_reducible, simps]
def SSet.Subcomplex.toPairFunctor (X : SSet.{u}) : X.Subcomplex ⥤ SSetPair.{u} where
  obj := pair
  map f := SSetPair.homMk (SSet.Subcomplex.homOfLE f.le) (𝟙 _)

/-- If `X` is a simplicial set, this is the pair in `SSetPair` corresponding
to the inclusion of the empty subcomplex in `X`. -/
abbrev SSet.pair (X : SSet.{u}) : SSetPair.{u} := SSet.Subcomplex.pair (X := X) ⊥

/-- The functor `SSet ⥤ SSetPair` which sends `X : SSet` to the pair
corresponding to the inclusion of the empty subcomplex in `X`. -/
@[implicit_reducible, simps]
def SSet.toPairFunctor : SSet.{u} ⥤ SSetPair.{u} where
  obj := SSet.pair
  map f := SSetPair.homMk (Subcomplex.lift (Subcomplex.ι _ ≫ f) (fun _ _ h ↦ by simp at h)) f
