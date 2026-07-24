/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Relative simplicial homology


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

end SSetPair

/-- Given a subcomplex `A` of a simplical set `X`, this is the pair in `SSetPair`
corresponding to the inclusion `A.ι : (A : SSet) ⟶ X`. -/
abbrev SSet.Subcomplex.pair {X : SSet.{u}} (A : X.Subcomplex) : SSetPair.{u} := .of A.ι

/-- If `X` is a simplicial set, this is the pair in `SSetPair` corresponding
to the inclusion of the empty subcomplex in `X`. -/
abbrev SSet.pair (X : SSet.{u}) : SSetPair.{u} := SSet.Subcomplex.pair (X := X) ⊥
