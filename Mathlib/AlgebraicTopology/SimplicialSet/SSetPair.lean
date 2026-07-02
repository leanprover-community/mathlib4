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

abbrev SSetPair : Type (u + 1) := MorphismProperty.Arrow (.monomorphisms SSet.{u}) ⊤ ⊤

abbrev SSetPair.of {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] : SSetPair.{u} :=
  MorphismProperty.Arrow.mk i (by assumption)

abbrev SSet.Subcomplex.pair {X : SSet.{u}} (A : X.Subcomplex) : SSetPair.{u} := .of A.ι

abbrev SSet.pair (X : SSet.{u}) : SSetPair.{u} := SSet.Subcomplex.pair (X := X) ⊥

abbrev SSetPair.forget : SSetPair.{u} ⥤ Arrow SSet.{u} :=
  MorphismProperty.Arrow.forget _ _ _
