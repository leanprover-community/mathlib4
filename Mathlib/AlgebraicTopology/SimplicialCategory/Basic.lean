/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Simplicial categories

A simplicial category is a category `C` that is enriched over the
category of simplicial sets in such a way that morphisms in
`C` identify to the `0`-simplices of the enriched hom.

## TODO

* construct a simplicial category structure on simplicial objects, so
  that it applies in particular to simplicial sets
* obtain the adjunction property `(K ⊗ X ⟶ Y) ≃ (K ⟶ sHom X Y)` when `K`, `X`, and `Y`
  are simplicial sets
* develop the notion of "simplicial tensor" `K ⊗ₛ X : C` with `K : SSet` and `X : C`
  an object in a simplicial category `C`
* define the notion of path between `0`-simplices of simplicial sets
* deduce the notion of homotopy between morphisms in a simplicial category
* obtain that homotopies in simplicial categories can be interpreted as given
  by morphisms `Δ[1] ⊗ X ⟶ Y`.

## References
* [Daniel G. Quillen, *Homotopical algebra*, II §1][quillen-1967]

-/

@[expose] public section

universe v u

open CategoryTheory Category Simplicial MonoidalCategory

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- A simplicial category is a category `C` that is enriched over the
category of simplicial sets in such a way that morphisms in
`C` identify to the `0`-simplices of the enriched hom. -/
abbrev SimplicialCategory := EnrichedOrdinaryCategory SSet.{v} C

namespace SimplicialCategory

variable [SimplicialCategory C]

variable {C}

/-- Abbreviation for the enriched hom of a simplicial category. -/
abbrev sHom (K L : C) : SSet.{v} := K ⟶[SSet] L

/-- Abbreviation for the enriched composition in a simplicial category. -/
abbrev sHomComp (K L M : C) : sHom K L ⊗ sHom L M ⟶ sHom K M := eComp SSet K L M

/-- The bijection `(K ⟶ L) ≃ sHom K L _⦋0⦌` for all objects `K` and `L`
in a simplicial category. -/
def homEquiv' (K L : C) : (K ⟶ L) ≃ sHom K L _⦋0⦌ :=
  (eHomEquiv SSet).trans (sHom K L).unitHomEquiv

variable (C) in
/-- The bifunctor `Cᵒᵖ ⥤ C ⥤ SSet.{v}` which sends `K : Cᵒᵖ` and `L : C` to `sHom K.unop L`. -/
noncomputable abbrev sHomFunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v} := eHomFunctor _ _

end SimplicialCategory

end CategoryTheory
