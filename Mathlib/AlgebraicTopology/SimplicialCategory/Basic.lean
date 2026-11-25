/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Simplicial categories

A simplicial category is a category `C` that is enriched over the
category of simplicial sets in such a way that morphisms in
`C` identify to the `0`-simplices of the enriched hom.

## TODO

* develop the notion of "simplicial tensor" `K ⊗ₛ X : C` with `K : SSet` and `X : C`
  an object in a simplicial category `C`
* define the notion of path between `0`-simplices of simplicial sets
* deduce the notion of homotopy between morphisms in a simplicial category
* obtain that homotopies in simplicial categories can be interpreted as given
  by morphisms `Δ[1] ⊗ X ⟶ Y`.

## References

* [Daniel G. Quillen, *Homotopical algebra*, II §1][Quillen1967]
-/

@[expose] public section

universe v u

open CategoryTheory Category MonoidalCategory

open scoped Simplicial

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

variable {m : SimplexCategoryᵒᵖ}

/-- The identity `m`-simplex of `sHom K K`. -/
def idS (m : SimplexCategoryᵒᵖ) (K : C) : (sHom K K).obj m :=
  (eId SSet K).app m PUnit.unit

/-- Composition of `m`-simplices of the simplicial homs. -/
def comp {K L M : C} (s : (sHom K L).obj m) (t : (sHom L M).obj m) :
    (sHom K M).obj m :=
  (sHomComp K L M).app m (s, t)

@[simp]
lemma idS_comp {K L : C} (s : (sHom K L).obj m) :
    comp (idS m K) s = s :=
  ConcreteCategory.congr_hom (congr_app (e_id_comp SSet K L) m) s

@[simp]
lemma comp_idS {K L : C} (s : (sHom K L).obj m) :
    comp s (idS m L) = s :=
  ConcreteCategory.congr_hom (congr_app (e_comp_id SSet K L) m) s

lemma comp_assoc {K L M N : C} (s : (sHom K L).obj m) (t : (sHom L M).obj m)
    (r : (sHom M N).obj m) :
    comp (comp s t) r = comp s (comp t r) :=
  ConcreteCategory.congr_hom (congr_app (e_assoc SSet K L M N) m)
    ((s, (t, r)) : (sHom K L ⊗ (sHom L M ⊗ sHom M N)).obj m)

/-- The category of `m`-simplices of a simplicial category `C`: the objects of `C`, and the
`m`-simplices of `sHom A B` as morphisms `A ⟶ B`. -/
@[kerodon 00JT]
structure Level (C : Type u) [Category.{v} C] [SimplicialCategory C]
    (m : SimplexCategoryᵒᵖ) : Type u where
  /-- The underlying object of `C`. -/
  as : C

instance : Category.{v} (Level C m) where
  Hom A B := (sHom A.as B.as).obj m
  id A := idS m A.as
  comp s t := comp s t
  id_comp := idS_comp
  comp_id := comp_idS
  assoc := comp_assoc

end SimplicialCategory

end CategoryTheory
