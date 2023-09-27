/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.Condensed.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Limits.Presheaf

universe u

open CategoryTheory

def TopCat.condensedVal (X : TopCat.{u}) :
    CompHaus.{u}ᵒᵖ ⥤ Type (u+1) :=
  compHausToTop.op ⋙ yoneda.obj X ⋙ uliftFunctor.{u+1}

lemma TopCat.isSheaf_condensedVal (X : TopCat.{u}) :
    Presheaf.IsSheaf (coherentTopology _) X.condensedVal := by
  rw [isSheaf_iff_isSheaf_of_type, isSheaf_coherent]
  intro B α _ X π hπ
  have := (CompHaus.effectiveEpiFamily_tfae X π).out 0 2
  rw [this] at hπ ; clear this
  sorry


def TopCat.condensed (X : TopCat.{u}) : Condensed.{u} (Type (u+1)) where
  val := X.condensedVal
  cond := X.isSheaf_condensedVal

def TopCat.mapCondensed {X Y : TopCat.{u}} (f : X ⟶ Y) : X.condensed ⟶ Y.condensed :=
  ⟨whiskerLeft _ <| whiskerRight (yoneda.map f) _⟩

@[simp]
lemma TopCat.mapCondensed_id (X : TopCat.{u}) : TopCat.mapCondensed (𝟙 X) = 𝟙 _ := rfl

@[reassoc (attr := simp)]
lemma TopCat.mapCondensed_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.mapCondensed (f ≫ g) = TopCat.mapCondensed f ≫ TopCat.mapCondensed g :=
  rfl

def TopCat.toCodnensed : TopCat.{u} ⥤ Condensed.{u} (Type (u+1)) where
  obj X := X.condensed
  map f := TopCat.mapCondensed f
