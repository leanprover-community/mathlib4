/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.End

/-!
# Chosen Coends

This file defines a typeclass `ChosenCoends` which contains the data of a chosen coend in `C` for
each functor `Jᵒᵖ ⥤ J ⥤ C`.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory.Limits

/-- The data of chosen coends in `C`. -/
@[nolint checkUnivs, univ_out_params, pp_with_univ]
class ChosenCoends (C : Type*) [Category* C] where
  /-- The chosen cowedge for each functor `Jᵒᵖ ⥤ J ⥤ C`. -/
  cowedge {J : Type u} [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ C) : Cowedge F
  /-- The chosen cowedge is colimiting. -/
  isCoend {J : Type u} [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ C) : IsColimit (cowedge F)

variable {C : Type*} [Category* C] [ChosenCoends.{v, u} C]

variable {J : Type u} [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ C)

/-- The chosen coend of a functor `Jᵒᵖ ⥤ J ⥤ C`. -/
def chosenCoend : C := (ChosenCoends.cowedge F).pt

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the inclusion `(F.obj (op j)).obj j ⟶ chosenCoend F`
for any `j : J`. -/
def chosenCoend.ι (j : J) : (F.obj (op j)).obj j ⟶ chosenCoend F :=
  (ChosenCoends.cowedge F).π j

lemma chosenCoend.condition {i j : J} (f : i ⟶ j) :
    (F.map f.op).app _ ≫ chosenCoend.ι F i = (F.obj _).map f ≫ chosenCoend.ι F j :=
  (ChosenCoends.cowedge F).condition f

variable {F}

/-- Morphisms out of the chosen coend are determined by their composites with `chosenCoend.ι`. -/
@[ext]
lemma chosenCoend.hom_ext {X : C} {f g : chosenCoend F ⟶ X}
    (h : ∀ j, chosenCoend.ι F j ≫ f = chosenCoend.ι F j ≫ g) : f = g := by
  apply (ChosenCoends.isCoend F).hom_ext
  rintro (a | a)
  · simpa using _ ≫= h _
  · exact h _

variable {X : C} (f : ∀ j, (F.obj (op j)).obj j ⟶ X)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j)

/-- Constructor for morphisms out of the chosen coend of a functor. -/
def chosenCoend.desc : chosenCoend F ⟶ X :=
  Cowedge.IsColimit.desc (ChosenCoends.isCoend F) f hf

@[reassoc (attr := simp)]
lemma chosenCoend.ι_desc (j : J) : chosenCoend.ι F j ≫ chosenCoend.desc f hf = f j := by
  apply IsColimit.fac

/-- A natural transformation of bifunctors induces a map on chosen coends. -/
def chosenCoend.map {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) : chosenCoend F ⟶ chosenCoend G :=
  chosenCoend.desc (fun x ↦ (f.app (op x)).app x ≫ chosenCoend.ι _ _) (fun j j' φ ↦ by
    simp [chosenCoend.condition])

@[reassoc (attr := simp)]
lemma chosenCoend.ι_map {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (j : J) :
    chosenCoend.ι F j ≫ chosenCoend.map f = (f.app _).app _ ≫ chosenCoend.ι G j := by
  simp [chosenCoend.map]

@[simp]
lemma chosenCoend.map_id : chosenCoend.map (𝟙 F) = 𝟙 _ := by cat_disch

@[reassoc (attr := simp)]
lemma chosenCoend.map_comp {G H : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (g : G ⟶ H) :
    chosenCoend.map f ≫ chosenCoend.map g = chosenCoend.map (f ≫ g) := by
  cat_disch

/-- The chosen coend construction as a functor out of the bifunctor category. -/
@[simps]
def chosenCoendFunctor : (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where
  obj := chosenCoend
  map := chosenCoend.map

end CategoryTheory.Limits
