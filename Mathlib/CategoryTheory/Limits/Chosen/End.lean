/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.End

/-!
# Chosen ends and coends

This file defines typeclasses `ChosenCoends` and `ChosenEnds` which contain the data of a chosen
coend and end in `C` for each functor `Jᵒᵖ ⥤ J ⥤ C`.
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

/-- The data of chosen ends in `C`. -/
@[nolint checkUnivs, univ_out_params, pp_with_univ]
class ChosenEnds (C : Type*) [Category* C] where
  /-- The chosen wedge for each functor `Jᵒᵖ ⥤ J ⥤ C`. -/
  wedge {J : Type u} [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ C) : Wedge F
  /-- The chosen wedge is limiting. -/
  isEnd {J : Type u} [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ C) : IsLimit (wedge F)

variable {C : Type*} [Category* C] [ChosenEnds.{v, u} C]
variable {J : Type u} [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ C)

/-- The chosen end of a functor `Jᵒᵖ ⥤ J ⥤ C`. -/
def chosenEnd : C := (ChosenEnds.wedge F).pt

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the projection `chosenEnd F ⟶ (F.obj (op j)).obj j`
for any `j : J`. -/
def chosenEnd.π (j : J) : chosenEnd F ⟶ (F.obj (op j)).obj j :=
  (ChosenEnds.wedge F).ι j

lemma chosenEnd.condition {i j : J} (f : i ⟶ j) :
    chosenEnd.π F i ≫ (F.obj (op i)).map f = chosenEnd.π F j ≫ (F.map f.op).app j :=
  (ChosenEnds.wedge F).condition f

variable {F}

/-- Morphisms into the chosen end are determined by their composites with `chosenEnd.π`. -/
@[ext]
lemma chosenEnd.hom_ext {X : C} {f g : X ⟶ chosenEnd F}
    (h : ∀ j, f ≫ chosenEnd.π F j = g ≫ chosenEnd.π F j) : f = g :=
  Wedge.IsLimit.hom_ext (ChosenEnds.isEnd F) h

variable {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j)

/-- Constructor for morphisms into the chosen end of a functor. -/
def chosenEnd.lift : X ⟶ chosenEnd F :=
  Wedge.IsLimit.lift (ChosenEnds.isEnd F) f hf

@[reassoc (attr := simp)]
lemma chosenEnd.lift_π (j : J) : chosenEnd.lift f hf ≫ chosenEnd.π F j = f j := by
  apply IsLimit.fac

/-- A natural transformation of bifunctors induces a map on chosen ends. -/
def chosenEnd.map {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) : chosenEnd F ⟶ chosenEnd G :=
  chosenEnd.lift (fun x ↦ chosenEnd.π F x ≫ (f.app (op x)).app x) (fun j j' φ ↦ by
    have e := (f.app (op j)).naturality φ
    simp only [Category.assoc]
    rw [← e, reassoc_of% chosenEnd.condition F φ]
    simp)

@[reassoc (attr := simp)]
lemma chosenEnd.map_π {G : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (j : J) :
    chosenEnd.map f ≫ chosenEnd.π G j = chosenEnd.π F j ≫ (f.app (op j)).app j := by
  simp [chosenEnd.map]

@[simp]
lemma chosenEnd.map_id : chosenEnd.map (𝟙 F) = 𝟙 _ := by cat_disch

@[reassoc (attr := simp)]
lemma chosenEnd.map_comp {G H : Jᵒᵖ ⥤ J ⥤ C} (f : F ⟶ G) (g : G ⟶ H) :
    chosenEnd.map f ≫ chosenEnd.map g = chosenEnd.map (f ≫ g) := by
  cat_disch

/-- The chosen end construction as a functor out of the bifunctor category. -/
@[simps]
def chosenEndFunctor : (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where
  obj := chosenEnd
  map := chosenEnd.map

end CategoryTheory.Limits
