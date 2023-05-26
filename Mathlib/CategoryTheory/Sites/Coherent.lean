/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.CategoryTheory.Sites.Coverage

namespace CategoryTheory

variable {C : Type _} [Category C]

@[ext]
structure Presieve.DiagramBase {X : C} (S : Presieve X) where
  Y : C
  f : Y ⟶ X
  hf : S f

@[ext]
structure Presieve.Relation {X : C} (S : Presieve X) (Y₁ Y₂ : S.DiagramBase) where
  R : C
  g₁ : R ⟶ Y₁.Y
  g₂ : R ⟶ Y₂.Y
  r : R ⟶ X
  w₁ : g₁ ≫ Y₁.f = r
  w₂ : g₂ ≫ Y₂.f = r

attribute [reassoc (attr := simp)]
  Presieve.Relation.w₁
  Presieve.Relation.w₂

@[ext]
structure Presieve.RelationHom {X : C} (S : Presieve X) {Y₁ Y₂ : S.DiagramBase}
    (R₁ R₂ : S.Relation Y₁ Y₂) where
  e : R₁.R ⟶ R₂.R
  w₁ : e ≫ R₂.g₁ = R₁.g₁
  w₂ : e ≫ R₂.g₂ = R₁.g₂

@[simps]
def Presieve.RelationHom.comp {X : C} {S : Presieve X} {Y₁ Y₂ : S.DiagramBase}
    {R₁ R₂ R₃ : S.Relation Y₁ Y₂} (f : S.RelationHom R₁ R₂) (g : S.RelationHom R₂ R₃) :
    S.RelationHom R₁ R₃ where
  e := f.e ≫ g.e
  w₁ := by simp [f.w₁, g.w₁]
  w₂ := by simp [f.w₂, g.w₂]

@[simps]
def Presieve.RelationHom.id {X : C} {S : Presieve X} {Y₁ Y₂ : S.DiagramBase}
    (R : S.Relation Y₁ Y₂ ) : S.RelationHom R R where
  e := 𝟙 _
  w₁ := by simp
  w₂ := by simp

instance Presieve.instCategoryRelationHom {X : C} {S : Presieve X} (Y₁ Y₂ : S.DiagramBase) :
    Category (S.Relation Y₁ Y₂) where
  Hom := S.RelationHom
  id := Presieve.RelationHom.id
  comp := Presieve.RelationHom.comp

@[reassoc (attr := simp)]
lemma Presieve.RelationHom_w₁ {X : C} {S : Presieve X} {Y₁ Y₂ : S.DiagramBase}
    (R₁ R₂ : S.Relation Y₁ Y₂) (e : R₁ ⟶ R₂) : e.e ≫ R₂.g₁ = R₁.g₁ := e.w₁

@[reassoc (attr := simp)]
lemma Presieve.RelationHom_w₂ {X : C} {S : Presieve X} {Y₁ Y₂ : S.DiagramBase}
    (R₁ R₂ : S.Relation Y₁ Y₂) (e : R₁ ⟶ R₂) : e.e ≫ R₂.g₂ = R₁.g₂ := e.w₂

@[reassoc (attr := simp)]
lemma Presieve.RelationHom_e_r {X : C} {S : Presieve X} {Y₁ Y₂ : S.DiagramBase}
    (R₁ R₂ : S.Relation Y₁ Y₂) (e : S.RelationHom R₁ R₂) :
    e.e ≫ R₂.r = R₁.r := by
  simp only [← R₁.w₁, ← R₁.w₂, ← R₂.w₁, ← R₂.w₂, ← Category.assoc, e.w₁]

@[reassoc (attr := simp)]
lemma Presieve.RelationHom_id_e {X : C} {S : Presieve X} {Y₁ Y₂ : S.DiagramBase}
    (R : S.Relation Y₁ Y₂) : (𝟙 R : R ⟶ R).e = 𝟙 _ := rfl

@[reassoc (attr := simp)]
lemma Presieve.RelationHom_comp_e {X : C} {S : Presieve X} {Y₁ Y₂ : S.DiagramBase}
    {R₁ R₂ R₃ : S.Relation Y₁ Y₂} (f : R₁ ⟶ R₂) (g : R₂ ⟶ R₃) :
    (f ≫ g).e = f.e ≫ g.e := rfl

inductive Presieve.Diagram {X : C} (S : Presieve X) where
  | cover (Y : S.DiagramBase) : S.Diagram
  | relation {Y₁ Y₂ : S.DiagramBase} (R : S.Relation Y₁ Y₂) : S.Diagram

inductive Presieve.DiagramHom {X : C} (S : Presieve X) :
    S.Diagram → S.Diagram → Type _ where
  | id (x : S.Diagram) : S.DiagramHom x x
  | rel {Y₁ Y₂ : S.DiagramBase} {R₁ R₂ : S.Relation Y₁ Y₂} (e : R₁ ⟶ R₂) :
      S.DiagramHom (.relation R₁) (.relation R₂)

def Presieve.DiagramHomComp {X : C} {S : Presieve X} {x y z : S.Diagram}
    (f : S.DiagramHom x y) (g : S.DiagramHom y z) : S.DiagramHom x z :=
  match f, g with
  | .id _, e => e
  | e, .id _ => e
  | .rel e₁, .rel e₂ => .rel (e₁ ≫ e₂)

instance Presieve.instCategoryDiagram {X : C} (S : Presieve X) : Category (S.Diagram) where
  Hom := S.DiagramHom
  id := .id
  comp := Presieve.DiagramHomComp
  id_comp := by rintro D₁ D₂ (_|_) <;> aesop_cat
  comp_id := by rintro D₁ D₂ (_|_) <;> aesop_cat
  assoc := by
    rintro D₁ D₂ D₃ D₄ (_|_) (_|_) (_|_) <;> try rfl
    dsimp [DiagramHomComp] ; simp


macro_rules
  | `(tactic| aesop $cs*) => `(tactic| aesop_no_checkpoint $cs*)
  | `(tactic| aesop? $cs*) => `(tactic| aesop_no_checkpoint? $cs*)

@[simps]
def Presieve.DiagramFunctor {X : C} (S : Presieve X) : S.Diagram ⥤ C where
  obj | .cover Y => Y.Y
      | .relation R => R.R
  map | .id _ => 𝟙 _
      | .rel e => e.e
  map_id := by rintro (_|_) <;> aesop
  map_comp := by rintro (_|_) (_|_) (_|_) (_|_) (_|_) <;> aesop

def Presieve.DiagramCocone {X : C} (S : Presieve X) : Limits.Cocone S.DiagramFunctor where
  pt := X
  ι := {
    app := fun Z =>
      match Z with
      | .cover Y => Y.f
      | .relation R => R.r
    naturality := by rintro (_|_) (_|_) (_|_) <;> aesop }

def Presieve.IsEffective {X : C} (S : Presieve X) : Prop :=
  Nonempty <| Limits.IsColimit S.DiagramCocone

end CategoryTheory
