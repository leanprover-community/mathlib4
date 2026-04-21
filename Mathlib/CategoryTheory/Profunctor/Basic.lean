/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Adam Topaz, Adrian Marti
-/
module

public import Mathlib.CategoryTheory.Yoneda

/-!

# Profunctors

A profunctor from a category `C` to a category `D` is a functor from `C` to a category of
presheaves of sets on `D`. We define this as `Profunctor.{w} C D := C ⥤ Dᵒᵖ ⥤ Type w`.

This file provides convenient constructors `ProfunctorCore` and `ProfunctorCore.Hom` for profunctors
and natural transformations between them. We also define the identity profunctor `Profunctor.id`
as the Yoneda bifunctor, the opposite of a profunctor, the `ulift` of a profunctor, whiskering
of a profunctor with functors, and the profunctors in both directions corresponding to a functor
`C ⥤ D` (see `Functor.toProfunctor` and `Functor.toProfunctorFlip`).

## Future work

- Define composition of profunctors.
- Define the bicategory of categories where the 1-morphisms are profunctors.
-/

@[expose] public section

namespace CategoryTheory

open Opposite

universe w' w v₁ v₂ u₁ u₂

variable (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D]

/-- Custom structure to construct profunctors, i.e. bifunctors `C ⥤ Dᵒᵖ ⥤ Type w`. -/
@[pp_with_univ]
structure ProfunctorCore where
  /-- The object part -/
  obj : C → D → Type w
  /-- The morphism part -/
  map {X X' : C} {Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') : obj X Y' ⟶ obj X' Y
  map_id (X : C) (Y : D) : map (𝟙 X) (𝟙 Y) = 𝟙 _ := by cat_disch
  map_comp {X₁ X₂ X₃ : C} {Y₁ Y₂ Y₃ : D} (f : X₁ ⟶ X₂) (f' : X₂ ⟶ X₃) (g : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃) :
    map (f ≫ f') (g ≫ g') = map f g' ≫ map f' g := by cat_disch

attribute [simp] ProfunctorCore.map_id ProfunctorCore.map_comp

/-- A profunctor from C to D (`Profunctor.{w} C D`) is a bifunctor `C ⥤ Dᵒᵖ ⥤ Type w`. -/
@[pp_with_univ]
abbrev Profunctor := C ⥤ Dᵒᵖ ⥤ Type w

variable {C D}

/-- Typecheck a bifunctor `C ⥤ Dᵒᵖ ⥤ Type w` as a profunctor. -/
abbrev Functor.profunctor (F : C ⥤ Dᵒᵖ ⥤ Type w) : Profunctor.{w} C D := F

namespace ProfunctorCore

/-- Custom structure to construct natural transformations between profunctors, see
`CategoryTheory.Profunctor.ofHom`. -/
structure Hom (P Q : ProfunctorCore.{w} C D) where
  /-- The components of the natural transformation -/
  app (X : C) (Y : D) : P.obj X Y ⟶ Q.obj X Y
  naturality ⦃X X' : C⦄ ⦃Y Y' : D⦄ (f : X ⟶ X') (g : Y ⟶ Y') :
    P.map f g ≫ app X' Y = app X Y' ≫ Q.map f g := by cat_disch

attribute [reassoc (attr := simp)] ProfunctorCore.Hom.naturality

@[simp]
lemma map_id_comp (P : ProfunctorCore.{w} C D) (X : C) {Y Y' Y'' : D}
    (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    P.map (𝟙 X) (g ≫ g') = P.map (𝟙 X) g' ≫ P.map (𝟙 X) g := by
  nth_rw 1 [← Category.id_comp (𝟙 X)]
  simp only [P.map_comp]

@[simp]
lemma map_comp_id (P : ProfunctorCore.{w} C D) {X X' X'' : C} (Y : D)
    (f : X ⟶ X') (f' : X' ⟶ X'') :
    P.map (f ≫ f') (𝟙 Y) = P.map f (𝟙 Y) ≫ P.map f' (𝟙 Y) := by
  nth_rw 1 [← Category.id_comp (𝟙 Y)]
  simp only [P.map_comp]

@[reassoc (attr := simp)]
lemma map_lid_comp_map_rid (P : ProfunctorCore.{w} C D) {X X' : C} {Y Y' : D}
    (f : X ⟶ X') (g : Y ⟶ Y') : P.map (𝟙 _) g ≫ P.map f (𝟙 _) = P.map f g := by
  simp [← P.map_comp]

@[reassoc (attr := simp)]
lemma map_rid_comp_map_lid (P : ProfunctorCore.{w} C D) {X X' : C} {Y Y' : D}
    (f : X ⟶ X') (g : Y ⟶ Y') : P.map f (𝟙 _) ≫ P.map (𝟙 _) g = P.map f g := by
  simp [← P.map_comp]

end ProfunctorCore

namespace Profunctor

/-- Construct a profunctor from a `ProfunctorCore`. -/
@[simps]
def ofCore (P : ProfunctorCore.{w} C D) : Profunctor.{w} C D where
  obj X := { obj Y := P.obj X (unop Y), map f := P.map (𝟙 _) f.unop }
  map g := { app X := P.map g (𝟙 _) }

/-- Construct a natural transformation between profunctors from a `ProfunctorCore.Hom`. -/
@[simps]
def ofHom {P Q : ProfunctorCore.{w} C D} (f : P.Hom Q) : ofCore P ⟶ ofCore Q where
  app X := { app Y := f.app X (unop Y) }

/-- The identity profunctor from `C` to `C`. This is defined as the Yoneda bifunctor. -/
@[simps! obj_obj obj_map map_app]
protected def id : Profunctor C C := yoneda

/-- The opposite of a profunctor. -/
@[simps! obj_obj obj_map map_app]
def op (P : Profunctor.{w} C D) : Profunctor.{w} Dᵒᵖ Cᵒᵖ :=
  .ofCore {
    obj X Y := (P.obj (unop Y)).obj X
    map f g := (P.map g.unop).app _ ≫ (P.obj _).map f }

/-- Whisker a profunctor from `C` to `D` with functors into `C` and `D`. -/
@[simps! obj_obj obj_map map_app]
def whiskerLeft₂ {A B : Type*} [Category* A] [Category* B]
    (P : Profunctor.{w} C D) (F : A ⥤ C) (G : B ⥤ D) : Profunctor.{w} A B :=
  (((Functor.whiskeringLeft₂ _).obj F).obj G.op).obj P

/-- Increase the universe level of a profunctor. -/
@[pp_with_univ, simps! obj_obj obj_map map_app]
def ulift (P : Profunctor.{w} C D) : Profunctor.{max w' w} C D :=
  (Functor.postcompose₂.obj uliftFunctor).obj P

/-- Increase the universe level of a profunctor by one. This enables dot notation `P.ulift1`,
which is not possible with `Profunctor.ulift`. -/
abbrev ulift1 (P : Profunctor.{w} C D) : Profunctor.{w + 1} C D :=
  Profunctor.ulift.{w + 1} P

end Profunctor

/-- Given a functor from `C` to `D`, this is the corresponding profunctor from `C` to `D`. -/
@[simps! obj_obj obj_map map_app]
def Functor.toProfunctor (F : C ⥤ D) : Profunctor.{v₂} C D :=
  (Profunctor.id (C := D)).whiskerLeft₂ F (𝟭 _)

/-- Given a functor from `C` to `D`, this is the corresponding profunctor from `D` to `C`. -/
@[simps! obj_obj obj_map map_app]
def Functor.toProfunctorRev (F : C ⥤ D) : Profunctor.{v₂} D C :=
  (Profunctor.id (C := D)).whiskerLeft₂ (𝟭 _) F

end CategoryTheory
