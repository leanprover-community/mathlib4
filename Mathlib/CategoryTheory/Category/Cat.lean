/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Bicategory.Strict

/-!
# Category of categories

This file contains the definition of the category `Cat` of all categories.
In this category objects are categories and
morphisms are functors between these categories.

## Implementation notes

Though `Cat` is not a concrete category, we use `bundled` to define
its carrier type.
-/


universe v u

namespace CategoryTheory

open Bicategory

-- intended to be used with explicit universe parameters
/-- Category of categories. -/
@[nolint checkUnivs]
def Cat :=
  Bundled Category.{v, u}

namespace Cat

instance : Inhabited Cat :=
  ⟨⟨Type u, CategoryTheory.types⟩⟩

-- Porting note: maybe this coercion should be defined to be `objects.obj`?
instance : CoeSort Cat (Type u) :=
  ⟨Bundled.α⟩

instance str (C : Cat.{v, u}) : Category.{v, u} C :=
  Bundled.str C

/-- Construct a bundled `Cat` from the underlying type and the typeclass. -/
def of (C : Type u) [Category.{v} C] : Cat.{v, u} :=
  Bundled.of C

/-- Bicategory structure on `Cat` -/
instance bicategory : Bicategory.{max v u, max v u} Cat.{v, u} where
  Hom C D := C ⥤ D
  id C := 𝟭 C
  comp F G := F ⋙ G
  homCategory := fun _ _ => Functor.category
  whiskerLeft {_} {_} {_} F _ _ η := whiskerLeft F η
  whiskerRight {_} {_} {_} _ _ η H := whiskerRight η H
  associator {_} {_} {_} _ := Functor.associator
  leftUnitor {_} _ := Functor.leftUnitor
  rightUnitor {_} _ := Functor.rightUnitor
  pentagon := fun {_} {_} {_} {_} {_}=> Functor.pentagon
  triangle {_} {_} {_} := Functor.triangle

/-- `Cat` is a strict bicategory. -/
instance bicategory.strict : Bicategory.Strict Cat.{v, u} where
  id_comp {C} {D} F := by cases F; rfl
  comp_id {C} {D} F := by cases F; rfl
  assoc := by intros; rfl

/-- Category structure on `Cat` -/
instance category : LargeCategory.{max v u} Cat.{v, u} :=
  StrictBicategory.category Cat.{v, u}

@[ext]
theorem ext {C D : Cat} {F G : C ⟶ D} {α β : F ⟶ G} (w : α.app = β.app) : α = β :=
  NatTrans.ext w

@[simp]
theorem id_obj {C : Cat} (X : C) : (𝟙 C : C ⥤ C).obj X = X :=
  rfl

@[simp]
theorem id_map {C : Cat} {X Y : C} (f : X ⟶ Y) : (𝟙 C : C ⥤ C).map f = f :=
  rfl

@[simp]
theorem comp_obj {C D E : Cat} (F : C ⟶ D) (G : D ⟶ E) (X : C) : (F ≫ G).obj X = G.obj (F.obj X) :=
  rfl

@[simp]
theorem comp_map {C D E : Cat} (F : C ⟶ D) (G : D ⟶ E) {X Y : C} (f : X ⟶ Y) :
    (F ≫ G).map f = G.map (F.map f) :=
  rfl

@[simp]
theorem id_app {C D : Cat} (F : C ⟶ D) (X : C) : (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X) := rfl

@[simp]
theorem comp_app {C D : Cat} {F G H : C ⟶ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
    (α ≫ β).app X = α.app X ≫ β.app X := rfl

@[simp]
theorem eqToHom_app {C D : Cat} (F G : C ⟶ D) (h : F = G) (X : C) :
    (eqToHom h).app X = eqToHom (Functor.congr_obj h X) :=
  CategoryTheory.eqToHom_app h X

@[simp]
lemma whiskerLeft_app {C D E : Cat} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H) (X : C) :
    (F ◁ η).app X = η.app (F.obj X) :=
  rfl

@[simp]
lemma whiskerRight_app {C D E : Cat} {F G : C ⟶ D} (H : D ⟶ E) (η : F ⟶ G) (X : C) :
    (η ▷ H).app X = H.map (η.app X) :=
  rfl

lemma leftUnitor_hom_app {B C : Cat} (F : B ⟶ C) (X : B) : (λ_ F).hom.app X = eqToHom (by simp) :=
  rfl

lemma leftUnitor_inv_app {B C : Cat} (F : B ⟶ C) (X : B) : (λ_ F).inv.app X = eqToHom (by simp) :=
  rfl

lemma rightUnitor_hom_app {B C : Cat} (F : B ⟶ C) (X : B) : (ρ_ F).hom.app X = eqToHom (by simp) :=
  rfl

lemma rightUnitor_inv_app {B C : Cat} (F : B ⟶ C) (X : B) : (ρ_ F).inv.app X = eqToHom (by simp) :=
  rfl

lemma associator_hom_app {B C D E : Cat} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B) :
    (α_ F G H).hom.app X = eqToHom (by simp) :=
  rfl

lemma associator_inv_app {B C D E : Cat} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B) :
    (α_ F G H).inv.app X = eqToHom (by simp) :=
  rfl

/-- The identity in the category of categories equals the identity functor. -/
theorem id_eq_id (X : Cat) : 𝟙 X = 𝟭 X := rfl

/-- Composition in the category of categories equals functor composition. -/
theorem comp_eq_comp {X Y Z : Cat} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙ G := rfl

@[simp] theorem of_α (C) [Category C] : (of C).α = C := rfl

@[simp] theorem coe_of (C : Cat.{v, u}) : Cat.of C = C := rfl

end Cat

namespace Functor

/-- Functors between categories of the same size define arrows in `Cat`. -/
def toCatHom {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    Cat.of C ⟶ Cat.of D := F

/-- Arrows in `Cat` define functors. -/
def ofCatHom {C D : Type} [Category C] [Category D] (F : Cat.of C ⟶ Cat.of D) : C ⥤ D := F

@[simp] theorem to_ofCatHom {C D : Type} [Category C] [Category D] (F : Cat.of C ⟶ Cat.of D) :
    (ofCatHom F).toCatHom = F := rfl

@[simp] theorem of_toCatHom {C D : Type} [Category C] [Category D] (F : C ⥤ D) :
    ofCatHom (F.toCatHom) = F := rfl

end Functor
namespace Cat

/-- Functor that gets the set of objects of a category. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Cat.{v, u} ⥤ Type u where
  obj C := C
  map F := F.obj

-- Porting note: this instance was needed for CategoryTheory.Category.Cat.Limit
instance (X : Cat.{v, u}) : Category (objects.obj X) := (inferInstance : Category X)

section

attribute [local simp] eqToHom_map

/-- Any isomorphism in `Cat` induces an equivalence of the underlying categories. -/
def equivOfIso {C D : Cat} (γ : C ≅ D) : C ≌ D where
  functor := γ.hom
  inverse := γ.inv
  unitIso := eqToIso <| Eq.symm γ.hom_inv_id
  counitIso := eqToIso γ.inv_hom_id

end

end Cat

/-- Embedding `Type` into `Cat` as discrete categories.

This ought to be modelled as a 2-functor!
-/
@[simps]
def typeToCat : Type u ⥤ Cat where
  obj X := Cat.of (Discrete X)
  map := fun f => Discrete.functor (Discrete.mk ∘ f)
  map_id X := by
    apply Functor.ext
    · intro X Y f
      cases f
      simp only [id_eq, eqToHom_refl, Cat.id_map, Category.comp_id, Category.id_comp]
      apply ULift.ext
      aesop_cat
    · simp
  map_comp f g := by apply Functor.ext; aesop_cat

instance : Functor.Faithful typeToCat.{u} where
  map_injective {_X} {_Y} _f _g h :=
    funext fun x => congr_arg Discrete.as (Functor.congr_obj h ⟨x⟩)

instance : Functor.Full typeToCat.{u} where
  map_surjective F := ⟨Discrete.as ∘ F.obj ∘ Discrete.mk, by
    apply Functor.ext
    · intro x y f
      dsimp
      apply ULift.ext
      aesop_cat
    · rintro ⟨x⟩
      apply Discrete.ext
      rfl⟩

end CategoryTheory
