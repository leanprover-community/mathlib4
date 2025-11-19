/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.CategoryTheory.Bicategory.Strict.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Bundled
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Category of categories

This file contains the definition of the category `Cat` of all categories.
In this category objects are categories and
morphisms are functors between these categories.

## Implementation notes

Though `Cat` is not a concrete category, we use `bundled` to define
its carrier type.
-/

@[expose] public section


universe v u

namespace CategoryTheory

open Bicategory Functor

-- intended to be used with explicit universe parameters
/-- Category of categories. -/
@[nolint checkUnivs]
def Cat :=
  Bundled Category.{v, u}

namespace Cat

instance : Inhabited Cat :=
  ⟨⟨Type u, CategoryTheory.types⟩⟩

-- TODO: maybe this coercion should be defined to be `objects.obj`?
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
def ofCatHom {C D : Cat.{v, u}} (F : C ⟶ D) : C ⥤ D := F

@[simp] theorem to_ofCatHom {C D : Cat.{v, u}} (F : C ⟶ D) :
    (ofCatHom F).toCatHom = F := rfl

@[simp] theorem of_toCatHom {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    ofCatHom (F.toCatHom) = F := rfl

@[simp]
lemma _root_.CategoryTheory.Cat.id_of (C : Type u) [Category.{v} C] :
    𝟙 (Cat.of C) = (Functor.id C).toCatHom := rfl

lemma toCatHom_id (C : Type u) [Category.{v} C] :
    (Functor.id C).toCatHom = 𝟙 (Cat.of C) := rfl

@[simp]
lemma toCatHom_comp_toCatHom {C D E : Type u} [Category.{v} C] [Category.{v} D]
    [Category.{v} E] (F : C ⥤ D) (G : D ⥤ E) :
    F.toCatHom ≫ G.toCatHom = (F ⋙ G).toCatHom := rfl

@[simp]
lemma toCatHom_congr {C D : Type u} [Category.{v} C] [Category.{v} D] (F G : C ⥤ D) :
    F.toCatHom = G.toCatHom ↔ F = G where
  mp := congrArg ofCatHom
  mpr := congrArg toCatHom

end Functor

namespace NatTrans

def toCatHom₂ {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤ D} (η : F ⟶ G) :
    F.toCatHom ⟶ G.toCatHom := η

def ofCatHom₂ {C D : Cat.{v, u}} {F G : C ⟶ D}
  (η : F ⟶ G) : (ofCatHom F) ⟶ (ofCatHom G) := η

@[simp]
lemma of_toCatHom₂ {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤ D} (η : F ⟶ G) :
  ofCatHom₂ (η.toCatHom₂) = η := rfl

@[simp]
lemma toCatHom₂_congr {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤ D}
    (η₁ η₂ : F ⟶ G) : η₁.toCatHom₂ = η₂.toCatHom₂ ↔ η₁ = η₂ where
  mp := congrArg ofCatHom₂
  mpr := congrArg toCatHom₂

@[simps]
def toCatIso₂ {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤ D}
    (η : F ≅ G) : F.toCatHom ≅ G.toCatHom where
  hom := η.hom.toCatHom₂
  inv := η.inv.toCatHom₂
  hom_inv_id := congr(toCatHom₂ $η.hom_inv_id)
  inv_hom_id := congr(toCatHom₂ $η.inv_hom_id)

@[simps]
def ofCatIso₂ {C D : Cat.{v, u}} {F G : C ⟶ D}
    (η : F ≅ G) : (ofCatHom F) ≅ (ofCatHom G) where
  hom := ofCatHom₂ η.hom
  inv := ofCatHom₂ η.inv
  hom_inv_id := congr(ofCatHom₂ $η.hom_inv_id)
  inv_hom_id := congr(ofCatHom₂ $η.inv_hom_id)

@[simp]
lemma of_toCatIso₂ {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤ D}
    (η : F ≅ G) : ofCatIso₂ (toCatIso₂ η) = η := rfl

@[simp]
lemma to_ofCatIso {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ≅ G) :
    toCatIso₂ (ofCatIso₂ η) = η := rfl

@[simp]
lemma _root_.CategoryTheory.Cat.id_toCatHom {C D : Type u} [Category.{v} C] [Category.{v} D]
  (F : C ⥤ D) : 𝟙 (F.toCatHom) = (𝟙 F : F ⟶ F).toCatHom₂ := rfl

lemma toCatHom₂_id {C D : Type u} [Category.{v} C] [Category.{v} D]
  (F : C ⥤ D) : (𝟙 F : F ⟶ F).toCatHom₂ = 𝟙 (F.toCatHom) := rfl

@[simp]
lemma toCatHom₂_comp_toCatHom₂ {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G H : C ⥤ D} (η₁ : F ⟶ G) (η₂ : G ⟶ H) :
    η₁.toCatHom₂ ≫ η₂.toCatHom₂ = (η₁ ≫ η₂).toCatHom₂ := rfl

@[simp]
lemma _root_.CategoryTheory.Cat.toCatHom_whiskerLeft_toCatHom₂ {C D E : Type u}
    [Category.{v} C] [Category.{v} D] [Category.{v} E] (F : C ⥤ D) {G H : D ⥤ E}
    (η : G ⟶ H) : F.toCatHom ◁ (η.toCatHom₂) = (F.whiskerLeft η).toCatHom₂ := rfl

@[simp]
lemma _root_.CategoryTheory.Cat.toCatHom₂_whiskerRight_toCatHom {C D E : Type u}
    [Category.{v} C] [Category.{v} D] [Category.{v} E] {F G : C ⥤ D} (η : F ⟶ G)
    (H : D ⥤ E) : (η.toCatHom₂) ▷ H.toCatHom = (Functor.whiskerRight η H).toCatHom₂ := rfl

-- in the following section, we should decide which of these pairs should be simp.
section

lemma _root_.CategoryTheory.Cat.associator_toCatHom_hom {B C D E : Type u} [Category.{v} B]
    [Category.{v} C] [Category.{v} D] [Category.{v} E] (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E) :
    (α_ (F.toCatHom) (G.toCatHom) (H.toCatHom)).hom =
      (Functor.associator F G H).hom.toCatHom₂ := rfl

lemma toCatHom₂_associator_hom {B C D E : Type u} [Category.{v} B] [Category.{v} C] [Category.{v} D]
    [Category.{v} E] (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E) :
    (Functor.associator F G H).hom.toCatHom₂ = (α_ (F.toCatHom) (G.toCatHom) (H.toCatHom)).hom :=
    rfl

lemma _root_.CategoryTheory.Cat.associator_toCatHom_inv {B C D E : Type u} [Category.{v} B]
    [Category.{v} C] [Category.{v} D] [Category.{v} E] (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E) :
    (α_ (F.toCatHom) (G.toCatHom) (H.toCatHom)).inv =
      (Functor.associator F G H).inv.toCatHom₂ := rfl

lemma toCatHom₂_associator_inv {B C D E : Type u} [Category.{v} B] [Category.{v} C] [Category.{v} D]
    [Category.{v} E] (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E) :
    (Functor.associator F G H).inv.toCatHom₂ = (α_ (F.toCatHom) (G.toCatHom) (H.toCatHom)).inv :=
  rfl

lemma _root_.CategoryTheory.Cat.leftUnitor_toCatHom_hom {C D : Type u} [Category.{v} C]
    [Category.{v} D] (F : C ⥤ D) : (λ_ F.toCatHom).hom = (Functor.leftUnitor F).hom.toCatHom₂ := rfl

lemma _root_.CategoryTheory.Cat.leftUnitor_toCatHom_inv {C D : Type u} [Category.{v} C]
    [Category.{v} D] (F : C ⥤ D) : (λ_ F.toCatHom).inv = (Functor.leftUnitor F).inv.toCatHom₂ := rfl

lemma _root_.CategoryTheory.Cat.rightUnitor_toCatHom_hom {C D : Type u} [Category.{v} C]
    [Category.{v} D] (F : C ⥤ D) : (ρ_ F.toCatHom).hom = (Functor.rightUnitor F).hom.toCatHom₂ :=
  rfl

lemma _root_.CategoryTheory.Cat.rightUnitor_toCatHom_inv {C D : Type u} [Category.{v} C]
    [Category.{v} D] (F : C ⥤ D) : (ρ_ F.toCatHom).inv = (Functor.rightUnitor F).inv.toCatHom₂ :=
  rfl

end

end NatTrans
namespace Cat

/-- Functor that gets the set of objects of a category. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Cat.{v, u} ⥤ Type u where
  obj C := C
  map F := F.obj

/-- See through the defeq `objects.obj X = X`. -/
instance (X : Cat.{v, u}) : Category (objects.obj X) := inferInstanceAs <| Category X

section

attribute [local simp] eqToHom_map

/-- Any isomorphism in `Cat` induces an equivalence of the underlying categories. -/
def equivOfIso {C D : Cat} (γ : C ≅ D) : C ≌ D where
  functor := γ.hom
  inverse := γ.inv
  unitIso := eqToIso <| Eq.symm γ.hom_inv_id
  counitIso := eqToIso γ.inv_hom_id

/-- Under certain hypotheses, an equivalence of categories actually
defines an isomorphism in `Cat`. -/
@[simps]
def isoOfEquiv {C D : Cat.{v, u}} (e : C ≌ D)
    (h₁ : ∀ (X : C), e.inverse.obj (e.functor.obj X) = X)
    (h₂ : ∀ (Y : D), e.functor.obj (e.inverse.obj Y) = Y)
    (h₃ : ∀ (X : C), e.unitIso.hom.app X = eqToHom (h₁ X).symm := by cat_disch)
    (h₄ : ∀ (Y : D), e.counitIso.hom.app Y = eqToHom (h₂ Y) := by cat_disch) :
    C ≅ D where
  hom := e.functor
  inv := e.inverse
  hom_inv_id := (Functor.ext_of_iso e.unitIso (fun X ↦ (h₁ X).symm) h₃).symm
  inv_hom_id := (Functor.ext_of_iso e.counitIso h₂ h₄)

end

end Cat

/-- Embedding `Type` into `Cat` as discrete categories.

This ought to be modelled as a 2-functor!
-/
@[simps]
def typeToCat : Type u ⥤ Cat where
  obj X := Cat.of (Discrete X)
  map f := (Discrete.functor (Discrete.mk ∘ f)).toCatHom
  map_id X := by
    simp only [Cat.id_of, toCatHom_congr]
    fapply Functor.ext
    · simp
    · intro X Y f
      cases f
      simp only [Discrete.functor_obj_eq_as, Function.comp_apply, types_id_apply, Discrete.mk_as,
        id_obj, eqToHom_refl, Functor.id_map, Category.comp_id, Category.id_comp]
      apply ULift.ext
      cat_disch
  map_comp f g := by
    simp only [toCatHom_comp_toCatHom, toCatHom_congr]
    apply Functor.ext
    cat_disch

instance : Functor.Faithful typeToCat.{u} where
  map_injective {X} {Y} f g h := by
    ext x
    have := congrArg (Discrete.as) (Functor.congr_obj h ⟨x⟩)
    simp only [typeToCat_obj, Cat.of_α, typeToCat_map] at this

    exact this

instance : Functor.Full typeToCat.{u} where
  map_surjective F := ⟨Discrete.as ∘ F.obj ∘ Discrete.mk, by
    apply Functor.ext
    · intro x y f
      dsimp
      apply ULift.ext
      cat_disch
    · rintro ⟨x⟩
      apply Discrete.ext
      rfl⟩

end CategoryTheory
