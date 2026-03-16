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

section

#adaptation_note /-- Removed `private`:
`ofFunctor` was marked `private` in #31807,
but we have removed this when disabling `set_option backward.privateInPublic` as a global option. -/
/--
The type of 1-morphisms in the bicategory of categories `Cat`.
This is a structure around `Functor` to prevent defeq-abuse
-/
@[ext]
structure Hom (C D : Cat.{v, u}) where
  ofFunctor ::
  /-- The Functor underlying a 1-morphism in Cat -/
  toFunctor : C ⥤ D

instance : Quiver (Cat.{v, u}) where
  Hom C D := Hom C D

/-- The 1-morphism in `Cat` corresponding to a functor. -/
@[simps]
def _root_.CategoryTheory.Functor.toCatHom {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) : Cat.of C ⟶ Cat.of D where
  toFunctor := F

@[ext]
lemma ext {C D : Cat.{v, u}} {F G : C ⟶ D} (h : F.toFunctor = G.toFunctor) : F = G :=
  congrArg (Functor.toCatHom) h

/--
The equivalence between the type of functors between two categories and
the type of 1-morphisms in Cat between the objects corresponding to those categories.
-/
@[simps]
def _root_.CategoryTheory.Functor.equivCatHom (C D : Type u) [Category.{v} C] [Category.{v} D] :
    C ⥤ D ≃ ((Cat.of C) ⟶ (Cat.of D)) where
  toFun := Functor.toCatHom
  invFun := Cat.Hom.toFunctor
  left_inv _ := rfl
  right_inv _ := rfl

/--
The equivalence between the type of 1-morphisms in Cat between two objects
and the type of functors between the categories corresponding to those objects.
-/
@[simps! apply symm_apply]
def Hom.equivFunctor (C D : Cat.{v, u}) :
    (C ⟶ D) ≃ C ⥤ D := (equivCatHom _ _).symm

#adaptation_note /-- Removed `private`:
`ofNatTrans` was marked `private` in #31807,
but we have removed this when disabling `set_option backward.privateInPublic` as a global option. -/
/--
The type of 2-morphisms in the bicategory of categories `Cat`.
This is a wrapper around `NatTrans` to prevent defeq-abuse.
-/
structure Hom₂ {C D : Cat.{v, u}} (F G : C ⟶ D) where
  ofNatTrans ::
  /-- The natural transformation underlying a 2-morphism in `Cat` -/
  toNatTrans : F.toFunctor ⟶ G.toFunctor

namespace Hom

instance instQuiver {C D : Cat.{v, u}} : Quiver (C ⟶ D) where
  Hom F G := Hom₂ F G

/-- The 2-morphism in `Cat` corresponding to a natural transformation between functors. -/
@[simps]
def _root_.CategoryTheory.NatTrans.toCatHom₂ {C D : Type u} [Category.{v} C]
    [Category.{v} D] {F G : C ⥤ D} (η : F ⟶ G) : F.toCatHom ⟶ G.toCatHom where
  toNatTrans := η

instance instCategory {X Y : Cat.{v, u}} : Category (X ⟶ Y) where
  id F := NatTrans.toCatHom₂ (𝟙 F.toFunctor)
  comp η₁ η₂ := NatTrans.toCatHom₂ (η₁.toNatTrans ≫ η₂.toNatTrans)
  id_comp η := congrArg (NatTrans.toCatHom₂) (Category.id_comp η.toNatTrans)
  comp_id η := congrArg (NatTrans.toCatHom₂) (Category.comp_id η.toNatTrans)
  assoc η₁ η₂ η₃ :=
    congrArg (NatTrans.toCatHom₂) (Category.assoc η₁.toNatTrans η₂.toNatTrans η₃.toNatTrans)

@[simp, push_cast]
lemma _root_.CategoryTheory.NatTrans.toCatHom₂_id {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) :
    (𝟙 F : F ⟶ F).toCatHom₂ = 𝟙 F.toCatHom := rfl

@[simp, push_cast]
lemma _root_.CategoryTheory.NatTrans.toCatHom₂_comp {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G H : C ⥤ D} (η₁ : F ⟶ G) (η₂ : G ⟶ H) :
    (η₁ ≫ η₂).toCatHom₂ = η₁.toCatHom₂ ≫ η₂.toCatHom₂ := rfl

@[simp, push_cast]
lemma toNatTrans_id {C D : Cat.{v, u}} (F : C ⟶ D) :
  (𝟙 F : F ⟶ F).toNatTrans = 𝟙 (F.toFunctor) := rfl

@[simp, push_cast]
lemma toNatTrans_comp {C D : Cat.{v, u}} {F G H : C ⟶ D} (η₁ : F ⟶ G) (η₂ : G ⟶ H) :
  (η₁ ≫ η₂).toNatTrans = η₁.toNatTrans ≫ η₂.toNatTrans := rfl

@[ext]
lemma _root_.CategoryTheory.Cat.Hom₂.ext {C D : Cat.{v, u}} {F G : C ⟶ D} {η₁ η₂ : F ⟶ G}
    (h : η₁.toNatTrans = η₂.toNatTrans) : η₁ = η₂ := congr($(h).toCatHom₂)

/-- The 2-iso in Cat corresponding to a natural isomorphism. -/
@[simps]
def isoMk {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤ D} (e : F ≅ G) :
    F.toCatHom ≅ G.toCatHom where
  hom := e.hom.toCatHom₂
  inv := e.inv.toCatHom₂
  hom_inv_id := congrArg NatTrans.toCatHom₂ e.hom_inv_id
  inv_hom_id := congrArg NatTrans.toCatHom₂ e.inv_hom_id

/-- The natural isomorphism corresponding to a 2-iso in `Cat` -/
@[simps]
def toNatIso {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) : F.toFunctor ≅ G.toFunctor where
  hom := e.hom.toNatTrans
  inv := e.inv.toNatTrans
  hom_inv_id := congrArg Hom₂.toNatTrans e.hom_inv_id
  inv_hom_id := congrArg Hom₂.toNatTrans e.inv_hom_id

@[simp]
lemma isoMk_toNatIso {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) :
    isoMk (Hom.toNatIso e) = e := rfl

@[simp]
lemma toNatIso_isoMk {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤ D} (e : F ≅ G) :
    Hom.toNatIso (isoMk e) = e := rfl

instance {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) :
    IsIso e.hom.toNatTrans :=
  (toNatIso e).isIso_hom

instance {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) :
    IsIso e.inv.toNatTrans :=
  (toNatIso e).isIso_inv

@[reassoc (attr := simp)]
lemma hom_inv_id_toNatTrans {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) :
    e.hom.toNatTrans ≫ e.inv.toNatTrans = 𝟙 _ :=
  (toNatIso e).hom_inv_id

@[reassoc (attr := simp)]
lemma inv_hom_id_toNatTrans {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) :
    e.inv.toNatTrans ≫ e.hom.toNatTrans = 𝟙 _ :=
  (toNatIso e).inv_hom_id

@[reassoc (attr := simp)]
lemma hom_inv_id_toNatTrans_app {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) (A : X) :
    e.hom.toNatTrans.app A ≫ e.inv.toNatTrans.app A = 𝟙 _ :=
  (toNatIso e).hom_inv_id_app A

@[reassoc (attr := simp)]
lemma inv_hom_id_toNatTrans_app {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) (A : X) :
    e.inv.toNatTrans.app A ≫ e.hom.toNatTrans.app A = 𝟙 _ :=
  (toNatIso e).inv_hom_id_app A

end Hom

end

/-- Bicategory structure on `Cat` -/
instance bicategory : Bicategory.{max v u, max v u} Cat.{v, u} where
  id C := (𝟭 C).toCatHom
  comp F G := (F.toFunctor ⋙ G.toFunctor).toCatHom
  homCategory := fun _ _ => Hom.instCategory
  whiskerLeft F _ _ η := (Functor.whiskerLeft F.toFunctor η.toNatTrans).toCatHom₂
  whiskerRight η H := (Functor.whiskerRight η.toNatTrans H.toFunctor).toCatHom₂
  associator F G H := Hom.isoMk
    (Functor.associator F.toFunctor G.toFunctor H.toFunctor)
  leftUnitor F := Hom.isoMk (Functor.leftUnitor F.toFunctor)
  rightUnitor F := Hom.isoMk (Functor.rightUnitor F.toFunctor)

/-- `Cat` is a strict bicategory. -/
instance bicategory.strict : Bicategory.Strict Cat.{v, u} where
  id_comp {C} {D} F := by cases F; rfl
  comp_id {C} {D} F := by cases F; rfl
  assoc := by intros; rfl

/-- Category structure on `Cat` -/
instance category : LargeCategory.{max v u} Cat.{v, u} :=
  StrictBicategory.category Cat.{v, u}

@[simp, push_cast]
lemma Hom.id_toFunctor {C : Cat.{v, u}} : (𝟙 C : C ⟶ C).toFunctor = 𝟭 C := rfl

@[simp]
theorem Hom.id_obj {C : Cat.{v, u}} (X : C) : (𝟙 C : C ⟶ C).toFunctor.obj X = X := by
  simp

@[simp]
theorem Hom.id_map {C : Cat.{v, u}} {X Y : C} (f : X ⟶ Y) : (𝟙 C : C ⟶ C).toFunctor.map f = f := by
  simp

@[simp, push_cast]
lemma Hom.comp_toFunctor {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) :
  (F ≫ G).toFunctor = F.toFunctor ⋙ G.toFunctor := rfl

@[simp]
theorem Hom.comp_obj {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) (X : C) :
    (F ≫ G).toFunctor.obj X = G.toFunctor.obj (F.toFunctor.obj X) := by
  simp

@[simp]
theorem Hom.comp_map {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) {X Y : C} (f : X ⟶ Y) :
    (F ≫ G).toFunctor.map f = G.toFunctor.map (F.toFunctor.map f) := by
  simp

@[simp]
theorem Hom₂.id_app {C D : Cat.{v, u}} (F : C ⟶ D) (X : C) :
    (𝟙 F : F ⟶ F).toNatTrans.app X = 𝟙 (F.toFunctor.obj X) := by
  simp

@[simp, reassoc]
theorem Hom₂.comp_app {C D : Cat.{v, u}} {F G H : C ⟶ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
    (α ≫ β).toNatTrans.app X = α.toNatTrans.app X ≫ β.toNatTrans.app X := rfl

@[simp]
theorem Hom₂.eqToHom_toNatTrans {C D : Cat.{v, u}} {F G : C ⟶ D} (h : F = G) :
  (eqToHom h).toNatTrans = eqToHom congr(($h).toFunctor) := by cases h; simp

theorem eqToHom_app {C D : Cat.{v, u}} (F G : C ⟶ D) (h : F = G) (X : C) :
    (eqToHom h).toNatTrans.app X = eqToHom congr(($h).toFunctor.obj X) := by
  simp

@[simp, push_cast]
lemma whiskerLeft_toNatTrans {C D E : Cat.{v, u}} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H) :
  (F ◁ η).toNatTrans = F.toFunctor.whiskerLeft η.toNatTrans := rfl

@[simp]
lemma whiskerLeft_app {C D E : Cat.{v, u}} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H) (X : C) :
    (F ◁ η).toNatTrans.app X = η.toNatTrans.app (F.toFunctor.obj X) := by simp

@[simp, push_cast]
lemma whiskerRight_toNatTrans {C D E : Cat.{v, u}} {F G : C ⟶ D} (H : D ⟶ E) (η : F ⟶ G) :
    (η ▷ H).toNatTrans = Functor.whiskerRight η.toNatTrans H.toFunctor := rfl

@[simp]
lemma whiskerRight_app {C D E : Cat.{v, u}} {F G : C ⟶ D} (H : D ⟶ E) (η : F ⟶ G) (X : C) :
    (η ▷ H).toNatTrans.app X = H.toFunctor.map (η.toNatTrans.app X) := by simp

@[simp, push_cast]
lemma Hom.toNatIso_leftUnitor {B C : Cat.{v, u}} (F : B ⟶ C) :
    Hom.toNatIso (λ_ F) = F.toFunctor.leftUnitor := rfl

@[simp, push_cast]
lemma leftUnitor_hom_toNatTrans {B C : Cat.{v, u}} (F : B ⟶ C) :
    (λ_ F).hom.toNatTrans = (F.toFunctor.leftUnitor).hom := rfl

@[simp, push_cast]
lemma leftUnitor_inv_toNatTrans {B C : Cat.{v, u}} (F : B ⟶ C) :
    (λ_ F).inv.toNatTrans = (F.toFunctor.leftUnitor).inv := rfl

lemma leftUnitor_hom_app {B C : Cat} (F : B ⟶ C) (X : B) :
    (λ_ F).hom.toNatTrans.app X = eqToHom (by simp) := by simp

lemma leftUnitor_inv_app {B C : Cat} (F : B ⟶ C) (X : B) :
    (λ_ F).inv.toNatTrans.app X = eqToHom (by simp) := by simp

@[simp, push_cast]
lemma Hom.toNatIso_rightUnitor {B C : Cat.{v, u}} (F : B ⟶ C) :
    Hom.toNatIso (ρ_ F) = eqToIso rfl ≪≫ F.toFunctor.rightUnitor ≪≫ eqToIso rfl := by simp; rfl

@[simp, push_cast]
lemma rightUnitor_hom_toNatTrans {B C : Cat.{v, u}} (F : B ⟶ C) :
    (ρ_ F).hom.toNatTrans = (F.toFunctor.rightUnitor).hom := rfl

@[simp, push_cast]
lemma rightUnitor_inv_toNatTrans {B C : Cat.{v, u}} (F : B ⟶ C) :
    (ρ_ F).inv.toNatTrans = (F.toFunctor.rightUnitor).inv := rfl

lemma rightUnitor_hom_app {B C : Cat.{v, u}} (F : B ⟶ C) (X : B) :
    (ρ_ F).hom.toNatTrans.app X = eqToHom (by simp) := by simp

lemma rightUnitor_inv_app {B C : Cat.{v, u}} (F : B ⟶ C) (X : B) :
    (ρ_ F).inv.toNatTrans.app X = eqToHom (by simp) := by simp

@[simp, push_cast]
lemma Hom.toNatIso_associator {B C D E : Cat.{v, u}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) :
    Hom.toNatIso (α_ F G H) = Functor.associator F.toFunctor G.toFunctor H.toFunctor := rfl

@[simp, push_cast]
lemma associator_hom_toNatTrans {B C D E : Cat.{v, u}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) :
    (α_ F G H).hom.toNatTrans = (Functor.associator F.toFunctor G.toFunctor H.toFunctor).hom := rfl

@[simp, push_cast]
lemma associator_inv_toNatTrans {B C D E : Cat.{v, u}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) :
    (α_ F G H).inv.toNatTrans = (Functor.associator F.toFunctor G.toFunctor H.toFunctor).inv := rfl

lemma associator_hom_app {B C D E : Cat} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B) :
    (α_ F G H).hom.toNatTrans.app X = eqToHom (by simp) := by simp

lemma associator_inv_app {B C D E : Cat} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B) :
    (α_ F G H).inv.toNatTrans.app X = eqToHom (by simp) := by simp

/-- The identity in the category of categories equals the identity functor. -/
theorem id_eq_id (X : Cat.{u, v}) : (𝟙 X : X ⟶ X).toFunctor = 𝟭 X := rfl

/-- Composition in the category of categories equals functor composition. -/
theorem comp_eq_comp {X Y Z : Cat} (F : X ⟶ Y) (G : Y ⟶ Z) :
    (F ≫ G).toFunctor = F.toFunctor ⋙ G.toFunctor := rfl

@[simp] theorem of_α (C) [Category* C] : (of C).α = C := rfl

@[simp] theorem coe_of (C : Cat.{v, u}) : Cat.of C = C := rfl

/-- Functor that gets the set of objects of a category. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Cat.{v, u} ⥤ Type u where
  obj C := C
  map F := F.toFunctor.obj

/-- See through the defeq `objects.obj X = X`. -/
instance (X : Cat.{v, u}) : Category (objects.obj X) := inferInstanceAs <| Category X

section

attribute [local simp] eqToHom_map

/-- Any isomorphism in `Cat` induces an equivalence of the underlying categories. -/
def equivOfIso {C D : Cat} (γ : C ≅ D) : C ≌ D where
  functor := γ.hom.toFunctor
  inverse := γ.inv.toFunctor
  unitIso := eqToIso <| congr($(γ.hom_inv_id).toFunctor).symm
  counitIso := eqToIso <| congr($(γ.inv_hom_id).toFunctor)

/-- Under certain hypotheses, an equivalence of categories actually
defines an isomorphism in `Cat`. -/
@[simps]
def isoOfEquiv {C D : Cat.{v, u}} (e : C ≌ D)
    (h₁ : ∀ (X : C), e.inverse.obj (e.functor.obj X) = X)
    (h₂ : ∀ (Y : D), e.functor.obj (e.inverse.obj Y) = Y)
    (h₃ : ∀ (X : C), e.unitIso.hom.app X = eqToHom (h₁ X).symm := by cat_disch)
    (h₄ : ∀ (Y : D), e.counitIso.hom.app Y = eqToHom (h₂ Y) := by cat_disch) :
    C ≅ D where
  hom := e.functor.toCatHom
  inv := e.inverse.toCatHom
  hom_inv_id := congrArg Functor.toCatHom
    (Functor.ext_of_iso e.unitIso (fun X ↦ (h₁ X).symm) h₃).symm
  inv_hom_id := congrArg Functor.toCatHom (Functor.ext_of_iso e.counitIso h₂ h₄)

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
    ext
    simp only [Cat.of_α, toCatHom_toFunctor, Cat.Hom.id_toFunctor]
    fapply Functor.ext
    · simp
    · intro X Y f
      cases f
      simp only [Discrete.functor_obj_eq_as, Function.comp_apply, types_id_apply, Discrete.mk_as,
        id_obj, eqToHom_refl, Functor.id_map, Category.comp_id, Category.id_comp]
      apply ULift.ext
      cat_disch
  map_comp f g := by
    ext
    simp only [Cat.of_α, toCatHom_toFunctor, Cat.Hom.comp_toFunctor]
    apply Functor.ext
    cat_disch

instance : Functor.Faithful typeToCat.{u} where
  map_injective {_X} {_Y} _f _g h :=
    funext (fun x => congrArg (Discrete.as) (Functor.congr_obj congr(($h).toFunctor) ⟨x⟩))

instance : Functor.Full typeToCat.{u} where
  map_surjective F := ⟨Discrete.as ∘ F.toFunctor.obj ∘ Discrete.mk, by
    ext
    apply Functor.ext
    · intro x y f
      dsimp
      apply ULift.ext
      cat_disch
    · rintro ⟨x⟩
      apply Discrete.ext
      rfl⟩

end CategoryTheory
