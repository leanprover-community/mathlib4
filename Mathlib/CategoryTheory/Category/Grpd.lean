/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Bicategory.Functor.Strict

/-!
# Category of groupoids

This file contains the definition of the category `Grpd` of all groupoids.
In this category objects are groupoids and morphisms are functors
between these groupoids.

We also provide two “forgetting” functors: `objects : Grpd ⥤ Type`
and `forgetToCat : Grpd ⥤ Cat`.

## Implementation notes

Though `Grpd` is not a concrete category, we use `Bundled` to define
its carrier type.
-/

@[expose] public section

assert_not_exists MonoidWithZero

universe v u

namespace CategoryTheory

open Bicategory Functor

-- intended to be used with explicit universe parameters
/-- Category of groupoids -/
@[nolint checkUnivs]
def Grpd :=
  Bundled Groupoid.{v, u}

namespace Grpd

instance : Inhabited Grpd :=
  ⟨Bundled.of (SingleObj PUnit)⟩


instance str' (C : Grpd.{v, u}) : Groupoid.{v, u} C.α :=
  C.str

instance : CoeSort Grpd Type* :=
  Bundled.coeSort

/-- Construct a bundled `Grpd` from the underlying type and the typeclass `Groupoid`. -/
def of (C : Type u) [Groupoid.{v} C] : Grpd.{v, u} :=
  Bundled.of C

@[simp] theorem of_α (C) [Groupoid C] : (of C).α = C := rfl

@[simp]
theorem coe_of (C : Type u) [Groupoid C] : (of C : Type u) = C :=
  rfl

/-- Bicategory structure on `Grpd` -/
instance bicategory : Bicategory.{max v u, max v u} Grpd.{v, u} where
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

/-- `Grpd` is a strict bicategory. -/
instance bicategory.strict : Bicategory.Strict Grpd.{v, u} where
  id_comp {C} {D} F := by cases F; rfl
  comp_id {C} {D} F := by cases F; rfl
  assoc := by intros; rfl

/-- Category structure on `Grpd` -/
instance category : LargeCategory.{max v u} Grpd.{v, u} :=
  StrictBicategory.category Grpd.{v, u}

@[ext]
theorem natTrans_ext {C D : Grpd} {F G : C ⟶ D} {η θ : F ⟶ G} (h : η.app = θ.app) :
    η = θ := NatTrans.ext' h

@[simp]
theorem id_obj {C : Grpd} (X : C) : (𝟙 C : C ⥤ C).obj X = X :=
  rfl

@[simp]
theorem id_map {C : Grpd} {X Y : C} (f : X ⟶ Y) : (𝟙 C : C ⥤ C).map f = f :=
  rfl

@[simp]
theorem comp_obj {C D E : Grpd} (F : C ⟶ D) (G : D ⟶ E) (X : C) :
    (F ≫ G).obj X = G.obj (F.obj X) :=
  rfl

@[simp]
theorem comp_map {C D E : Grpd} (F : C ⟶ D) (G : D ⟶ E) {X Y : C} (f : X ⟶ Y) :
    (F ≫ G).map f = G.map (F.map f) :=
  rfl

@[simp]
theorem id_app {C D : Grpd} (F : C ⟶ D) (X : C) : (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X) := rfl

@[simp]
theorem comp_app {C D : Grpd} {F G H : C ⟶ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
    (α ≫ β).app X = α.app X ≫ β.app X := rfl

@[simp]
lemma whiskerLeft_app {C D E : Grpd} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H) (X : C) :
    (F ◁ η).app X = η.app (F.obj X) :=
  rfl

@[simp]
lemma whiskerRight_app {C D E : Grpd} {F G : C ⟶ D} (H : D ⟶ E) (η : F ⟶ G) (X : C) :
    (η ▷ H).app X = H.map (η.app X) :=
  rfl

@[simp]
theorem eqToHom_app {C D : Grpd} (F G : C ⟶ D) (h : F = G) (X : C) :
    (eqToHom h).app X = eqToHom (Functor.congr_obj h X) :=
  CategoryTheory.eqToHom_app h X

lemma leftUnitor_hom_app {B C : Grpd} (F : B ⟶ C) (X : B) : (λ_ F).hom.app X = eqToHom (by simp) :=
  rfl

lemma leftUnitor_inv_app {B C : Grpd} (F : B ⟶ C) (X : B) : (λ_ F).inv.app X = eqToHom (by simp) :=
  rfl

lemma rightUnitor_hom_app {B C : Grpd} (F : B ⟶ C) (X : B) :
    (ρ_ F).hom.app X = eqToHom (by simp) :=
  rfl

lemma rightUnitor_inv_app {B C : Grpd} (F : B ⟶ C) (X : B) :
    (ρ_ F).inv.app X = eqToHom (by simp) :=
  rfl

lemma associator_hom_app {B C D E : Grpd} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B) :
    (α_ F G H).hom.app X = eqToHom (by simp) :=
  rfl

lemma associator_inv_app {B C D E : Grpd} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B) :
    (α_ F G H).inv.app X = eqToHom (by simp) :=
  rfl

/-- The identity in the category of groupoids equals the identity functor. -/
theorem id_eq_id (X : Grpd) : 𝟙 X = 𝟭 X := rfl

/-- Composition in the category of groupoids equals functor composition. -/
theorem comp_eq_comp {X Y Z : Grpd} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙ G := rfl

section

attribute [-simp] eqToIso_refl

/-- Forgetting pseudofunctor to `Cat`. -/
def forgetToCat : StrictPseudofunctor Grpd.{v, u} Cat.{v, u} :=
  StrictPseudofunctor.mk''
    { obj C := Cat.of C
      map := id
      map₂ := id }

end

instance forgetToCat_full : forgetToCat.toFunctor.Full where map_surjective f := ⟨f, rfl⟩

instance forgetToCat_faithful : forgetToCat.toFunctor.Faithful where

/-- Functor that gets the set of objects of a groupoid. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Grpd.{v, u} ⥤ Type u where
  obj := Bundled.α
  map F := F.obj

@[deprecated (since := "2025-09-04")] alias hom_to_functor := comp_eq_comp

@[deprecated "Deprecated in favor of using `CategoryTheory.Grpd.id_eq_id`" (since := "2025-09-04")]
theorem id_to_functor {C : Grpd.{v, u}} : 𝟭 C = 𝟙 C :=
  rfl

section Products

/-- Construct the product over an indexed family of groupoids, as a fan. -/
def piLimitFan ⦃J : Type u⦄ (F : J → Grpd.{u, u}) : Limits.Fan F :=
  Limits.Fan.mk (@of (∀ j : J, F j) _) fun j => CategoryTheory.Pi.eval _ j

/-- The product fan over an indexed family of groupoids, is a limit cone. -/
def piLimitFanIsLimit ⦃J : Type u⦄ (F : J → Grpd.{u, u}) : Limits.IsLimit (piLimitFan F) :=
  Limits.mkFanLimit (piLimitFan F) (fun s => Functor.pi' fun j => s.proj j)
    (by
      intros
      dsimp only [piLimitFan]
      simp [comp_eq_comp])
    (by
      intro s m w
      apply Functor.pi_ext
      intro j; specialize w j
      simpa)

instance has_pi : Limits.HasProducts.{u} Grpd.{u, u} :=
  Limits.hasProducts_of_limit_fans (by apply piLimitFan) (by apply piLimitFanIsLimit)

/-- The product of a family of groupoids is isomorphic
to the product object in the category of Groupoids -/
noncomputable def piIsoPi (J : Type u) (f : J → Grpd.{u, u}) : @of (∀ j, f j) _ ≅ ∏ᶜ f :=
  Limits.IsLimit.conePointUniqueUpToIso (piLimitFanIsLimit f)
    (Limits.limit.isLimit (Discrete.functor f))

@[simp]
theorem piIsoPi_hom_π (J : Type u) (f : J → Grpd.{u, u}) (j : J) :
    (piIsoPi J f).hom ≫ Limits.Pi.π f j = CategoryTheory.Pi.eval _ j := by
  simp [piIsoPi]
  rfl

end Products

end Grpd

end CategoryTheory
