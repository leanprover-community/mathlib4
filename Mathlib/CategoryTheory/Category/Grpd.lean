/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Bicategory.InducedBicategory

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

open Bicategory InducedBicategory

-- intended to be used with explicit universe parameters
/-- Bicategory of groupoids. -/
@[nolint checkUnivs]
structure Grpd where
  /-- Construct a bundled `Grpd` from the underlying type and the typeclass `Groupoid`. -/
  of ::
  carrier : Type u
  [str : Groupoid.{v} carrier]

attribute [instance] Grpd.str

initialize_simps_projections Grpd (-str)

namespace Grpd

instance : CoeSort Grpd Type* :=
  ⟨Grpd.carrier⟩

instance : Inhabited Grpd :=
  ⟨Grpd.of (SingleObj PUnit)⟩

@[simp] theorem of_α (C) [Groupoid C] : (of C).carrier = C := rfl

@[simp]
theorem coe_of (C : Type u) [Groupoid C] : (of C : Type u) = C :=
  rfl

@[simps!]
def toCat (C : Grpd) : Cat.{v, u} :=
  Cat.of C

/-- Bicategory structure on `Grpd` -/
@[simps!]
instance bicategory : Bicategory.{max v u, max v u} Grpd.{v, u} :=
  Bicategory.InducedBicategory.bicategory toCat

instance bicategory.strict : Bicategory.Strict Grpd.{v, u} :=
  inferInstanceAs (Bicategory.Strict (InducedBicategory _ toCat))

/-- Category structure on `Grpd` -/
instance category : LargeCategory.{max v u} Grpd.{v, u} :=
  StrictBicategory.category Grpd.{v, u}

-- TODO: fix following once Cat API PR lands

-- @[ext]
-- theorem natTrans_ext {C D : Grpd} {F G : C ⟶ D} {η θ : F ⟶ G} (h : η.hom.app = θ.hom.app) :
--     η = θ := NatTrans.ext' h

-- @[simp]
-- theorem id_obj {C : Grpd} (X : C) : (𝟙 C : C ⥤ C).obj X = X :=
--   rfl

-- @[simp]
-- theorem id_map {C : Grpd} {X Y : C} (f : X ⟶ Y) : (𝟙 C : C ⥤ C).map f = f :=
--   rfl

-- @[simp]
-- theorem comp_obj {C D E : Grpd} (F : C ⟶ D) (G : D ⟶ E) (X : C) :
--     (F ≫ G).obj X = G.obj (F.obj X) :=
--   rfl

-- @[simp]
-- theorem comp_map {C D E : Grpd} (F : C ⟶ D) (G : D ⟶ E) {X Y : C} (f : X ⟶ Y) :
--     (F ≫ G).map f = G.map (F.map f) :=
--   rfl

-- @[simp]
-- theorem id_app {C D : Grpd} (F : C ⟶ D) (X : C) : (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X) := rfl

-- @[simp]
-- theorem comp_app {C D : Grpd} {F G H : C ⟶ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
--     (α ≫ β).app X = α.app X ≫ β.app X := rfl

-- @[simp]
-- lemma whiskerLeft_app {C D E : Grpd} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H) (X : C) :
--     (F ◁ η).app X = η.app (F.obj X) :=
--   rfl

-- @[simp]
-- lemma whiskerRight_app {C D E : Grpd} {F G : C ⟶ D} (H : D ⟶ E) (η : F ⟶ G) (X : C) :
--     (η ▷ H).app X = H.map (η.app X) :=
--   rfl

-- @[simp]
-- theorem eqToHom_app {C D : Grpd} (F G : C ⟶ D) (h : F = G) (X : C) :
--     (eqToHom h).app X = eqToHom (Functor.congr_obj h X) :=
--   CategoryTheory.eqToHom_app h X

-- lemma leftUnitor_hom_app {B C : Grpd} (F : B ⟶ C) (X : B) : (λ_ F).hom.app X = eqToHom (by simp) :=
--   rfl

-- lemma leftUnitor_inv_app {B C : Grpd} (F : B ⟶ C) (X : B) : (λ_ F).inv.app X = eqToHom (by simp) :=
--   rfl

-- lemma rightUnitor_hom_app {B C : Grpd} (F : B ⟶ C) (X : B) :
--     (ρ_ F).hom.app X = eqToHom (by simp) :=
--   rfl

-- lemma rightUnitor_inv_app {B C : Grpd} (F : B ⟶ C) (X : B) :
--     (ρ_ F).inv.app X = eqToHom (by simp) :=
--   rfl

-- lemma associator_hom_app {B C D E : Grpd} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B) :
--     (α_ F G H).hom.app X = eqToHom (by simp) :=
--   rfl

-- lemma associator_inv_app {B C D E : Grpd} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B) :
--     (α_ F G H).inv.app X = eqToHom (by simp) :=
--   rfl

-- /-- The identity in the category of groupoids equals the identity functor. -/
-- theorem id_eq_id (X : Grpd) : 𝟙 X = 𝟭 X := rfl

-- /-- Composition in the category of groupoids equals functor composition. -/
-- theorem comp_eq_comp {X Y Z : Grpd} (F : X ⟶ Y) (G : Y ⟶ Z) : F ≫ G = F ⋙ G := rfl

section

/-- Forgetting pseudofunctor to `Cat`. -/
-- TODO: check simp lemmas after API PR lands
@[simps!]
abbrev forget : StrictPseudofunctor Grpd.{v, u} Cat.{v, u} :=
  InducedBicategory.forget

instance forget_full : forget.toFunctor.Full := InducedBicategory.forget_full

instance forget_faithful : forget.toFunctor.Faithful := InducedBicategory.forget_faithful

end

/-- Functor that gets the set of objects of a groupoid. It is not
called `forget`, because it is not a faithful functor. -/
@[simps]
def objects : Grpd.{v, u} ⥤ Type u where
  obj := Grpd.carrier
  map F := F.hom.obj

section Products

/-- Construct the product over an indexed family of groupoids, as a fan. -/
@[simps!]
def piLimitFan ⦃J : Type u⦄ (F : J → Grpd.{u, u}) : Limits.Fan F :=
  Limits.Fan.mk (@of (∀ j : J, F j) _) fun j =>
    InducedBicategory.mkHom <| CategoryTheory.Pi.eval _ j

-- TODO: fix following once API PR lands

/-- The product fan over an indexed family of groupoids, is a limit cone. -/
@[simps!]
def piLimitFanIsLimit ⦃J : Type u⦄ (F : J → Grpd.{u, u}) : Limits.IsLimit (piLimitFan F) :=
  Limits.mkFanLimit (piLimitFan F) (fun s => mkHom <| Functor.pi' fun j => (s.proj j).hom)
    (by
      intros
      dsimp [piLimitFan]
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
