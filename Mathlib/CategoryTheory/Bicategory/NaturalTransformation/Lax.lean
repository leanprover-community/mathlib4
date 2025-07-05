/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne, Robin Carlier
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Lax
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Transformations between lax functors

Just as there are natural transformations between functors, there are transformations
between lax functors. The equality in the naturality condition of a natural transformation gets
replaced by a specified 2-morphism. Now, there are three possible types of transformations (between
lax functors):
* Lax natural transformations;
* OpLax natural transformations;
* Strong natural transformations.
These differ in the direction (and invertibility) of the 2-morphisms involved in the naturality
condition.

## Main definitions

* `Lax.LaxTrans F G`: lax transformations between lax functors `F` and `G`. The naturality
  condition is given by a 2-morphism `app a ≫ G.map f ⟶ F.map f ≫ app b` for each 1-morphism
  `f : a ⟶ b`.
* `Lax.StrongTrans F G`: Strong transformations between lax functors `F` and `G`.

Using these, we define two `CategoryStruct` (scoped) instances on `LaxFunctor B C`, one in the
`Lax.LaxTrans` namespace and one in the `Lax.StrongTrans` namespace. The arrows in these
CategoryStruct's are given by lax transformations and strong transformations respectively.

We also provide API for going between lax transformations and strong transformations:
* `Lax.StrongCore F G`: a structure on an lax transformation between lax functors that
promotes it to a strong transformation.
* `Lax.mkOfLax η η'`: given an lax transformation `η` such that each component
  2-morphism is an isomorphism, `mkOfLax` gives the corresponding strong transformation.

# TODO
This file could also include oplax transformations between lax functors.

## References
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055),
section 4.2.

-/

namespace CategoryTheory.Lax

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- If `η` is an lax transformation between `F` and `G`, we have a 1-morphism
`η.app a : F.obj a ⟶ G.obj a` for each object `a : B`. We also have a 2-morphism
`η.naturality f : app a ≫ G.map f ⟶ F.map f ≫ app b` for each 1-morphism `f : a ⟶ b`.
These 2-morphisms satisfies the naturality condition, and preserve the identities and
the compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
structure LaxTrans (F G : LaxFunctor B C) where
  /-- The component 1-morphisms of an lax transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-morphisms underlying the lax naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : app a ≫ G.map f ⟶ F.map f ≫ app b
  /-- Naturality of the lax naturality constraint. -/
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
     naturality f ≫ F.map₂ η ▷ app b = app a ◁ G.map₂ η ≫ naturality g := by
    aesop_cat
  /-- Lax unity. -/
  naturality_id (a : B) :
      app a ◁ G.mapId a ≫ naturality (𝟙 a) =
        (ρ_ (app a)).hom ≫ (λ_ (app a)).inv ≫ F.mapId a ▷ app a := by
    aesop_cat
  /-- Lax functoriality. -/
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      app a ◁ G.mapComp f g ≫ naturality (f ≫ g) =
      (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom ≫
        F.map f ◁ naturality g ≫ (α_ _ _ _).inv ≫ F.mapComp f g ▷ app c := by
    aesop_cat

attribute [reassoc (attr := simp)] LaxTrans.naturality_naturality LaxTrans.naturality_id
  LaxTrans.naturality_comp

namespace LaxTrans

variable {F G H : LaxFunctor B C} (η : LaxTrans F G) (θ : LaxTrans G H)

variable (F) in
/-- The identity lax transformation. -/
def id : LaxTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {_ _} f := (λ_ (F.map f)).hom ≫ (ρ_ (F.map f)).inv

instance : Inhabited (LaxTrans F F) :=
  ⟨id F⟩

/-- Auxiliary definition for `vComp`. -/
abbrev vCompApp (a : B) : F.obj a ⟶ H.obj a :=
  η.app a ≫ θ.app a

/-- Auxiliary definition for `vComp`. -/
abbrev vCompNaturality {a b : B} (f : a ⟶ b) :
    (η.app a ≫ θ.app a) ≫ H.map f ⟶ F.map f ≫ η.app b ≫ θ.app b :=
  (α_ _ _ _).hom ≫ η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv ≫
    η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom

theorem vComp_naturality_naturality {a b : B} {f g : a ⟶ b} (β : f ⟶ g) :
    η.vCompNaturality θ f ≫ F.map₂ β ▷ η.vCompApp θ b =
      η.vCompApp θ a ◁ H.map₂ β ≫ η.vCompNaturality θ g :=
  calc
    _ = 𝟙 _ ⊗≫ η.app a ◁ θ.naturality f ⊗≫
          (η.naturality f ≫ F.map₂ β ▷ η.app b) ▷ θ.app b ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.naturality f ≫ G.map₂ β ▷ θ.app b) ⊗≫
          η.naturality g ▷ θ.app b ⊗≫ 𝟙 _ := by
      rw [naturality_naturality]
      bicategory
    _ = _ := by
      rw [naturality_naturality]
      bicategory

theorem vComp_naturality_id (a : B) :
    η.vCompApp θ a ◁ H.mapId a ≫ η.vCompNaturality θ (𝟙 a) =
      (ρ_ (η.vCompApp θ a)).hom ≫ (λ_ (η.vCompApp θ a)).inv ≫ F.mapId a ▷ η.vCompApp θ a :=
  calc
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.app a ◁ H.mapId a ≫ θ.naturality (𝟙 a)) ⊗≫
          η.naturality (𝟙 a) ▷ θ.app a ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (η.app a ◁ G.mapId a ≫ η.naturality (𝟙 a)) ▷ θ.app a ⊗≫ 𝟙 _ := by
      rw [naturality_id]
      bicategory
    _ = _ := by
      rw [naturality_id]
      bicategory

theorem vComp_naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    η.vCompApp θ a ◁ H.mapComp f g ≫ η.vCompNaturality θ (f ≫ g) =
      (α_ (η.vCompApp θ a) (H.map f) (H.map g)).inv ≫
        η.vCompNaturality θ f ▷ H.map g ≫
          (α_ (F.map f) (η.vCompApp θ b) (H.map g)).hom ≫
            F.map f ◁ η.vCompNaturality θ g ≫
              (α_ (F.map f) (F.map g) (η.vCompApp θ c)).inv ≫ F.mapComp f g ▷ η.vCompApp θ c :=
  calc
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.app a ◁ H.mapComp f g ≫ θ.naturality (f ≫ g)) ⊗≫
          η.naturality (f ≫ g) ▷ θ.app c ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.naturality f ▷ (H.map g) ⊗≫ G.map f ◁ θ.naturality g) ⊗≫
          (η.app a ◁ G.mapComp f g ≫ η.naturality (f ≫ g)) ▷ θ.app c ⊗≫ 𝟙 _ := by
      rw [naturality_comp θ]
      bicategory
    _ = 𝟙 _ ⊗≫ η.app a ◁ θ.naturality f ▷ H.map g ⊗≫
          ((η.app a ≫ G.map f) ◁ θ.naturality g ≫ η.naturality f ▷ (G.map g ≫ θ.app c)) ⊗≫
            F.map f ◁ η.naturality g ▷ θ.app c ⊗≫
              F.mapComp f g ▷ η.app c ▷ θ.app c ⊗≫ 𝟙 _ := by
      rw [naturality_comp η]
      bicategory
    _ = _ := by
      rw [whisker_exchange]
      bicategory

/-- Vertical composition of lax transformations. -/
@[simps]
def vComp (η : LaxTrans F G) (θ : LaxTrans G H) : LaxTrans F H where
  app a := vCompApp η θ a
  naturality := vCompNaturality η θ
  naturality_naturality := vComp_naturality_naturality η θ
  naturality_id := vComp_naturality_id η θ
  naturality_comp := vComp_naturality_comp η θ

/-- `CategoryStruct` on `LaxFunctor B C` where the (1-)morphisms are given by lax
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
scoped instance : CategoryStruct (LaxFunctor B C) where
  Hom := LaxTrans
  id := LaxTrans.id
  comp := LaxTrans.vComp

end LaxTrans

/-- A strong natural transformation between lax functors `F` and `G` is a natural transformation
that is "natural up to 2-isomorphisms".

More precisely, it consists of the following:
* a 1-morphism `η.app a : F.obj a ⟶ G.obj a` for each object `a : B`.
* a 2-isomorphism `η.naturality f : app a ≫ G.map f ≅ F.map f ≫ app b` for each 1-morphism
`f : a ⟶ b`.
* These 2-isomorphisms satisfy the naturality condition, and preserve the identities and the
  compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
structure StrongTrans (F G : LaxFunctor B C) where
  app (a : B) : F.obj a ⟶ G.obj a
  naturality {a b : B} (f : a ⟶ b) : app a ≫ G.map f ≅ F.map f ≫ app b
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
     (naturality f).hom ≫ F.map₂ η ▷ app b = app a ◁ G.map₂ η ≫ (naturality g).hom := by
    aesop_cat
  /-- Lax unity. -/
  naturality_id (a : B) :
      app a ◁ G.mapId a ≫ (naturality (𝟙 a)).hom =
        (ρ_ (app a)).hom ≫ (λ_ (app a)).inv ≫ F.mapId a ▷ app a := by
    aesop_cat
  /-- Lax functoriality. -/
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      app a ◁ G.mapComp f g ≫ (naturality (f ≫ g)).hom =
      (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom ≫
        F.map f ◁ (naturality g).hom ≫ (α_ _ _ _).inv ≫ F.mapComp f g ▷ app c := by
    aesop_cat

attribute [nolint docBlame] CategoryTheory.Lax.StrongTrans.app
  CategoryTheory.Lax.StrongTrans.naturality

attribute [reassoc (attr := simp)] StrongTrans.naturality_naturality
  StrongTrans.naturality_id StrongTrans.naturality_comp

/-- A structure on an lax transformation that promotes it to a strong transformation.

See `Pseudofunctor.StrongTrans.mkOfLax`. -/
structure LaxTrans.StrongCore {F G : LaxFunctor B C} (η : F ⟶ G) where
  /-- The underlying 2-isomorphisms of the naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : η.app a ≫ G.map f ≅ F.map f ≫ η.app b
  /-- The 2-isomorphisms agree with the underlying 2-morphism of the lax transformation. -/
  naturality_hom {a b : B} (f : a ⟶ b) : (naturality f).hom = η.naturality f := by aesop_cat

attribute [simp] LaxTrans.StrongCore.naturality_hom

namespace StrongTrans

/-- The underlying lax natural transformation of a strong natural transformation. -/
@[simps]
def toLax {F G : LaxFunctor B C} (η : StrongTrans F G) : LaxTrans F G where
  app := η.app
  naturality f := (η.naturality f).hom

/-- Construct a strong natural transformation from an lax natural transformation whose
naturality 2-morphism is an isomorphism. -/
def mkOfLax {F G : LaxFunctor B C} (η : LaxTrans F G) (η' : LaxTrans.StrongCore η) :
    StrongTrans F G where
  app := η.app
  naturality := η'.naturality

/-- Construct a strong natural transformation from an lax natural transformation whose
naturality 2-morphism is an isomorphism. -/
noncomputable def mkOfLax' {F G : LaxFunctor B C} (η : LaxTrans F G)
    [∀ a b (f : a ⟶ b), IsIso (η.naturality f)] : StrongTrans F G where
  app := η.app
  naturality _ := asIso (η.naturality _)

variable (F : LaxFunctor B C)

/-- The identity strong natural transformation. -/
@[simps!]
def id : StrongTrans F F :=
  mkOfLax (LaxTrans.id F) { naturality := fun f ↦ (λ_ (F.map f)) ≪≫ (ρ_ (F.map f)).symm }

@[simp]
lemma id.toLax : (id F).toLax = LaxTrans.id F :=
  rfl

instance : Inhabited (StrongTrans F F) :=
  ⟨id F⟩

variable {F} {G H : LaxFunctor B C} (η : StrongTrans F G) (θ : StrongTrans G H)

/-- Vertical composition of strong natural transformations. -/
@[simps!]
def vComp : StrongTrans F H :=
  mkOfLax (LaxTrans.vComp η.toLax θ.toLax)
    { naturality := fun {a b} f ↦
        (α_ _ _ _) ≪≫ whiskerLeftIso (η.app a) (θ.naturality f) ≪≫ (α_ _ _ _).symm ≪≫
        whiskerRightIso (η.naturality f) (θ.app b) ≪≫ (α_ _ _ _) }

/-- `CategoryStruct` on `LaxFunctor B C` where the (1-)morphisms are given by strong
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
scoped instance categoryStruct : CategoryStruct (LaxFunctor B C) where
  Hom := StrongTrans
  id := StrongTrans.id
  comp := StrongTrans.vComp

end StrongTrans

end CategoryTheory.Lax
