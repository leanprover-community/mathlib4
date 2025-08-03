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
* `Lax.OplaxTrans F G`: oplax transformations between lax functors `F` and `G`. The naturality
  condition is given by a 2-morphism `F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism
  `f : a ⟶ b`.

Using these, we define two `CategoryStruct` (scoped) instances on `LaxFunctor B C`, one in the
`Lax.LaxTrans` namespace and one in the `Lax.OplaxTrans` namespace. The arrows in these
CategoryStruct's are given by lax transformations and strong transformations respectively.

## References
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055),
section 4.2.
-/

namespace CategoryTheory.Lax

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- If `η` is a lax transformation between `F` and `G`, we have a 1-morphism
`η.app a : F.obj a ⟶ G.obj a` for each object `a : B`. We also have a 2-morphism
`η.naturality f : app a ≫ G.map f ⟶ F.map f ≫ app b` for each 1-morphism `f : a ⟶ b`.
These 2-morphisms satisfy the naturality condition, and preserve the identities and
the compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
structure LaxTrans (F G : LaxFunctor B C) where
  /-- The component 1-morphisms of a lax transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-morphisms underlying the lax naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : app a ≫ G.map f ⟶ F.map f ≫ app b
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      naturality f ≫ F.map₂ η ▷ app b = app a ◁ G.map₂ η ≫ naturality g := by
    aesop_cat
  naturality_id (a : B) :
      app a ◁ G.mapId a ≫ naturality (𝟙 a) =
        (ρ_ (app a)).hom ≫ (λ_ (app a)).inv  ≫ F.mapId a ▷ app a := by
    aesop_cat
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      app a ◁ G.mapComp f g ≫ naturality (f ≫ g) =
        (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫
          (α_ _ _ _).hom ≫  F.map f ◁ naturality g ≫
            (α_ _ _ _).inv ≫ F.mapComp f g ▷ app c := by
    aesop_cat

namespace LaxTrans

attribute [reassoc (attr := simp)] naturality_naturality naturality_id naturality_comp

variable {F G H : LaxFunctor B C}
variable (η : LaxTrans F G) (θ : LaxTrans G H)

variable (F) in
/-- The identity lax transformation. -/
def id : LaxTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {_ _} f := (λ_ (F.map f)).hom ≫ (ρ_ (F.map f)).inv

instance : Inhabited (LaxTrans F F ) :=
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

/-- If `η` is an oplax transformation between `F` and `G`, we have a 1-morphism
`η.app a : F.obj a ⟶ G.obj a` for each object `a : B`. We also have a 2-morphism
`η.naturality f : F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism `f : a ⟶ b`.
These 2-morphisms satisfies the naturality condition, and preserve the identities and
the compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
structure OplaxTrans (F G : LaxFunctor B C) where
  /-- The component 1-morphisms of an oplax transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-morphisms underlying the oplax naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ⟶ app a ≫ G.map f
  /-- Naturality of the oplax naturality constraint. -/
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      F.map₂ η ▷ app b ≫ naturality g = naturality f ≫ app a ◁ G.map₂ η := by
    aesop_cat
  naturality_id (a : B) :
      F.mapId a ▷ app a ≫ naturality (𝟙 a) =
        (λ_ (app a)).hom ≫ (ρ_ (app a)).inv ≫ app a ◁ G.mapId a := by
    aesop_cat
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      F.mapComp f g ▷ app c ≫ naturality (f ≫ g) =
        (α_ _ _ _).hom ≫ F.map f ◁ naturality g ≫
          (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom ≫
            app a ◁ G.mapComp f g := by
    aesop_cat

namespace OplaxTrans

attribute [reassoc (attr := simp)] naturality_naturality naturality_id naturality_comp

variable {F G H : LaxFunctor B C} (η : OplaxTrans F G) (θ : OplaxTrans G H)

variable (F) in
/-- The identity oplax transformation. -/
def id : OplaxTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {_ _} f := (ρ_ (F.map f)).hom ≫ (λ_ (F.map f)).inv

instance : Inhabited (OplaxTrans F F ) :=
  ⟨id F⟩

/-- Auxiliary definition for `vComp`. -/
abbrev vCompApp (a : B) : F.obj a ⟶ H.obj a := η.app a ≫ θ.app a

/-- Auxiliary definition for `vComp`. -/
abbrev vCompNaturality {a b : B} (f : a ⟶ b) :
    F.map f ≫ η.app b ≫ θ.app b ⟶ (η.app a ≫ θ.app a) ≫ H.map f :=
  (α_ _ _ _).inv ≫ η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom ≫
    η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv

theorem vComp_naturality_naturality {a b : B} {f g : a ⟶ b} (β : f ⟶ g) :
    F.map₂ β ▷ η.vCompApp θ b ≫ η.vCompNaturality θ g =
      η.vCompNaturality θ f ≫ η.vCompApp θ a ◁ H.map₂ β := by
  calc
    _ = 𝟙 _ ⊗≫ (F.map₂ β ▷ η.app b ≫ η.naturality g) ▷ θ.app b ⊗≫
          η.app a ◁ θ.naturality g ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ η.naturality f ▷ θ.app b ⊗≫
          η.app a ◁ (G.map₂ β ▷ θ.app b ≫ θ.naturality g) ⊗≫ 𝟙 _ := by
      rw [η.naturality_naturality]
      bicategory
    _ = _ := by
      rw [θ.naturality_naturality]
      bicategory

theorem vComp_naturality_id (a : B) :
    F.mapId a ▷ η.vCompApp θ a ≫ η.vCompNaturality θ (𝟙 a) =
      (λ_ (η.vCompApp θ a)).hom ≫ (ρ_ (η.vCompApp θ a)).inv ≫ η.vCompApp θ a ◁ H.mapId a := by
  calc
    _ = 𝟙 _ ⊗≫ (F.mapId a ▷ η.app a ≫ η.naturality (𝟙 a)) ▷ θ.app a ⊗≫
          η.app a ◁ θ.naturality (𝟙 a) ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ η.app a ◁ (G.mapId a ▷ θ.app a ≫ θ.naturality (𝟙 a)) ⊗≫ 𝟙 _ := by
      rw [η.naturality_id]
      bicategory
    _ = _ := by
      rw [θ.naturality_id]
      bicategory

theorem vComp_naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    F.mapComp f g ▷ η.vCompApp θ c ≫ η.vCompNaturality θ (f ≫ g) =
      (α_ (F.map f) (F.map g) (η.vCompApp θ c)).hom ≫
        F.map f ◁ η.vCompNaturality θ g ≫
          (α_ (F.map f) (η.vCompApp θ b) (H.map g)).inv ≫
            η.vCompNaturality θ f ▷ H.map g ≫
              (α_ (η.vCompApp θ a) (H.map f) (H.map g)).hom ≫ η.vCompApp θ a ◁ H.mapComp f g := by
  calc
    _ = 𝟙 _ ⊗≫ (F.mapComp f g ▷ η.app c ≫ η.naturality (f ≫ g)) ▷ θ.app c ⊗≫
          η.app a ◁ θ.naturality (f ≫ g) ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (F.map f ◁ η.naturality g ⊗≫ η.naturality f ▷ G.map g) ▷ θ.app c ⊗≫
          η.app a ◁ (G.mapComp f g ▷ θ.app c ≫ θ.naturality (f ≫ g)) ⊗≫ 𝟙 _ := by
      rw [η.naturality_comp]
      bicategory
    _ = 𝟙 _ ⊗≫ F.map f ◁ η.naturality g ▷ θ.app c ⊗≫
          (η.naturality f ▷ (G.map g ≫ θ.app c) ≫ (η.app a ≫ G.map f) ◁ θ.naturality g) ⊗≫
            η.app a ◁ (θ.naturality f ▷ H.map g ⊗≫ θ.app a ◁ H.mapComp f g) ⊗≫ 𝟙 _ := by
      rw [θ.naturality_comp]
      bicategory
    _ = _ := by
      rw [← whisker_exchange]
      bicategory

/-- Vertical composition of oplax transformations. -/
def vComp (η : OplaxTrans F G) (θ : OplaxTrans G H) : OplaxTrans F H where
  app := vCompApp η θ
  naturality := vCompNaturality η θ
  naturality_naturality := vComp_naturality_naturality η θ
  naturality_id := vComp_naturality_id η θ
  naturality_comp := vComp_naturality_comp η θ

/-- `CategoryStruct` on `LaxFunctor B C` where the (1-)morphisms are given by oplax
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
scoped instance : CategoryStruct (LaxFunctor B C) where
  Hom := OplaxTrans
  id := OplaxTrans.id
  comp := OplaxTrans.vComp

end OplaxTrans

end Lax

end CategoryTheory
