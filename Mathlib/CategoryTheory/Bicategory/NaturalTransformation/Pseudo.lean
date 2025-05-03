/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax

/-!

# Strong transformations of pseudofunctors

A strong transformation is an oplax transformation such that each component 2-cell
is an isomorphism.

## Main definitions

* `StrongTrans F G` : strong transformations between oplax functors `F` and `G`.
* `mkOfOplax η η'` : given an oplax transformation `η` such that each component 2-cell
  is an isomorphism, `mkOfOplax` gives the corresponding strong transformation.
* `StrongTrans.vcomp η θ` : the vertical composition of strong transformations `η`
  and `θ`.
* `StrongTrans.category F G` : a category structure on Pseudofunctors between `F` and `G`,
  where the morphisms are strong transformations.

## TODO

After having defined lax functors, we should define 3 different types of strong natural
transformations:
* strong transformations between oplax functors (as defined here).
* strong transformations between lax functors.
* strong transformations between Pseudofunctors. From these types of strong natural
  transformations, we can define the underlying natural transformations between the underlying
  oplax resp. lax functors. Many properties can then be inferred from these.

## References
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055)

-/

namespace CategoryTheory.Pseudofunctor

open Category Bicategory Oplax

open scoped Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- A strong transformation between pseudofunctors `F` and `G` is a natural transformation
that is "natural up to 2-isomorphisms".
More precisely, it consists of the following:
* a 1-morphism `η.app a : F.obj a ⟶ G.obj a` for each object `a : B`.
* a 2-isomorphism `η.naturality f : F.map f ≫ app b ≅ app a ≫ G.map f` for each 1-morphism
`f : a ⟶ b`.
* These 2-isomorphisms satisfy the naturality condition, and preserve the identities and the
compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
structure StrongTrans (F G : Pseudofunctor B C) where
  /-- The component 1-morphisms of a strong transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-isomorphisms underlying the strong naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ≅ app a ≫ G.map f
  /-- Naturality of the strong naturality constraint. -/
  naturality_naturality :
    ∀ {a b : B} {f g : a ⟶ b} (η : f ⟶ g),
      F.map₂ η ▷ app b ≫ (naturality g).hom = (naturality f).hom ≫ app a ◁ G.map₂ η := by
    aesop_cat
  /-- Oplax unity. -/
  naturality_id :
    ∀ a : B,
      (naturality (𝟙 a)).hom ≫ app a ◁ (G.mapId a).hom =
        (F.mapId a).hom ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv := by
    aesop_cat
  /-- Oplax functoriality. -/
  naturality_comp :
    ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
      (naturality (f ≫ g)).hom ≫ app a ◁ (G.mapComp f g).hom =
        (F.mapComp f g).hom ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫
        (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom := by
    aesop_cat

attribute [reassoc (attr := simp)] StrongTrans.naturality_naturality
  StrongTrans.naturality_id StrongTrans.naturality_comp

/-- A structure on an oplax transformation that promotes it to a strong transformation.
See `Pseudofunctor.StrongTrans.mkOfOplax`. -/
structure StrongCore {F G : Pseudofunctor B C} (η : OplaxTrans F.toOplax G) where
  /-- The underlying 2-isomorphisms of the naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ η.app b ≅ η.app a ≫ G.map f
  /-- The 2-isomorphisms agree with the underlying 2-morphism of the oplax transformation. -/
  naturality_hom {a b : B} (f : a ⟶ b) : (naturality f).hom = η.naturality f := by aesop_cat

attribute [simp] StrongCore.naturality_hom

namespace StrongTrans

section

variable {F G : Pseudofunctor B C}

/-- The underlying oplax transformation of a strong transformation. -/
@[simps]
def toOplax (η : StrongTrans F G) : F.toOplax ⟶ G.toOplax where
  app := η.app
  naturality f := (η.naturality f).hom

instance hasCoeToOplax : Coe (StrongTrans F G) (F.toOplax ⟶ G) :=
  ⟨toOplax⟩

/-- Construct a strong transformation from an oplax transformation whose
naturality 2-morphism is an isomorphism. -/
@[simps]
def mkOfOplax {F G : Pseudofunctor B C} (η : F.toOplax ⟶ G) (η' : StrongCore η) :
    StrongTrans F G where
  app := η.app
  naturality := η'.naturality
  -- Not automatic as simp must convert F.toOplax.map₂ to F.map₂ in η.naturality_naturality etc
  naturality_naturality θ := by simpa using η.naturality_naturality θ
  naturality_id a := by simpa using η.naturality_id a
  naturality_comp f g := by simpa using η.naturality_comp f g

/-- Construct a strong transformation from an oplax transformation whose
naturality 2-morphism is an isomorphism. -/
@[simps]
noncomputable def mkOfOplax' {F G : Pseudofunctor B C} (η : F.toOplax ⟶ G)
    [∀ a b (f : a ⟶ b), IsIso (η.naturality f)] : StrongTrans F G where
  app := η.app
  naturality := fun f => asIso (η.naturality _)
  naturality_naturality θ := by simpa using η.naturality_naturality θ
  naturality_id a := by simpa using η.naturality_id a
  naturality_comp f g := by simpa using η.naturality_comp f g


variable {H : Pseudofunctor B C} (η : StrongTrans F G) (θ : StrongTrans G H)

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp), to_app]
theorem whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ (θ.naturality h).hom =
      f ◁ (θ.naturality g).hom ≫ f ◁ θ.app a ◁ H.map₂ β :=
  θ.toOplax.whiskerLeft_naturality_naturality _ _

@[reassoc (attr := simp), to_app]
theorem whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') :
    F.map₂ β ▷ η.app b ▷ h ≫ (η.naturality g).hom ▷ h =
      (η.naturality f).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h ≫ (α_ _ _ _).inv :=
  η.toOplax.whiskerRight_naturality_naturality _ _

@[reassoc (attr := simp), to_app]
theorem whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
    f ◁ (θ.naturality (g ≫ h)).hom ≫ f ◁ θ.app a ◁ (H.mapComp g h).hom =
      f ◁ (G.mapComp g h).hom ▷ θ.app c ≫
        f ◁ (α_ _ _ _).hom ≫
          f ◁ G.map g ◁ (θ.naturality h).hom ≫
            f ◁ (α_ _ _ _).inv ≫ f ◁ (θ.naturality g).hom ▷ H.map h ≫ f ◁ (α_ _ _ _).hom :=
  θ.toOplax.whiskerLeft_naturality_comp _ _ _

@[reassoc (attr := simp), to_app]
theorem whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
    (η.naturality (f ≫ g)).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ (G.mapComp f g).hom ▷ h =
      (F.mapComp f g).hom ▷ η.app c ▷ h ≫
        (α_ _ _ _).hom ▷ h ≫
          (α_ _ _ _).hom ≫
            F.map f ◁ (η.naturality g).hom ▷ h ≫
              (α_ _ _ _).inv ≫
                (α_ _ _ _).inv ▷ h ≫
                 (η.naturality f).hom ▷ G.map g ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom :=
  η.toOplax.whiskerRight_naturality_comp _ _ _

@[reassoc (attr := simp), to_app]
theorem whiskerLeft_naturality_id (f : a' ⟶ G.obj a) :
    f ◁ (θ.naturality (𝟙 a)).hom ≫ f ◁ θ.app a ◁ (H.mapId a).hom =
      f ◁ (G.mapId a).hom ▷ θ.app a ≫ f ◁ (λ_ (θ.app a)).hom ≫ f ◁ (ρ_ (θ.app a)).inv :=
  θ.toOplax.whiskerLeft_naturality_id _

@[reassoc (attr := simp), to_app]
theorem whiskerRight_naturality_id (f : G.obj a ⟶ a') :
    (η.naturality (𝟙 a)).hom ▷ f ≫ (α_ _ _ _).hom ≫ η.app a ◁ (G.mapId a).hom ▷ f =
    (F.mapId a).hom ▷ η.app a ▷ f ≫ (λ_ (η.app a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫
    (α_ _ _ _).hom :=
  η.toOplax.whiskerRight_naturality_id _

end

variable (F) in
/-- The identity strong transformation. -/
def id : StrongTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {a b} f := (ρ_ (F.map f)) ≪≫ (λ_ (F.map f)).symm

instance : Inhabited (StrongTrans F F) :=
  ⟨id F⟩

/-- Vertical composition of strong transformations. -/
def vcomp (η : StrongTrans F G) (θ : StrongTrans G H) :
    StrongTrans F H :=
  mkOfOplax (OplaxTrans.vcomp η.toOplax θ.toOplax)
    { naturality := fun {a b} f ↦
        (α_ _ _ _).symm ≪≫ whiskerRightIso (η.naturality f) (θ.app b) ≪≫
        (α_ _ _ _) ≪≫ whiskerLeftIso (η.app a) (θ.naturality f) ≪≫ (α_ _ _ _).symm }

end

end StrongTrans

variable (B C)

@[simps! id_app id_naturality_hom id_naturality_inv comp_naturality_hom
comp_naturality_inv]
instance categoryStruct : CategoryStruct (Pseudofunctor B C) where
  Hom F G := StrongTrans F G
  id F := StrongTrans.id F
  comp := StrongTrans.vcomp

section

variable {F G H : Pseudofunctor B C}

@[simp]
lemma StrongTrans.comp_app (η : F ⟶ G) (θ : G ⟶ H) (a : B) :
    (η ≫ θ).app a = η.app a ≫ θ.app a :=
  rfl

end
@[simp]
lemma id.toOplax (F : Pseudofunctor B C) : 𝟙 F = 𝟙 F.toOplax :=
  rfl

end CategoryTheory.Pseudofunctor
