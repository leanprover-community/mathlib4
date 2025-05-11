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
abbrev StrongTrans (F G : Pseudofunctor B C) := Oplax.StrongTrans F.toOplax G.toOplax

namespace StrongTrans

variable {F G : Pseudofunctor B C} (η : StrongTrans F G)

@[reassoc (attr := simp), to_app]
lemma naturality_naturality {a b : B} (f g : a ⟶ b) (φ : f ⟶ g) :
    F.map₂ φ ▷ η.app b ≫ (η.naturality g).hom = (η.naturality f).hom ≫ η.app a ◁ G.map₂ φ :=
  Oplax.StrongTrans.naturality_naturality η φ

@[reassoc (attr := simp), to_app]
lemma naturality_id (a : B) :
    (η.naturality (𝟙 a)).hom ≫ η.app a ◁ (G.mapId a).hom =
      (F.mapId a).hom ▷ η.app a ≫ (λ_ (η.app a)).hom ≫ (ρ_ (η.app a)).inv :=
  Oplax.StrongTrans.naturality_id η a

@[reassoc (attr := simp), to_app]
lemma naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (η.naturality (f ≫ g)).hom ≫ η.app a ◁ (G.mapComp f g).hom =
      (F.mapComp f g).hom ▷ η.app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (η.naturality g).hom ≫
        (α_ _ _ _).inv ≫ (η.naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom :=
  Oplax.StrongTrans.naturality_comp η f g


section

variable {F G H : Pseudofunctor B C} (η : StrongTrans F G) (θ : StrongTrans G H)
  {a b c : B} {a' : C}

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

/-- The identity strong transformation. -/
abbrev id (F : Pseudofunctor B C) : StrongTrans F F := Oplax.StrongTrans.id F.toOplax

instance (F : Pseudofunctor B C) : Inhabited (StrongTrans F F) :=
  ⟨id F⟩

/-- Vertical composition of strong transformations. -/
abbrev vcomp {F G H : Pseudofunctor B C} (η : StrongTrans F G) (θ : StrongTrans G H) :
    StrongTrans F H :=
  Oplax.StrongTrans.vcomp η θ

end StrongTrans

variable (B C)

@[simps! id_app id_naturality_hom id_naturality_inv comp_naturality_hom
comp_naturality_inv]
scoped instance categoryStruct : CategoryStruct (Pseudofunctor B C) where
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

end CategoryTheory.Pseudofunctor
