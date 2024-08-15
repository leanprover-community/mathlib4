/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax

/-!
# Strong natural transformations

A strong natural transformation is an oplax natural transformation such that each component 2-cell
is an isomorphism.

## Main definitions

* `StrongPseudoNatTrans F G` : strong natural transformations between oplax functors `F` and `G`.
* `mkOfOplax η η'` : given an oplax natural transformation `η` such that each component 2-cell
  is an isomorphism, `mkOfOplax` gives the corresponding strong natural transformation.
* `StrongPseudoNatTrans.vcomp η θ` : the vertical composition of strong natural transformations `η`
  and `θ`.
* `StrongPseudoNatTrans.category F G` : a category structure on Pseudofunctors between `F` and `G`,
  where the morphisms are strong natural transformations.

## TODO

After having defined lax functors, we should define 3 different types of strong natural
transformations:
* strong natural transformations between oplax functors (as defined here).
* strong natural transformations between lax functors.
* strong natural transformations between Pseudofunctors. From these types of strong natural
  transformations, we can define the underlying natural transformations between the underlying
  oplax resp. lax functors. Many properties can then be inferred from these.

## References
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055)

-/

namespace CategoryTheory

open Category Bicategory

open scoped Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- A strong natural transformation between oplax functors `F` and `G` is a natural transformation
that is "natural up to 2-isomorphisms".

More precisely, it consists of the following:
* a 1-morphism `η.app a : F.obj a ⟶ G.obj a` for each object `a : B`.
* a 2-isomorphism `η.naturality f : F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism
`f : a ⟶ b`.
* These 2-isomorphisms satisfy the naturality condition, and preserve the identities and the
compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
structure StrongPseudoNatTrans (F G : Pseudofunctor B C) where
  app (a : B) : F.obj a ⟶ G.obj a
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ≅ app a ≫ G.map f
  naturality_naturality :
    ∀ {a b : B} {f g : a ⟶ b} (η : f ⟶ g),
      F.map₂ η ▷ app b ≫ (naturality g).hom = (naturality f).hom ≫ app a ◁ G.map₂ η := by
    aesop_cat
  naturality_id :
    ∀ a : B,
      (naturality (𝟙 a)).hom ≫ app a ◁ (G.mapId a).hom =
        (F.mapId a).hom ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv := by
    aesop_cat
  naturality_comp :
    ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
      (naturality (f ≫ g)).hom ≫ app a ◁ (G.mapComp f g).hom =
        (F.mapComp f g).hom ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫
        (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom := by
    aesop_cat

attribute [nolint docBlame] CategoryTheory.StrongPseudoNatTrans.app
  CategoryTheory.StrongPseudoNatTrans.naturality
  CategoryTheory.StrongPseudoNatTrans.naturality_naturality
  CategoryTheory.StrongPseudoNatTrans.naturality_id
  CategoryTheory.StrongPseudoNatTrans.naturality_comp

attribute [reassoc (attr := simp)] StrongPseudoNatTrans.naturality_naturality
  StrongPseudoNatTrans.naturality_id StrongPseudoNatTrans.naturality_comp

namespace StrongPseudoNatTrans

section

variable {F G : Pseudofunctor B C}

/-- The underlying oplax natural transformation of a strong natural transformation. -/
@[simps]
def toStrongOplax (η : StrongPseudoNatTrans F G) :
    StrongOplaxNatTrans F.toOplax G.toOplax where
  app := η.app
  naturality f := η.naturality f

instance hasCoeToStrongOplax : Coe (StrongPseudoNatTrans F G)
    (StrongOplaxNatTrans F.toOplax G) :=
  ⟨toStrongOplax⟩

/-- Construct a strong natural transformation between pseudofunctors from a strong natural
transformation between the underlying oplax functors. -/
def mkOfStrongOplax (η : StrongOplaxNatTrans F.toOplax G) : StrongPseudoNatTrans F G where
  app := η.app
  naturality := η.naturality
  naturality_naturality := η.naturality_naturality
  naturality_id := η.naturality_id
  naturality_comp := η.naturality_comp

section

variable (F)


/-- The identity strong natural transformation. -/
@[simps!]
def id : StrongPseudoNatTrans F F :=
  mkOfStrongOplax (StrongOplaxNatTrans.id F.toOplax)

@[simp]
lemma id.toOplax : (id F).toStrongOplax = StrongOplaxNatTrans.id F.toOplax :=
  rfl

instance : Inhabited (StrongPseudoNatTrans F F) :=
  ⟨id F⟩

end

variable {H : Pseudofunctor B C} (η : StrongPseudoNatTrans F G) (θ : StrongPseudoNatTrans G H)

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ (θ.naturality h).hom =
      f ◁ (θ.naturality g).hom ≫ f ◁ θ.app a ◁ H.map₂ β := by
  apply θ.toStrongOplax.whiskerLeft_naturality_naturality

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') :
    F.map₂ β ▷ η.app b ▷ h ≫ (η.naturality g).hom ▷ h =
      (η.naturality f).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h ≫ (α_ _ _ _).inv := by
  apply η.toStrongOplax.whiskerRight_naturality_naturality

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
    f ◁ (θ.naturality (g ≫ h)).hom ≫ f ◁ θ.app a ◁ (H.mapComp g h).hom =
      f ◁ (G.mapComp g h).hom ▷ θ.app c ≫
        f ◁ (α_ _ _ _).hom ≫
          f ◁ G.map g ◁ (θ.naturality h).hom ≫
            f ◁ (α_ _ _ _).inv ≫ f ◁ (θ.naturality g).hom ▷ H.map h ≫ f ◁ (α_ _ _ _).hom := by
  apply θ.toStrongOplax.whiskerLeft_naturality_comp

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
    (η.naturality (f ≫ g)).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ (G.mapComp f g).hom ▷ h =
      (F.mapComp f g).hom ▷ η.app c ▷ h ≫
        (α_ _ _ _).hom ▷ h ≫
          (α_ _ _ _).hom ≫
            F.map f ◁ (η.naturality g).hom ▷ h ≫
              (α_ _ _ _).inv ≫
                (α_ _ _ _).inv ▷ h ≫
                 (η.naturality f).hom ▷ G.map g ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom := by
  apply η.toStrongOplax.whiskerRight_naturality_comp

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_id (f : a' ⟶ G.obj a) :
    f ◁ (θ.naturality (𝟙 a)).hom ≫ f ◁ θ.app a ◁ (H.mapId a).hom =
      f ◁ (G.mapId a).hom ▷ θ.app a ≫ f ◁ (λ_ (θ.app a)).hom ≫ f ◁ (ρ_ (θ.app a)).inv := by
  apply θ.toStrongOplax.whiskerLeft_naturality_id

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_id (f : G.obj a ⟶ a') :
    (η.naturality (𝟙 a)).hom ▷ f ≫ (α_ _ _ _).hom ≫ η.app a ◁ (G.mapId a).hom ▷ f =
    (F.mapId a).hom ▷ η.app a ▷ f ≫ (λ_ (η.app a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫
    (α_ _ _ _).hom := by
  apply η.toStrongOplax.whiskerRight_naturality_id

end

/-- Vertical composition of strong natural transformations. -/
@[simps!]
def vcomp (η : StrongPseudoNatTrans F G) (θ : StrongPseudoNatTrans G H) :
    StrongPseudoNatTrans F H :=
  mkOfStrongOplax (StrongOplaxNatTrans.vcomp η.toStrongOplax θ.toStrongOplax)

end

end StrongPseudoNatTrans

variable (B C)

@[simps id comp]
instance Pseudofunctor.categoryStruct : CategoryStruct (Pseudofunctor B C) where
  Hom F G := StrongPseudoNatTrans F G
  id F := StrongPseudoNatTrans.id F
  comp := StrongPseudoNatTrans.vcomp


end CategoryTheory
