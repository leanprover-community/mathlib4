/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax

/-!

# Strong transformations of pseudofunctors

There are three types of transformations between pseudofunctors, depending on the direction
or invertibility of the 2-morphism witnessing the naturality condition.

In this file we define strong transformations, which require the 2-morphism to be invertible.

## Main definitions

* `Pseudofunctor.StrongTrans F G`: strong transformations between pseudofunctors `F` and `G`.
* `Pseudofunctor.mkOfOplax η η'`: Given two pseudofunctors, and a strong transformation `η` between
  their underlying oplax functors, `mkOfOplax` lifts this to a strong transformation between the
  pseudofunctors.
* `Pseudofunctor.StrongTrans.vcomp η θ`: the vertical composition of strong transformations `η`
  and `θ`.

Using this we obtain a `CategoryStruct` on pseudofunctors, where the arrows are given by
strong transformations. See `Pseudofunctor.categoryStruct`.

## References
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055)

-/

namespace CategoryTheory.Pseudofunctor

open Category Bicategory Oplax

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
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      F.map₂ η ▷ app b ≫ (naturality g).hom = (naturality f).hom ≫ app a ◁ G.map₂ η := by
    cat_disch
  /-- Oplax unity. -/
  naturality_id (a : B) :
      (naturality (𝟙 a)).hom ≫ app a ◁ (G.mapId a).hom =
        (F.mapId a).hom ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv := by
    cat_disch
  /-- Oplax functoriality. -/
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      (naturality (f ≫ g)).hom ≫ app a ◁ (G.mapComp f g).hom =
        (F.mapComp f g).hom ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫
        (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom := by
    cat_disch

attribute [reassoc (attr := simp)] StrongTrans.naturality_naturality
  StrongTrans.naturality_id StrongTrans.naturality_comp

namespace StrongTrans

variable {F G : Pseudofunctor B C}

/-- The underlying oplax transformation of a strong transformation. -/
@[simps]
def toOplax (η : StrongTrans F G) : Oplax.StrongTrans F.toOplax G.toOplax where
  app := η.app
  naturality f := η.naturality f

instance hasCoeToOplax : Coe (StrongTrans F G) (Oplax.StrongTrans F.toOplax G.toOplax) :=
  ⟨toOplax⟩

/-- Construct a strong transformation of pseudofunctors from a strong transformation of the
underlying oplax functors. -/
@[simps]
def mkOfOplax (η : Oplax.StrongTrans F.toOplax G.toOplax) :
    StrongTrans F G where
  app := η.app
  naturality := η.naturality
  naturality_naturality θ := η.naturality_naturality θ
  naturality_id a := η.naturality_id a
  naturality_comp f g := η.naturality_comp f g

variable (F) in
/-- The identity strong transformation. -/
def id : StrongTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {a b} f := (ρ_ (F.map f)) ≪≫ (λ_ (F.map f)).symm

instance : Inhabited (StrongTrans F F) :=
  ⟨id F⟩

variable {H : Pseudofunctor B C}

/-- Vertical composition of strong transformations. -/
def vcomp (η : StrongTrans F G) (θ : StrongTrans G H) : StrongTrans F H :=
  mkOfOplax (Oplax.StrongTrans.vcomp η.toOplax θ.toOplax)

/-- `CategoryStruct` on `Pseudofunctor B C` where the (1-)morphisms are given by strong
transformations. -/
@[simps! id_app id_naturality_hom id_naturality_inv comp_naturality_hom
comp_naturality_inv]
scoped instance categoryStruct : CategoryStruct (Pseudofunctor B C) where
  Hom F G := StrongTrans F G
  id F := StrongTrans.id F
  comp := StrongTrans.vcomp

variable (η : F ⟶ G) (θ : G ⟶ H)

@[simp]
lemma comp_app (η : F ⟶ G) (θ : G ⟶ H) (a : B) :
    (η ≫ θ).app a = η.app a ≫ θ.app a :=
  rfl

variable (F) in
@[simp]
lemma id.toOplax : Oplax.StrongTrans.id F.toOplax = 𝟙 F :=
  rfl

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

@[reassoc, to_app]
lemma naturality_id_hom (α : F ⟶ G) (a : B) :
    (α.naturality (𝟙 a)).hom = (F.mapId a).hom ▷ α.app a ≫
      (λ_ (α.app a)).hom ≫ (ρ_ (α.app a)).inv ≫ α.app a ◁ (G.mapId a).inv := by
  simp [← assoc, ← IsIso.comp_inv_eq]

lemma naturality_id_iso (α : F ⟶ G) (a : B) :
    α.naturality (𝟙 a) = whiskerRightIso (F.mapId a) (α.app a) ≪≫
      (λ_ (α.app a)) ≪≫ (ρ_ (α.app a)).symm ≪≫ whiskerLeftIso (α.app a) (G.mapId a).symm := by
  ext
  simp [naturality_id_hom]

@[reassoc, to_app]
lemma naturality_id_inv (α : F ⟶ G) (a : B) :
    (α.naturality (𝟙 a)).inv = α.app a ◁ (G.mapId a).hom ≫ (ρ_ (α.app a)).hom ≫
      (λ_ (α.app a)).inv ≫ (F.mapId a).inv ▷ α.app a := by
  simp [naturality_id_iso]

@[reassoc, to_app]
lemma naturality_naturality_hom (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g) :
    (α.naturality g).hom =
     (F.map₂ η.inv) ▷ α.app b ≫ (α.naturality f).hom ≫ α.app a ◁ G.map₂ η.hom := by
  simp [← IsIso.inv_comp_eq, ← G.map₂_inv η.inv]

lemma naturality_naturality_iso (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g) :
    α.naturality g = whiskerRightIso (F.map₂Iso η.symm) (α.app b) ≪≫
      (α.naturality f) ≪≫ whiskerLeftIso (α.app a) (G.map₂Iso η) := by
  ext
  rw [naturality_naturality_hom α η]
  simp

lemma naturality_naturality_inv (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g) :
    (α.naturality g).inv =
      α.app a ◁ G.map₂ η.inv ≫ (α.naturality f).inv ≫ F.map₂ η.hom ▷ α.app b := by
  simp [naturality_naturality_iso α η]

@[reassoc, to_app]
lemma naturality_comp_hom (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (α.naturality (f ≫ g)).hom =
      (F.mapComp f g).hom ▷ α.app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (α.naturality g).hom ≫
      (α_ _ _ _).inv ≫ (α.naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom ≫
      α.app a ◁ (G.mapComp f g).inv := by
  simp [← assoc, ← IsIso.comp_inv_eq]

lemma naturality_comp_iso (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    α.naturality (f ≫ g) = whiskerRightIso (F.mapComp f g) (α.app c) ≪≫ (α_ _ _ _) ≪≫
      whiskerLeftIso (F.map f) (α.naturality g) ≪≫ (α_ _ _ _).symm ≪≫
      whiskerRightIso (α.naturality f) (G.map g) ≪≫ α_ _ _ _ ≪≫
      whiskerLeftIso (α.app a) (G.mapComp f g).symm := by
  ext
  simp [naturality_comp_hom α f g]

@[reassoc, to_app]
lemma naturality_comp_inv (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (α.naturality (f ≫ g)).inv =
      α.app a ◁ (G.mapComp f g).hom ≫ (α_ _ _ _).inv ≫  (α.naturality f).inv ▷ G.map g ≫
      (α_ _ _ _).hom ≫ F.map f ◁ (α.naturality g).inv ≫ (α_ _ _ _).inv ≫
      (F.mapComp f g).inv ▷ α.app c := by
  simp [naturality_comp_iso α f g]

end

end CategoryTheory.Pseudofunctor.StrongTrans
