/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Oplax

/-!
# Transformations between oplax functors

Just as there are natural transformations between functors, there are transformations
between oplax functors. The equality in the naturality condition of a natural transformation gets
replaced by a specified 2-morphism. Now, there are three possible types of transformations (between
oplax functors):
* Oplax natural transformations;
* Lax natural transformations;
* Strong natural transformations.
These differ in the direction (and invertibility) of the 2-morphisms involved in the naturality
condition.

## Main definitions

* `Oplax.OplaxTrans F G`: oplax transformations between oplax functors `F` and `G`. The naturality
  condition is given by a 2-morphism `F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism
  `f : a ⟶ b`.
* `Oplax.StrongTrans F G`: Strong transformations between oplax functors `F` and `G`.

Using these, we define two `CategoryStruct` (scoped) instances on `OplaxFunctor B C`, one in the
`Oplax.OplaxTrans` namespace and one in the `Oplax.StrongTrans` namespace. The arrows in these
CategoryStruct's are given by oplax transformations and strong transformations respectively.

We also provide API for going between oplax transformations and strong transformations:
* `Oplax.StrongCore F G`: a structure on an oplax transformation between oplax functors that
  promotes it to a strong transformation.
* `Oplax.mkOfOplax η η'`: given an oplax transformation `η` such that each component
  2-morphism is an isomorphism, `mkOfOplax` gives the corresponding strong transformation.

# TODO
This file could also include lax transformations between oplax functors.

## References
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055)

-/

namespace CategoryTheory.Oplax

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- If `η` is an oplax transformation between `F` and `G`, we have a 1-morphism
`η.app a : F.obj a ⟶ G.obj a` for each object `a : B`. We also have a 2-morphism
`η.naturality f : F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism `f : a ⟶ b`.
These 2-morphisms satisfies the naturality condition, and preserve the identities and
the compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
structure OplaxTrans (F G : OplaxFunctor B C) where
  /-- The component 1-morphisms of an oplax transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-morphisms underlying the oplax naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ⟶ app a ≫ G.map f
  /-- Naturality of the oplax naturality constraint. -/
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      F.map₂ η ▷ app b ≫ naturality g = naturality f ≫ app a ◁ G.map₂ η := by
    cat_disch
  /-- Oplax unity. -/
  naturality_id (a : B) :
      naturality (𝟙 a) ≫ app a ◁ G.mapId a =
        F.mapId a ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv := by
    cat_disch
  /-- Oplax functoriality. -/
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      naturality (f ≫ g) ≫ app a ◁ G.mapComp f g =
        F.mapComp f g ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ naturality g ≫
          (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom := by
    cat_disch

attribute [reassoc (attr := simp)] OplaxTrans.naturality_naturality OplaxTrans.naturality_id
  OplaxTrans.naturality_comp

namespace OplaxTrans

variable {F : OplaxFunctor B C} {G H : OplaxFunctor B C} (η : OplaxTrans F G) (θ : OplaxTrans G H)

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ θ.naturality h =
      f ◁ θ.naturality g ≫ f ◁ θ.app a ◁ H.map₂ β := by
  simp_rw [← whiskerLeft_comp, naturality_naturality]

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') :
    F.map₂ β ▷ η.app b ▷ h ≫ η.naturality g ▷ h =
      η.naturality f ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h ≫ (α_ _ _ _).inv := by
  rw [← comp_whiskerRight, naturality_naturality, comp_whiskerRight, whisker_assoc]

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
    f ◁ θ.naturality (g ≫ h) ≫ f ◁ θ.app a ◁ H.mapComp g h =
      f ◁ G.mapComp g h ▷ θ.app c ≫
        f ◁ (α_ _ _ _).hom ≫
          f ◁ G.map g ◁ θ.naturality h ≫
            f ◁ (α_ _ _ _).inv ≫ f ◁ θ.naturality g ▷ H.map h ≫ f ◁ (α_ _ _ _).hom := by
  simp_rw [← whiskerLeft_comp, naturality_comp]

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
    η.naturality (f ≫ g) ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapComp f g ▷ h =
      F.mapComp f g ▷ η.app c ▷ h ≫
        (α_ _ _ _).hom ▷ h ≫
          (α_ _ _ _).hom ≫
            F.map f ◁ η.naturality g ▷ h ≫
              (α_ _ _ _).inv ≫
                (α_ _ _ _).inv ▷ h ≫
                  η.naturality f ▷ G.map g ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom := by
  rw [← associator_naturality_middle, ← comp_whiskerRight_assoc, naturality_comp]; simp

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_id (f : a' ⟶ G.obj a) :
    f ◁ θ.naturality (𝟙 a) ≫ f ◁ θ.app a ◁ H.mapId a =
      f ◁ G.mapId a ▷ θ.app a ≫ f ◁ (λ_ (θ.app a)).hom ≫ f ◁ (ρ_ (θ.app a)).inv := by
  simp_rw [← whiskerLeft_comp, naturality_id]

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_id (f : G.obj a ⟶ a') :
    η.naturality (𝟙 a) ▷ f ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapId a ▷ f =
    F.mapId a ▷ η.app a ▷ f ≫ (λ_ (η.app a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫ (α_ _ _ _).hom := by
  rw [← associator_naturality_middle, ← comp_whiskerRight_assoc, naturality_id]; simp

end

variable (F) in
/-- The identity oplax transformation. -/
def id : OplaxTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {_ _} f := (ρ_ (F.map f)).hom ≫ (λ_ (F.map f)).inv

instance : Inhabited (OplaxTrans F F) :=
  ⟨id F⟩

/-- Vertical composition of oplax transformations. -/
def vcomp : OplaxTrans F H where
  app a := η.app a ≫ θ.app a
  naturality {a b} f :=
    (α_ _ _ _).inv ≫
      η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom ≫ η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv
  naturality_comp {a b c} f g :=
    calc
      _ =
        (α_ _ _ _).inv ≫
          F.mapComp f g ▷ η.app c ▷ θ.app c ≫
            (α_ _ _ _).hom ▷ _ ≫ (α_ _ _ _).hom ≫
              F.map f ◁ η.naturality g ▷ θ.app c ≫
                _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫
                  (F.map f ≫ η.app b) ◁ θ.naturality g ≫
                    η.naturality f ▷ (θ.app b ≫ H.map g) ≫
                      (α_ _ _ _).hom ≫ _ ◁ (α_ _ _ _).inv ≫
                        η.app a ◁ θ.naturality f ▷ H.map g ≫
                          _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv := by
        rw [whisker_exchange_assoc]; simp
      _ = _ := by simp

/-- `CategoryStruct` on `OplaxFunctor B C` where the (1-)morphisms are given by oplax
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
scoped instance : CategoryStruct (OplaxFunctor B C) where
  Hom := OplaxTrans
  id := OplaxTrans.id
  comp := OplaxTrans.vcomp

end OplaxTrans

/-- A strong natural transformation between oplax functors `F` and `G` is a natural transformation
that is "natural up to 2-isomorphisms".

More precisely, it consists of the following:
* a 1-morphism `η.app a : F.obj a ⟶ G.obj a` for each object `a : B`.
* a 2-isomorphism `η.naturality f : F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism
  `f : a ⟶ b`.
* These 2-isomorphisms satisfy the naturality condition, and preserve the identities and the
  compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
structure StrongTrans (F G : OplaxFunctor B C) where
  app (a : B) : F.obj a ⟶ G.obj a
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ≅ app a ≫ G.map f
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      F.map₂ η ▷ app b ≫ (naturality g).hom = (naturality f).hom ≫ app a ◁ G.map₂ η := by
    cat_disch
  naturality_id (a : B) :
      (naturality (𝟙 a)).hom ≫ app a ◁ G.mapId a =
        F.mapId a ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv := by
    cat_disch
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      (naturality (f ≫ g)).hom ≫ app a ◁ G.mapComp f g =
        F.mapComp f g ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫
        (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom := by
    cat_disch

attribute [nolint docBlame] CategoryTheory.Oplax.StrongTrans.app
  CategoryTheory.Oplax.StrongTrans.naturality

attribute [reassoc (attr := simp)] StrongTrans.naturality_naturality
  StrongTrans.naturality_id StrongTrans.naturality_comp

/-- A structure on an oplax transformation that promotes it to a strong transformation.

See `Pseudofunctor.StrongTrans.mkOfOplax`. -/
structure OplaxTrans.StrongCore {F G : OplaxFunctor B C} (η : F ⟶ G) where
  /-- The underlying 2-isomorphisms of the naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ η.app b ≅ η.app a ≫ G.map f
  /-- The 2-isomorphisms agree with the underlying 2-morphism of the oplax transformation. -/
  naturality_hom {a b : B} (f : a ⟶ b) : (naturality f).hom = η.naturality f := by cat_disch

attribute [simp] OplaxTrans.StrongCore.naturality_hom

namespace StrongTrans

/-- The underlying oplax natural transformation of a strong natural transformation. -/
@[simps]
def toOplax {F G : OplaxFunctor B C} (η : StrongTrans F G) : OplaxTrans F G where
  app := η.app
  naturality f := (η.naturality f).hom

/-- Construct a strong natural transformation from an oplax natural transformation whose
naturality 2-morphism is an isomorphism. -/
def mkOfOplax {F G : OplaxFunctor B C} (η : OplaxTrans F G) (η' : OplaxTrans.StrongCore η) :
    StrongTrans F G where
  app := η.app
  naturality := η'.naturality

/-- Construct a strong natural transformation from an oplax natural transformation whose
naturality 2-morphism is an isomorphism. -/
noncomputable def mkOfOplax' {F G : OplaxFunctor B C} (η : OplaxTrans F G)
    [∀ a b (f : a ⟶ b), IsIso (η.naturality f)] : StrongTrans F G where
  app := η.app
  naturality _ := asIso (η.naturality _)

variable (F : OplaxFunctor B C)


/-- The identity strong natural transformation. -/
@[simps!]
def id : StrongTrans F F :=
  mkOfOplax (OplaxTrans.id F) { naturality := fun f ↦ (ρ_ (F.map f)) ≪≫ (λ_ (F.map f)).symm }

@[simp]
lemma id.toOplax : (id F).toOplax = OplaxTrans.id F :=
  rfl

instance : Inhabited (StrongTrans F F) :=
  ⟨id F⟩


variable {F} {G H : OplaxFunctor B C} (η : StrongTrans F G) (θ : StrongTrans G H)

/-- Vertical composition of strong natural transformations. -/
@[simps!]
def vcomp : StrongTrans F H :=
  mkOfOplax (OplaxTrans.vcomp η.toOplax θ.toOplax)
    { naturality := fun {a b} f ↦
        (α_ _ _ _).symm ≪≫ whiskerRightIso (η.naturality f) (θ.app b) ≪≫
        (α_ _ _ _) ≪≫ whiskerLeftIso (η.app a) (θ.naturality f) ≪≫ (α_ _ _ _).symm }

/-- `CategoryStruct` on `OplaxFunctor B C` where the (1-)morphisms are given by strong
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
scoped instance OplaxFunctor.instCategoryStruct : CategoryStruct (OplaxFunctor B C) where
  Hom := StrongTrans
  id := StrongTrans.id
  comp := StrongTrans.vcomp

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp), to_app]
theorem whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ (θ.naturality h).hom =
      f ◁ (θ.naturality g).hom ≫ f ◁ θ.app a ◁ H.map₂ β := by
  apply θ.toOplax.whiskerLeft_naturality_naturality

@[reassoc (attr := simp), to_app]
theorem whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') :
    F.map₂ β ▷ η.app b ▷ h ≫ (η.naturality g).hom ▷ h =
      (η.naturality f).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h ≫ (α_ _ _ _).inv :=
  η.toOplax.whiskerRight_naturality_naturality _ _

@[reassoc (attr := simp), to_app]
theorem whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
    f ◁ (θ.naturality (g ≫ h)).hom ≫ f ◁ θ.app a ◁ H.mapComp g h =
      f ◁ G.mapComp g h ▷ θ.app c ≫
        f ◁ (α_ _ _ _).hom ≫
          f ◁ G.map g ◁ (θ.naturality h).hom ≫
            f ◁ (α_ _ _ _).inv ≫ f ◁ (θ.naturality g).hom ▷ H.map h ≫ f ◁ (α_ _ _ _).hom :=
  θ.toOplax.whiskerLeft_naturality_comp _ _ _

@[reassoc (attr := simp), to_app]
theorem whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
    (η.naturality (f ≫ g)).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapComp f g ▷ h =
      F.mapComp f g ▷ η.app c ▷ h ≫
        (α_ _ _ _).hom ▷ h ≫
          (α_ _ _ _).hom ≫
            F.map f ◁ (η.naturality g).hom ▷ h ≫
              (α_ _ _ _).inv ≫
                (α_ _ _ _).inv ▷ h ≫
                 (η.naturality f).hom ▷ G.map g ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom :=
  η.toOplax.whiskerRight_naturality_comp _ _ _

@[reassoc (attr := simp), to_app]
theorem whiskerLeft_naturality_id (f : a' ⟶ G.obj a) :
    f ◁ (θ.naturality (𝟙 a)).hom ≫ f ◁ θ.app a ◁ H.mapId a =
      f ◁ G.mapId a ▷ θ.app a ≫ f ◁ (λ_ (θ.app a)).hom ≫ f ◁ (ρ_ (θ.app a)).inv :=
  θ.toOplax.whiskerLeft_naturality_id _

@[reassoc (attr := simp), to_app]
theorem whiskerRight_naturality_id (f : G.obj a ⟶ a') :
    (η.naturality (𝟙 a)).hom ▷ f ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapId a ▷ f =
    F.mapId a ▷ η.app a ▷ f ≫ (λ_ (η.app a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫
    (α_ _ _ _).hom :=
  η.toOplax.whiskerRight_naturality_id _

end

end StrongTrans

end CategoryTheory.Oplax
