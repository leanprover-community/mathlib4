/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne, Robin Carlier
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Lax

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
  condition is given by a 2-morphism `F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism
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

variable {F : LaxFunctor B C} {G H : LaxFunctor B C} (η : LaxTrans F G) (θ : LaxTrans G H)

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    f ◁ θ.naturality g ≫ f ◁ G.map₂ β ▷ θ.app b =
    f ◁ θ.app a ◁ H.map₂ β ≫ f ◁ θ.naturality h := by
  simp_rw [← Bicategory.whiskerLeft_comp, naturality_naturality]

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') :
    η.naturality f ▷ h ≫ F.map₂ β ▷ η.app b ▷ h =
    (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h  ≫ (α_ _ _ _).inv ≫ η.naturality g ▷ h := by
  rw [← comp_whiskerRight, naturality_naturality, comp_whiskerRight, whisker_assoc,
    Category.assoc, Category.assoc]

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
    f ◁ θ.app a ◁ H.mapComp g h ≫ f ◁ θ.naturality (g ≫ h) =
    f ◁ (α_ _ _ _).inv ≫ f ◁ θ.naturality g ▷ H.map h ≫ f ◁ (α_ _ _ _).hom ≫
      f ◁ G.map g ◁ θ.naturality h ≫ f ◁ (α_ _ _ _).inv ≫ f ◁ G.mapComp g h ▷ θ.app c := by
  simp_rw [← Bicategory.whiskerLeft_comp, naturality_comp]

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
    (α_ _ _ _).hom ≫ η.app a ◁ G.mapComp f g ▷ h ≫ (α_ _ _ _).inv ≫
      η.naturality (f ≫ g) ▷ h =
    (α_ _ _ _).inv ▷ h ≫
      η.naturality f ▷ G.map g ▷ h ≫
      (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom ≫
      F.map f ◁ η.naturality g ▷ h ≫ (α_ _ _ _).inv ≫
      (α_ _ _ _).inv ▷ h ≫ F.mapComp f g ▷ η.app c ▷ h := by
  simpa [-naturality_comp] using congr_arg (fun t ↦ t ▷ h) <| naturality_comp _ _ _

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_id (f : a' ⟶ G.obj a) :
    f ◁ θ.app a ◁ H.mapId a ≫ f ◁ θ.naturality (𝟙 a) =
    (α_ _ _ _).inv ≫ (ρ_ (f ≫ θ.app a)).hom ≫ f ◁ (λ_ (θ.app a)).inv ≫
      f ◁ G.mapId a ▷ θ.app a := by
  simpa [-naturality_id] using congr_arg (fun t ↦ f ◁ t) <| naturality_id _ _

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_id (f : G.obj a ⟶ a') :
    (α_ _ _ _).hom ≫ η.app a ◁ G.mapId a ▷ f ≫ (α_ _ _ _).inv ≫ η.naturality (𝟙 a) ▷ f =
    (ρ_ (η.app a)).hom ▷ f ≫ (λ_ (η.app a ≫ f)).inv ≫ (α_ _ _ _).inv ≫ F.mapId a ▷ η.app a ▷ f := by
  simpa [-naturality_id] using congr_arg (fun t ↦ t ▷ f) <| naturality_id _ _

end

variable (F) in
/-- The identity lax transformation. -/
def id : LaxTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {_ _} f := (λ_ (F.map f)).hom ≫ (ρ_ (F.map f)).inv

instance : Inhabited (LaxTrans F F) :=
  ⟨id F⟩

/-- Vertical composition of lax transformations. -/
@[simps]
def vcomp : LaxTrans F H where
  app a := η.app a ≫ θ.app a
  naturality {a b} f :=
    (α_ _ _ _).hom ≫ η.app a ◁ (θ.naturality f) ≫ (α_ _ _ _).inv ≫
      η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom
  naturality_comp {a b c} f g := by
    calc
      _ = (α_ _ _ _).hom ≫ _ ◁ (α_ _ _ _).inv  ≫
            η.app a ◁ θ.naturality f ▷ H.map g ≫
            _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫
            η.naturality f ▷ (θ.app b ≫ H.map g) ≫
            (F.map f ≫ η.app b) ◁ θ.naturality g ≫
            (α_ _ _ _).hom ≫ F.map f ◁ (α_ _ _ _).inv ≫
            F.map f ◁ η.naturality g ▷ θ.app c ≫
            (α_ _ _ _).inv ≫ (α_ _ _ _).inv ▷ _ ≫
            F.mapComp f g ▷ η.app c ▷ θ.app c ≫ (α_ _ _ _).hom := by
        rw [← whisker_exchange_assoc]
        simp only [← whisker_exchange_assoc, comp_whiskerLeft, assoc, Iso.inv_hom_id_assoc,
          whiskerLeft_naturality_comp_assoc, Bicategory.whiskerRight_comp,
          pentagon_hom_hom_inv_hom_hom_assoc, Iso.cancel_iso_hom_left,
          associator_inv_naturality_middle_assoc]
        simp
      _ = _ := by simp
  naturality_id x := by
    simp only [comp_whiskerLeft, assoc, Iso.inv_hom_id_assoc, whiskerLeft_naturality_id_assoc,
      Iso.hom_inv_id_assoc, Bicategory.whiskerRight_comp, Iso.cancel_iso_hom_left,
      associator_inv_naturality_middle_assoc]
    simp

/-- `CategoryStruct` on `LaxFunctor B C` where the (1-)morphisms are given by lax
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
scoped instance : CategoryStruct (LaxFunctor B C) where
  Hom := LaxTrans
  id := LaxTrans.id
  comp := LaxTrans.vcomp

end LaxTrans

/-- A strong natural transformation between lax functors `F` and `G` is a natural transformation
that is "natural up to 2-isomorphisms".

More precisely, it consists of the following:
* a 1-morphism `η.app a : F.obj a ⟶ G.obj a` for each object `a : B`.
* a 2-isomorphism `η.naturality f : F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism
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
def vcomp : StrongTrans F H :=
  mkOfLax (LaxTrans.vcomp η.toLax θ.toLax)
    { naturality := fun {a b} f ↦
        (α_ _ _ _) ≪≫ whiskerLeftIso (η.app a) (θ.naturality f) ≪≫ (α_ _ _ _).symm ≪≫
        whiskerRightIso (η.naturality f) (θ.app b) ≪≫ (α_ _ _ _) }

/-- `CategoryStruct` on `LaxFunctor B C` where the (1-)morphisms are given by strong
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
scoped instance LaxFunctor.instCategoryStruct : CategoryStruct (LaxFunctor B C) where
  Hom := StrongTrans
  id := StrongTrans.id
  comp := StrongTrans.vcomp

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp), to_app]
theorem whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    f ◁ (θ.naturality g).hom ≫ f ◁ G.map₂ β ▷ θ.app b =
    f ◁ θ.app a ◁ H.map₂ β ≫ f ◁ (θ.naturality h).hom := by
  apply θ.toLax.whiskerLeft_naturality_naturality

@[reassoc (attr := simp), to_app]
theorem whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') :
    (η.naturality f).hom ▷ h ≫ F.map₂ β ▷ η.app b ▷ h =
    (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h  ≫ (α_ _ _ _).inv ≫ (η.naturality g).hom ▷ h :=
  η.toLax.whiskerRight_naturality_naturality _ _

@[reassoc (attr := simp), to_app]
theorem whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
    f ◁ θ.app a ◁ H.mapComp g h ≫ f ◁ (θ.naturality (g ≫ h)).hom =
    f ◁ (α_ _ _ _).inv ≫ f ◁ (θ.naturality g).hom ▷ H.map h ≫ f ◁ (α_ _ _ _).hom ≫
      f ◁ G.map g ◁ (θ.naturality h).hom ≫ f ◁ (α_ _ _ _).inv ≫ f ◁ G.mapComp g h ▷ θ.app c  :=
  θ.toLax.whiskerLeft_naturality_comp _ _ _

@[reassoc (attr := simp), to_app]
theorem whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
    (α_ _ _ _).hom ≫ η.app a ◁ G.mapComp f g ▷ h ≫ (α_ _ _ _).inv ≫
      (η.naturality (f ≫ g)).hom ▷ h =
    (α_ _ _ _).inv ▷ h ≫
      (η.naturality f).hom ▷ G.map g ▷ h ≫
      (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom ≫
      F.map f ◁ (η.naturality g).hom ▷ h ≫ (α_ _ _ _).inv ≫
      (α_ _ _ _).inv ▷ h ≫ F.mapComp f g ▷ η.app c ▷ h :=
  η.toLax.whiskerRight_naturality_comp _ _ _

@[reassoc (attr := simp), to_app]
theorem whiskerLeft_naturality_id (f : a' ⟶ G.obj a) :
    f ◁ θ.app a ◁ H.mapId a ≫ f ◁ (θ.naturality (𝟙 a)).hom =
    (α_ _ _ _).inv ≫ (ρ_ (f ≫ θ.app a)).hom ≫ f ◁ (λ_ (θ.app a)).inv ≫
      f ◁ G.mapId a ▷ θ.app a :=
  θ.toLax.whiskerLeft_naturality_id _

@[reassoc (attr := simp), to_app]
theorem whiskerRight_naturality_id (f : G.obj a ⟶ a') :
    (α_ _ _ _).hom ≫ η.app a ◁ G.mapId a ▷ f ≫ (α_ _ _ _).inv ≫ (η.naturality (𝟙 a)).hom ▷ f =
    (ρ_ (η.app a)).hom ▷ f ≫ (λ_ (η.app a ≫ f)).inv ≫ (α_ _ _ _).inv ≫ F.mapId a ▷ η.app a ▷ f :=
  η.toLax.whiskerRight_naturality_id _

end

end StrongTrans

end CategoryTheory.Lax
