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

* `StrongNatTrans F G` : strong natural transformations between oplax functors `F` and `G`.
* `mkOfOplax η η'` : given an oplax natural transformation `η` such that each component 2-cell
  is an isomorphism, `mkOfOplax` gives the corresponding strong natural transformation.
* `StrongNatTrans.vcomp η θ` : the vertical composition of strong natural transformations `η`
  and `θ`.
* `StrongNatTrans.category F G` : a category structure on pseudofunctors between `F` and `G`,
  where the morphisms are strong natural transformations.

## TODO

After having defined lax functors, we should define 3 different types of strong natural
transformations:
* strong natural transformations between oplax functors (as defined here).
* strong natural transformations between lax functors.
* strong natural transformations between pseudofunctors. From these types of strong natural
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
structure StrongNatTrans (F G : OplaxFunctor B C) where
  app (a : B) : F.obj a ⟶ G.obj a
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ≅ app a ≫ G.map f
  naturality_naturality :
    ∀ {a b : B} {f g : a ⟶ b} (η : f ⟶ g),
      F.map₂ η ▷ app b ≫ (naturality g).hom = (naturality f).hom ≫ app a ◁ G.map₂ η := by
    aesop_cat
  naturality_id :
    ∀ a : B,
      (naturality (𝟙 a)).hom ≫ app a ◁ G.mapId a =
        F.mapId a ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv := by
    aesop_cat
  naturality_comp :
    ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
      (naturality (f ≫ g)).hom ≫ app a ◁ G.mapComp f g =
        F.mapComp f g ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫
        (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom := by
    aesop_cat

attribute [nolint docBlame] CategoryTheory.StrongNatTrans.app
  CategoryTheory.StrongNatTrans.naturality
  CategoryTheory.StrongNatTrans.naturality_naturality
  CategoryTheory.StrongNatTrans.naturality_id
  CategoryTheory.StrongNatTrans.naturality_comp

attribute [reassoc (attr := simp)] StrongNatTrans.naturality_naturality StrongNatTrans.naturality_id
  StrongNatTrans.naturality_comp

namespace StrongNatTrans

section

/-- The underlying oplax natural transformation of a strong natural transformation. -/
@[simps]
def toOplax {F G : OplaxFunctor B C} (η : StrongNatTrans F G) : OplaxNatTrans F G where
  app := η.app
  naturality f := (η.naturality f).hom

/-- Construct a strong natural transformation from an oplax natural transformation whose
naturality 2-cell is an isomorphism. -/
def mkOfOplax {F G : OplaxFunctor B C} (η : OplaxNatTrans F G) (η' : OplaxNatTrans.StrongCore η) :
    StrongNatTrans F G where
  app := η.app
  naturality := η'.naturality

/-- Construct a strong natural transformation from an oplax natural transformation whose
naturality 2-cell is an isomorphism. -/
noncomputable def mkOfOplax' {F G : OplaxFunctor B C} (η : OplaxNatTrans F G)
    [∀ a b (f : a ⟶ b), IsIso (η.naturality f)] : StrongNatTrans F G where
  app := η.app
  naturality := fun f => asIso (η.naturality _)

variable (F : OplaxFunctor B C)


/-- The identity oplax natural transformation. -/
@[simps!]
def id : StrongNatTrans F F :=
  mkOfOplax (OplaxNatTrans.id F) { naturality := λ f ↦ (ρ_ (F.map f)) ≪≫ (λ_ (F.map f)).symm }

@[simp]
lemma id.toOplax : (id F).toOplax = OplaxNatTrans.id F :=
  rfl

instance : Inhabited (StrongNatTrans F F) :=
  ⟨id F⟩

variable {F} {G H : OplaxFunctor B C} (η : StrongNatTrans F G) (θ : StrongNatTrans G H)

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ (θ.naturality h).hom =
      f ◁ (θ.naturality g).hom ≫ f ◁ θ.app a ◁ H.map₂ β := by
  apply θ.toOplax.whiskerLeft_naturality_naturality

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') :
    F.map₂ β ▷ η.app b ▷ h ≫ (η.naturality g).hom ▷ h =
      (η.naturality f).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h ≫ (α_ _ _ _).inv := by
  apply η.toOplax.whiskerRight_naturality_naturality

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
    f ◁ (θ.naturality (g ≫ h)).hom ≫ f ◁ θ.app a ◁ H.mapComp g h =
      f ◁ G.mapComp g h ▷ θ.app c ≫
        f ◁ (α_ _ _ _).hom ≫
          f ◁ G.map g ◁ (θ.naturality h).hom ≫
            f ◁ (α_ _ _ _).inv ≫ f ◁ (θ.naturality g).hom ▷ H.map h ≫ f ◁ (α_ _ _ _).hom := by
  apply θ.toOplax.whiskerLeft_naturality_comp

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
    (η.naturality (f ≫ g)).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapComp f g ▷ h =
      F.mapComp f g ▷ η.app c ▷ h ≫
        (α_ _ _ _).hom ▷ h ≫
          (α_ _ _ _).hom ≫
            F.map f ◁ (η.naturality g).hom ▷ h ≫
              (α_ _ _ _).inv ≫
                (α_ _ _ _).inv ▷ h ≫
                 (η.naturality f).hom ▷ G.map g ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom := by
  apply η.toOplax.whiskerRight_naturality_comp

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_id (f : a' ⟶ G.obj a) :
    f ◁ (θ.naturality (𝟙 a)).hom ≫ f ◁ θ.app a ◁ H.mapId a =
      f ◁ G.mapId a ▷ θ.app a ≫ f ◁ (λ_ (θ.app a)).hom ≫ f ◁ (ρ_ (θ.app a)).inv := by
  apply θ.toOplax.whiskerLeft_naturality_id

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_id (f : G.obj a ⟶ a') :
    (η.naturality (𝟙 a)).hom ▷ f ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapId a ▷ f =
    F.mapId a ▷ η.app a ▷ f ≫ (λ_ (η.app a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫
    (α_ _ _ _).hom := by
  apply η.toOplax.whiskerRight_naturality_id

end

/-- Vertical composition of oplax natural transformations. -/
@[simps!]
def vcomp (η : StrongNatTrans F G) (θ : StrongNatTrans G H) : StrongNatTrans F H :=
  mkOfOplax (OplaxNatTrans.vcomp η.toOplax θ.toOplax)
    { naturality := λ {a b} f ↦
        (α_ _ _ _).symm ≪≫ whiskerRightIso (η.naturality f) (θ.app b) ≪≫
        (α_ _ _ _) ≪≫ whiskerLeftIso (η.app a) (θ.naturality f) ≪≫ (α_ _ _ _).symm }

variable (B C)

@[simps id comp]
instance : CategoryStruct (Pseudofunctor B C) where
  Hom F G := StrongNatTrans F.toOplax G.toOplax
  id F := StrongNatTrans.id F.toOplax
  comp := StrongNatTrans.vcomp

end

section

-- TODO: move up?
open OplaxNatTrans

/-- Category structure on the strong natural transformations between pseudofunctors. -/
@[simps]
instance homcategory (F G : Pseudofunctor B C) : Category (F ⟶ G) where
  Hom η θ := Modification η.toOplax θ.toOplax
  id η := Modification.id η.toOplax
  comp := Modification.vcomp

-- Porting note: duplicating the `ext` lemma.
-- TODO: needed?
@[ext]
lemma ext {F G : Pseudofunctor B C} {α β : F ⟶ G} {m n : α ⟶ β} (w : ∀ b, m.app b = n.app b) :
    m = n :=
  OplaxNatTrans.ext w

-- -- TODO: ARE THESE NEEDED?
-- @[simp]
-- lemma Modification.id_app' {X : B} {F G : Pseudofunctor B C} (α : F ⟶ G) :
--     Modification.app (𝟙 α) X = 𝟙 (α.app X) := rfl

-- @[simp]
-- lemma Modification.comp_app' {X : B} {F G : Pseudofunctor B C} {α β γ : F ⟶ G}
--     (m : α ⟶ β) (n : β ⟶ γ) : (m ≫ n).app X = m.app X ≫ n.app X :=
--   rfl

-- -- TODO: I might need this one!
-- -- /-- Construct a modification isomorphism between oplax natural transformations
-- -- by giving object level isomorphisms, and checking naturality only in the forward direction.
-- -- -/
-- @[simps]
-- def ModificationIso.ofComponents {F G : Pseudofunctor B C} {η θ : F ⟶ G}
--     (app : ∀ a, η.app a ≅ θ.app a)
--     (naturality : ∀ {a b} (f : a ⟶ b),
--       F.map f ◁ (app b).hom ≫ (θ.naturality f).hom = (η.naturality f).hom ≫ (app a).hom ▷ G.map f) :
--     η ≅ θ where
--   hom := { app := fun a => (app a).hom }
--   inv :=
--     { app := fun a => (app a).inv
--       naturality := fun {a b} f => by
--         rw [←whiskerRightIso_inv, Iso.eq_comp_inv, assoc]
--         rw [←whiskerLeftIso_inv, Iso.inv_comp_eq]
--         apply (naturality f).symm }

end

end StrongNatTrans

end CategoryTheory
