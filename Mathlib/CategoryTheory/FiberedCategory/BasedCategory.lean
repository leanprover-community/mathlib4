/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import Mathlib.CategoryTheory.FiberedCategory.HomLift
import Mathlib.CategoryTheory.Bicategory.Strict
import Mathlib.CategoryTheory.Functor.Category

/-!
# The bicategory of based categories

In this file we define the type `BasedCategory 𝒮`, and give it the structure of a strict
bicategory. Given a category `𝒮`, we define the type `BasedCategory 𝒮` as the type of categories
`𝒳` equiped with a functor `𝒳.p : 𝒳 ⥤ 𝒮`.

We also define functors between based categories `𝒳 𝒴 : BasedCategory 𝒮`, via the structure
`BasedFunctor 𝒳 𝒴`. These are defined as functors between the underlying categories `𝒳.cat` and
`𝒴.cat` which commute with the projections to `𝒮`.

Natural transformations between based functors `F G : BasedFunctor 𝒳 𝒴` are given by the structure
`BasedNatTrans F G`. These are defined as natural transformations `α` between the functors
underlying `F` and `G` such that `α.app a` lifts `𝟙 S` whenever `𝒳.p.obj a = S`.
-/

universe u₁ v₁ u₂ v₂

open CategoryTheory Functor Category NatTrans IsHomLift

namespace Fibered

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- A based category over `𝒮` is a category `𝒳` together with a functor `p : 𝒳 ⥤ 𝒮` -/
structure BasedCategory (𝒮 : Type u₁) [Category.{v₁} 𝒮] where
  (cat : Type u₂)
  [isCat : Category.{v₂} cat]
  (p : cat ⥤ 𝒮)

instance (𝒳 : BasedCategory 𝒮) : Category 𝒳.cat := 𝒳.isCat

/-- A functor between based categories is a functor between the underlying categories that commutes with the projections. -/
structure BasedFunctor (𝒳 𝒴 : BasedCategory 𝒮) extends CategoryTheory.Functor 𝒳.cat 𝒴.cat where
  (w : toFunctor ⋙ 𝒴.p = 𝒳.p)

namespace BasedFunctor

/-- The identity functor is also a `BasedFunctor` -/
@[simps!]
protected def id (𝒳 : BasedCategory 𝒮) : BasedFunctor 𝒳 𝒳 :=
  { 𝟭 𝒳.cat with w := CategoryTheory.Functor.id_comp _ }

section

variable {𝒳 𝒴 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴)

/-- Composition of `BasedFunctor`s is defined as the composition of the underlying functors -/
@[simps!]
def comp {𝒵 : BasedCategory 𝒮} (G : BasedFunctor 𝒴 𝒵) : BasedFunctor 𝒳 𝒵 :=
  { F.toFunctor ⋙ G.toFunctor with w := by rw [Functor.assoc, G.w, F.w] }

@[simp]
lemma assoc {𝒵 𝒯 : BasedCategory 𝒮} (G : BasedFunctor 𝒴 𝒵) (H : BasedFunctor 𝒵 𝒯) :
    comp (comp F G) H = comp F (comp G H) :=
  rfl

@[simp]
lemma comp_id : comp (BasedFunctor.id 𝒳) F = F :=
  rfl

@[simp]
lemma id_comp : comp F (BasedFunctor.id 𝒴) = F :=
  rfl

@[simp]
lemma w_obj (a : 𝒳.cat) : 𝒴.p.obj (F.obj a) = 𝒳.p.obj a := by
  rw [←Functor.comp_obj, F.w]

/-- For a based functor `F : 𝒳 ⟶ 𝒴`, if an arrow `φ` in `𝒳` lifts some `f` in `𝒮`, then `F(φ)`
also lifts `f` -/
instance pres_IsHomLift {R S : 𝒮} {a b : 𝒳.cat} (f : R ⟶ S) (φ : a ⟶ b) [IsHomLift 𝒳.p f φ] :
    IsHomLift 𝒴.p f (F.map φ) := by
  apply of_fac 𝒴.p f (F.map φ) (Eq.trans (F.w_obj a) (domain_eq 𝒳.p f φ))
    (Eq.trans (F.w_obj b) (codomain_eq 𝒳.p f φ))
  rw [←Functor.comp_map, congr_hom F.w]
  simpa using (fac 𝒳.p f φ)

/-- For a based functor `F`, `F(φ)` always lifts `𝒳.p(φ)` -/
-- instance map_isHomLift {a b : 𝒳.cat} (φ : a ⟶ b) : IsHomLift 𝒴.p (𝒳.p.map φ) (F.map φ) :=
--   inferInstance

instance map_isHomLift (a : 𝒳.cat) : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (𝟙 (F.obj a)) := by
  simp_rw [← Functor.map_id]; infer_instance

/-- For a based functor `F : 𝒳 ⟶ 𝒴`, and an arrow `φ` in `𝒳`, then `φ` lifts an arrow `f` in `𝒮`
if `F(φ)` does -/
lemma IsHomLift_ofImage {S R : 𝒮} {a b : 𝒳.cat} (f : R ⟶ S) (φ : a ⟶ b)
    [IsHomLift 𝒴.p f (F.map φ)] : IsHomLift 𝒳.p f φ := by
  apply of_fac 𝒳.p f φ  (F.w_obj a ▸ domain_eq 𝒴.p f (F.map φ))
    (F.w_obj b ▸ codomain_eq 𝒴.p f (F.map φ))
  simp [congr_hom F.w.symm, fac 𝒴.p f (F.map φ)]

lemma IsHomLift_iff {S R : 𝒮} {a b : 𝒳.cat} {φ : a ⟶ b} {f : R ⟶ S} :
    IsHomLift 𝒴.p f (F.map φ) ↔ IsHomLift 𝒳.p f φ :=
  ⟨fun _ => IsHomLift_ofImage F f φ, fun _ => pres_IsHomLift F f φ⟩

end

end BasedFunctor

-- TODO: another costum .mk function here!

/-- A `BasedNatTrans` between two `BasedFunctor`s is a natural transformation `α` between the underlying functors,
    such that for all `a : 𝒳`, `α.app a` lifts `𝟙 S` whenever `𝒳.p.obj a = S`. -/
structure BasedNatTrans {𝒳 𝒴 : BasedCategory 𝒮} (F G : BasedFunctor 𝒳 𝒴) extends
    CategoryTheory.NatTrans F.toFunctor G.toFunctor where
  (aboveId : ∀ {a : 𝒳.cat} {S : 𝒮} (_ : 𝒳.p.obj a = S), IsHomLift 𝒴.p (𝟙 S) (toNatTrans.app a) := by aesop_cat)

namespace BasedNatTrans

variable {𝒳 𝒴 : BasedCategory 𝒮}

instance app_isHomLift {F G : BasedFunctor 𝒳 𝒴} (α : BasedNatTrans F G) (a : 𝒳.cat) :
    IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (α.toNatTrans.app a) :=
  α.aboveId rfl

@[ext]
lemma ext {F G : BasedFunctor 𝒳 𝒴} (α β : BasedNatTrans F G)
    (h : α.toNatTrans = β.toNatTrans) : α = β := by
  cases α; subst h; rfl

/-- The identity natural transformation is a `BasedNatTrans` -/
@[simps!]
def id (F : BasedFunctor 𝒳 𝒴) : BasedNatTrans F F where
  toNatTrans := CategoryTheory.NatTrans.id F.toFunctor
  aboveId := by
    intro a S ha
    apply of_fac 𝒴.p (𝟙 S) _
    rotate_left
    any_goals rwa [←CategoryTheory.Functor.comp_obj, F.w]
    simp

@[simp]
lemma id_toNatTrans (F : BasedFunctor 𝒳 𝒴) :
    (id F).toNatTrans = CategoryTheory.NatTrans.id F.toFunctor :=
  rfl

/-- Composition of `BasedNatTrans`s, given by composition of the underlying natural transformations -/
@[simps!]
def comp {F G H : BasedFunctor 𝒳 𝒴} (α : BasedNatTrans F G)
    (β : BasedNatTrans G H) : BasedNatTrans F H where
  toNatTrans := CategoryTheory.NatTrans.vcomp α.toNatTrans β.toNatTrans
  aboveId := by
    intro a S ha
    rw [CategoryTheory.NatTrans.vcomp_app]
    subst ha
    infer_instance

-- TODO: do I need these three lemmas...?

@[simp]
lemma CategoryTheory.NatTrans.id_vcomp {C D : Type _} [Category C] [Category D] {F G : C ⥤ D}
    (f : NatTrans F G) : NatTrans.vcomp (NatTrans.id F) f = f := by
  aesop_cat

@[simp]
lemma CategoryTheory.NatTrans.vcomp_id {C D : Type _} [Category C] [Category D] {F G : C ⥤ D}
    (f : NatTrans F G) : NatTrans.vcomp f (NatTrans.id G) = f := by
  aesop_cat

@[simp]
lemma comp_toNatTrans {F G H : BasedFunctor 𝒳 𝒴} (α : BasedNatTrans F G) (β : BasedNatTrans G H) :
    (comp α β).toNatTrans = NatTrans.vcomp α.toNatTrans β.toNatTrans :=
  rfl

@[simp]
lemma id_comp {F G : BasedFunctor 𝒳 𝒴} (α : BasedNatTrans F G) : comp (id F) α = α := by
  ext1; rw [comp_toNatTrans, id_toNatTrans, CategoryTheory.NatTrans.id_vcomp]

@[simp]
lemma comp_id {F G : BasedFunctor 𝒳 𝒴} (α : BasedNatTrans F G) : comp α (id G) = α := by
  ext1; rw [comp_toNatTrans, id_toNatTrans, CategoryTheory.NatTrans.vcomp_id]

lemma comp_assoc {F G H I : BasedFunctor 𝒳 𝒴} (α : BasedNatTrans F G) (β : BasedNatTrans G H)
    (γ : BasedNatTrans H I) : comp (comp α β) γ = comp α (comp β γ):= by
  ext1
  rw [comp_toNatTrans, comp_toNatTrans, comp_toNatTrans, comp_toNatTrans, NatTrans.vcomp_eq_comp, NatTrans.vcomp_eq_comp, NatTrans.vcomp_eq_comp, NatTrans.vcomp_eq_comp, assoc]

end BasedNatTrans

@[simps]
instance homCategory (𝒳 𝒴 : BasedCategory 𝒮) : Category (BasedFunctor 𝒳 𝒴) where
  Hom := BasedNatTrans
  id := BasedNatTrans.id
  comp := BasedNatTrans.comp
  -- TODO: can maybe remove these three? (will they still be simp lemmas then?)
  id_comp := BasedNatTrans.id_comp
  comp_id := BasedNatTrans.comp_id
  assoc := BasedNatTrans.comp_assoc

@[ext]
lemma homCategory.ext {𝒳 𝒴 : BasedCategory 𝒮} {F G : BasedFunctor 𝒳 𝒴} (α β : F ⟶ G)
    (h : α.toNatTrans = β.toNatTrans) : α = β :=
  BasedNatTrans.ext α β h

-- TODO: I should be able to recycle the identical code in the next few definitions

/-- The associator in the bicategory `BasedCategory` is given by the identity -/
@[simps]
def BasedFunctor.associator {𝒳 𝒴 𝒵 𝒱 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒴 𝒵)
    (H : BasedFunctor 𝒵 𝒱) : BasedFunctor.comp (BasedFunctor.comp F G) H ≅
      BasedFunctor.comp F (BasedFunctor.comp G H) where
    hom := {
      app := fun _ => 𝟙 _
      -- can this be automated?
      aboveId := by
        intro a S ha
        subst ha
        infer_instance
    }
    inv := {
      app := fun _ => 𝟙 _
      aboveId := by
        intro a S ha
        subst ha
        infer_instance
    }

/-- The left unitor in the bicategory `BasedCategory` is given by the identity -/
@[simps]
def BasedFunctor.leftUnitor {𝒳 𝒴 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴) :
  BasedFunctor.comp (BasedFunctor.id 𝒳) F ≅ F where
    hom := {
      app := fun a => 𝟙 (F.obj a)
      aboveId := by
        intro a S ha
        subst ha
        infer_instance
    }
    inv := {
      app := fun a => 𝟙 (F.obj a)
      aboveId := by
        intro a S ha
        subst ha
        infer_instance
    }

/-- The right unitor in the bicategory `BasedCategory` is given by the identity -/
@[simps]
def BasedFunctor.rightUnitor {𝒳 𝒴 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴) :
  BasedFunctor.comp F (BasedFunctor.id 𝒴) ≅ F where
    hom := {
      app := fun a => 𝟙 (F.obj a)
      aboveId := by
        intro a S ha
        subst ha
        infer_instance
    }
    inv := {
      app := fun a => 𝟙 (F.obj a)
      aboveId := by
        intro a S ha
        subst ha
        infer_instance
    }

/-- Left-whiskering in the bicategory `BasedCategory` is given by whiskering the underlying functors
    and natural transformations -/
@[simps!]
def BasedCategory.whiskerLeft {𝒳 𝒴 𝒵 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴)
    {G H : BasedFunctor 𝒴 𝒵} (α : G ⟶ H) : BasedFunctor.comp F G ⟶ BasedFunctor.comp F H where
  toNatTrans := CategoryTheory.whiskerLeft F.toFunctor α.toNatTrans
  aboveId := by
    intro a S ha
    apply α.aboveId
    simp only [BasedFunctor.w_obj, ha]

/-- Right-whiskering in the bicategory `BasedCategory` is given by whiskering the underlying functors
    and natural transformations -/
@[simps!]
def BasedCategory.whiskerRight {𝒳 𝒴 𝒵 : BasedCategory 𝒮} {F G : BasedFunctor 𝒳 𝒴} (α : F ⟶ G)
    (H : BasedFunctor 𝒴 𝒵) : BasedFunctor.comp F H ⟶ BasedFunctor.comp G H where
  toNatTrans := CategoryTheory.whiskerRight α.toNatTrans H.toFunctor
  aboveId := by
    intro a S ha
    subst ha
    apply BasedFunctor.pres_IsHomLift

-- TODO: aesop no longer solves these.....

/-- `BasedCategory 𝒮` forms a bicategory -/
instance BasedCategory.bicategory : Bicategory (BasedCategory 𝒮) where
  Hom := BasedFunctor
  id := BasedFunctor.id
  comp := BasedFunctor.comp
  homCategory 𝒳 𝒴 := homCategory 𝒳 𝒴
  whiskerLeft := BasedCategory.whiskerLeft
  whiskerRight {𝒳 𝒴 𝒵} F G α H := BasedCategory.whiskerRight α H
  associator := BasedFunctor.associator
  leftUnitor {𝒳 𝒴} F := BasedFunctor.leftUnitor F
  rightUnitor {𝒳 𝒴} F := BasedFunctor.rightUnitor F

/-- The bicategory structure on `BasedCategory 𝒮` is strict -/
instance : Bicategory.Strict (BasedCategory 𝒮) where
  id_comp := BasedFunctor.id_comp
  comp_id := BasedFunctor.comp_id
  assoc := BasedFunctor.assoc

end Fibered
