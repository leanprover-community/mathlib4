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

universe u₁ v₁

open CategoryTheory Functor Category NatTrans IsHomLift

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- A based category over `𝒮` is a category `𝒳` together with a functor `p : 𝒳 ⥤ 𝒮` -/
structure BasedCategory (𝒮 : Type u₁) [Category.{v₁} 𝒮] where
  /-- The type of objects in a `BasedCategory`-/
  cat : Type u₁
  /-- The underlying category of a `BasedCategory` -/
  isCat : Category.{v₁} cat
  /-- The functor to the base -/
  p : cat ⥤ 𝒮

instance (𝒳 : BasedCategory 𝒮) : Category 𝒳.cat := 𝒳.isCat

/-- A functor between based categories is a functor between the underlying categories that commutes
with the projections. -/
structure BasedFunctor (𝒳 𝒴 : BasedCategory 𝒮) extends CategoryTheory.Functor 𝒳.cat 𝒴.cat where
  w : toFunctor ⋙ 𝒴.p = 𝒳.p := by aesop_cat

namespace BasedFunctor

/-- The identity functor is also a `BasedFunctor` -/
@[simps!]
protected def id (𝒳 : BasedCategory 𝒮) : BasedFunctor 𝒳 𝒳 where
  toFunctor := 𝟭 𝒳.cat

section

variable {𝒳 𝒴 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴)

/-- Composition of `BasedFunctor`s is defined as the composition of the underlying functors -/
-- should I have simps here...? Messes with automation later
@[simps!]
def comp {𝒵 : BasedCategory 𝒮} (G : BasedFunctor 𝒴 𝒵) : BasedFunctor 𝒳 𝒵 where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  w := by rw [Functor.assoc, G.w, F.w]

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
  rw [← Functor.comp_obj, F.w]

instance (a : 𝒳.cat) : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (𝟙 (F.obj a)) :=
  IsHomLift.id (w_obj F a)

section

variable {R S : 𝒮} {a b : 𝒳.cat} (f : R ⟶ S) (φ : a ⟶ b)

/-- For a based functor `F : 𝒳 ⟶ 𝒴`, then whenever an arrow `φ` in `𝒳` lifts some `f` in `𝒮`,
then `F(φ)` also lifts `f` -/
instance pres_IsHomLift [IsHomLift 𝒳.p f φ] : IsHomLift 𝒴.p f (F.map φ) := by
  apply of_fac 𝒴.p f (F.map φ) (Eq.trans (F.w_obj a) (domain_eq 𝒳.p f φ))
    (Eq.trans (F.w_obj b) (codomain_eq 𝒳.p f φ))
  rw [← Functor.comp_map, congr_hom F.w]
  simpa using (fac 𝒳.p f φ)

/-- For a based functor `F : 𝒳 ⟶ 𝒴`, and an arrow `φ` in `𝒳`, then `φ` lifts an arrow `f` in `𝒮`
if `F(φ)` does -/
lemma IsHomLift_ofImage [IsHomLift 𝒴.p f (F.map φ)] : IsHomLift 𝒳.p f φ := by
  apply of_fac 𝒳.p f φ  (F.w_obj a ▸ domain_eq 𝒴.p f (F.map φ))
    (F.w_obj b ▸ codomain_eq 𝒴.p f (F.map φ))
  simp [congr_hom F.w.symm, fac 𝒴.p f (F.map φ)]

lemma IsHomLift_iff : IsHomLift 𝒴.p f (F.map φ) ↔ IsHomLift 𝒳.p f φ :=
  ⟨fun _ => IsHomLift_ofImage F f φ, fun _ => pres_IsHomLift F f φ⟩

end

end

end BasedFunctor

/-- A `BasedNatTrans` between two `BasedFunctor`s is a natural transformation `α` between the
underlying functors, such that for all `a : 𝒳`, `α.app a` lifts `𝟙 S` whenever `𝒳.p.obj a = S`. -/
structure BasedNatTrans {𝒳 𝒴 : BasedCategory 𝒮} (F G : BasedFunctor 𝒳 𝒴) extends
    CategoryTheory.NatTrans F.toFunctor G.toFunctor where
  aboveId' : ∀ (a : 𝒳.cat), IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (toNatTrans.app a) := by aesop_cat

namespace BasedNatTrans

open BasedFunctor

variable {𝒳 𝒴 : BasedCategory 𝒮}

/-- The identity natural transformation is a `BasedNatTrans` -/
@[simps!]
def id (F : BasedFunctor 𝒳 𝒴) : BasedNatTrans F F where
  toNatTrans := CategoryTheory.NatTrans.id F.toFunctor
  aboveId' := by
    intro a
    apply of_fac 𝒴.p _ _ (w_obj F a) (w_obj F a)
    simp

@[simp]
lemma id_toNatTrans (F : BasedFunctor 𝒳 𝒴) :
    (id F).toNatTrans = CategoryTheory.NatTrans.id F.toFunctor :=
  rfl

section

variable {F G : BasedFunctor 𝒳 𝒴} (α : BasedNatTrans F G)

instance app_isHomLift (a : 𝒳.cat) : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (α.toNatTrans.app a) :=
  α.aboveId' a

lemma aboveId {a : 𝒳.cat} {S : 𝒮} (ha : 𝒳.p.obj a = S) :
    IsHomLift 𝒴.p (𝟙 S) (α.toNatTrans.app a) := by
  subst ha; infer_instance

@[ext]
lemma ext (β : BasedNatTrans F G) (h : α.toNatTrans = β.toNatTrans) : α = β := by
  cases α; subst h; rfl

end

/-- Composition of `BasedNatTrans`, given by composition of the underlying natural
transformations -/
@[simps!]
def comp {F G H : BasedFunctor 𝒳 𝒴} (α : BasedNatTrans F G) (β : BasedNatTrans G H) :
    BasedNatTrans F H where
  toNatTrans := CategoryTheory.NatTrans.vcomp α.toNatTrans β.toNatTrans
  aboveId' := by
    intro a
    rw [CategoryTheory.NatTrans.vcomp_app]
    infer_instance

@[simp]
lemma comp_toNatTrans {F G H : BasedFunctor 𝒳 𝒴} (α : BasedNatTrans F G) (β : BasedNatTrans G H) :
    (comp α β).toNatTrans = NatTrans.vcomp α.toNatTrans β.toNatTrans :=
  rfl

end BasedNatTrans

namespace BasedCategory

open BasedFunctor BasedNatTrans

@[simps!]
instance homCategory (𝒳 𝒴 : BasedCategory 𝒮) : Category (BasedFunctor 𝒳 𝒴) where
  Hom := BasedNatTrans
  id := BasedNatTrans.id
  comp := BasedNatTrans.comp

section

variable {𝒳 𝒴 : BasedCategory 𝒮}

@[ext]
lemma homCategory.ext {F G : BasedFunctor 𝒳 𝒴} (α β : F ⟶ G) (h : α.toNatTrans = β.toNatTrans) :
    α = β :=
  BasedNatTrans.ext α β h

-- /-- The inverse of a based natural transformation whose underlying natural tranformation is an
-- isomorphism -/
-- def BasedNatIso {F G : BasedFunctor 𝒳 𝒴} (α : F.toFunctor ≅ G.toFunctor)
--     (aboveId' : ∀ a : 𝒳.cat, IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (α.hom.app a)) : F ≅ G where
--   hom := { toNatTrans := α.hom }
--   inv := {
--     toNatTrans := α.inv
--     aboveId' := by
--       intro a
--       specialize aboveId' a
--       rw [← NatIso.app_inv]
--       rw [← NatIso.app_hom] at aboveId'
--       apply IsHomLift.lift_id_inv
--   }

-- /-- The inverse of a based natural transformation whose underlying natural tranformation carries
-- an
-- `IsIso` instance. -/
-- noncomputable def BasedNatIso_of_isIso {F G : BasedFunctor 𝒳 𝒴} (α : F.toFunctor ⟶ G.toFunctor)
--     [IsIso α] (aboveId' : ∀ a : 𝒳.cat, IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (α.app a)) : F ≅ G where
--   hom := { toNatTrans := α }
--   inv := { toNatTrans := inv α, aboveId' := fun a => by simp [lift_id_inv_isIso] }

/-- The identity natural transformation is a based natural isomorphism -/
@[simps]
def BasedNatIso.id (F : BasedFunctor 𝒳 𝒴) : F ≅ F where
  hom := 𝟙 F
  inv := 𝟙 F

/-- Left-whiskering in the bicategory `BasedCategory` is given by whiskering the underlying functors
and natural transformations -/
@[simps!]
def whiskerLeft {𝒵 : BasedCategory 𝒮} (F : BasedFunctor 𝒳 𝒴) {G H : BasedFunctor 𝒴 𝒵}
    (α : G ⟶ H) : BasedFunctor.comp F G ⟶ BasedFunctor.comp F H where
  toNatTrans := CategoryTheory.whiskerLeft F.toFunctor α.toNatTrans
  aboveId' := fun a => α.aboveId (F.w_obj a)

/-- Right-whiskering in the bicategory `BasedCategory` is given by whiskering the underlying
functors and natural transformations -/
@[simps!]
def whiskerRight {𝒵 : BasedCategory 𝒮} {F G : BasedFunctor 𝒳 𝒴} (α : F ⟶ G)
    (H : BasedFunctor 𝒴 𝒵) : BasedFunctor.comp F H ⟶ BasedFunctor.comp G H where
  toNatTrans := CategoryTheory.whiskerRight α.toNatTrans H.toFunctor
  aboveId' := fun a => by apply BasedFunctor.pres_IsHomLift

end

/-- `BasedCategory 𝒮` forms a bicategory -/
instance bicategory : Bicategory (BasedCategory 𝒮) where
  Hom 𝒳 𝒴 := BasedFunctor 𝒳 𝒴
  id 𝒳 := BasedFunctor.id 𝒳
  comp F G := BasedFunctor.comp F G
  homCategory 𝒳 𝒴 := homCategory 𝒳 𝒴
  whiskerLeft {𝒳 𝒴 𝒵} F {G H} α := whiskerLeft F α
  whiskerRight {𝒳 𝒴 𝒵} F G α H := whiskerRight α H
  associator F G H := BasedNatIso.id _
  leftUnitor {𝒳 𝒴} F := BasedNatIso.id F
  rightUnitor {𝒳 𝒴} F := BasedNatIso.id F

/-- The bicategory structure on `BasedCategory 𝒮` is strict -/
instance : Bicategory.Strict (BasedCategory 𝒮) where
  id_comp F := BasedFunctor.id_comp F
  comp_id F := BasedFunctor.comp_id F
  assoc F G H := BasedFunctor.assoc F G H

end BasedCategory
