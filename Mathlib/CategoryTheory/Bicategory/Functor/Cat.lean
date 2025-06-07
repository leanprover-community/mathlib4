/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Strict

/-!
# Pseudofunctors to Cat

In this file, the equalities stated in `CategoryTheory.Bicategory.Functor.Strict`
for pseudofunctors (from a strict bicategory) are rephrased in the particular
case the target bicategory is `Cat`. Indeed, in that case, the general lemmas
for pseudofunctors involve equalities between natural transformations:
we rephrase them after the application of `NatTrans.app`.

-/

namespace CategoryTheory

open Bicategory

namespace Pseudofunctor

variable {B : Type*} [Bicategory B] (F : Pseudofunctor B Cat)

attribute [local simp] Cat.leftUnitor_hom_app Cat.rightUnitor_hom_app
  Cat.leftUnitor_inv_app Cat.rightUnitor_inv_app
  Cat.associator_hom_app Cat.associator_inv_app

section naturality

variable {b₀ b₁ b₂ : B} {X Y : F.obj b₀}

section

variable (f : b₀ ⟶ b₀) (hf : f = 𝟙 b₀) (a : X ⟶ Y)

@[reassoc]
lemma mapId'_hom_naturality :
    (F.map f).map a ≫ (F.mapId' f hf).hom.app Y = (F.mapId' f hf).hom.app X ≫ a :=
  (F.mapId' f hf).hom.naturality a

@[reassoc]
lemma mapId'_inv_naturality :
    (F.mapId' f hf).inv.app X ≫ (F.map f).map a = a ≫ (F.mapId' f hf).inv.app Y :=
  ((F.mapId' f hf).inv.naturality a).symm

end

section

variable (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
  (hfg : f ≫ g = fg) (a : X ⟶ Y)

@[reassoc]
lemma mapComp'_hom_naturality :
    (F.map fg).map a ≫ (F.mapComp' f g fg hfg).hom.app Y =
      (F.mapComp' f g fg hfg).hom.app X ≫ (F.map g).map ((F.map f).map a) :=
  (F.mapComp' f g fg hfg).hom.naturality a

@[reassoc (attr := simp)]
lemma mapComp'_inv_naturality :
    (F.map g).map ((F.map f).map a) ≫ (F.mapComp' f g fg hfg).inv.app Y =
    (F.mapComp' f g fg hfg).inv.app X ≫ (F.map fg).map a :=
  (F.mapComp' f g fg hfg).inv.naturality a

@[reassoc]
lemma mapComp'_naturality_1 :
    (F.mapComp' f g fg hfg).inv.app X ≫
      (F.map fg).map a ≫ (F.mapComp' f g fg hfg).hom.app Y =
      (F.map g).map ((F.map f).map a) :=
  NatIso.naturality_1 (F.mapComp' f g fg hfg) a

@[reassoc]
lemma mapComp'_naturality_2 :
    (F.mapComp' f g fg hfg).hom.app X ≫ (F.map g).map ((F.map f).map a) ≫
      (F.mapComp' f g fg hfg).inv.app Y =
      (F.map fg).map a :=
  NatIso.naturality_2 (F.mapComp' f g fg hfg) a

end

end naturality

variable [Strict B]

section unitality

variable {b₀ b₁ : B} (f : b₀ ⟶ b₁) (X : F.obj b₀)

lemma mapComp'_comp_id_hom_app :
    (F.mapComp' f (𝟙 b₁) f).hom.app X = (F.mapId b₁).inv.app ((F.map f).obj X) := by
  simp [mapComp'_comp_id]

lemma mapComp'_comp_id_inv_app :
    (F.mapComp' f (𝟙 b₁) f).inv.app X = (F.mapId b₁).hom.app ((F.map f).obj X) := by
  simp [mapComp'_comp_id]

lemma mapComp'_id_comp_hom_app :
    (F.mapComp' (𝟙 b₀) f f).hom.app X = (F.map f).map ((F.mapId b₀).inv.app X) := by
  simp [mapComp'_id_comp]

lemma mapComp'_id_comp_inv_app :
    (F.mapComp' (𝟙 b₀) f f).inv.app X = (F.map f).map ((F.mapId b₀).hom.app X) := by
  simp [mapComp'_id_comp]

end unitality

section associativity

variable {b₀ b₁ b₂ b₃ : B} (f₀₁ : b₀ ⟶ b₁)
  (f₁₂ : b₁ ⟶ b₂) (f₂₃ : b₂ ⟶ b₃) (f₀₂ : b₀ ⟶ b₂) (f₁₃ : b₁ ⟶ b₃) (f : b₀ ⟶ b₃)
  (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃)

@[reassoc]
lemma mapComp'_hom_app_comp_mapComp'_hom_app_map_obj (hf : f₀₁ ≫ f₁₃ = f) (X : F.obj b₀) :
    (F.mapComp' f₀₁ f₁₃ f).hom.app X ≫
      (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom.app ((F.map f₀₁).obj X) =
      (F.mapComp' f₀₂ f₂₃ f).hom.app X ≫
        (F.map f₂₃).map ((F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom.app X) := by
  simpa using NatTrans.congr_app (F.mapComp'_hom_comp_whiskerLeft_mapComp'_hom
    f₀₁ f₁₂ f₂₃ f₀₂ f₁₃ f h₀₂ h₁₃ hf) X

@[reassoc]
lemma mapComp'_inv_app_comp_mapComp'_hom_app (hf : f₀₁ ≫ f₁₃ = f) (X : F.obj b₀) :
    (F.mapComp' f₀₁ f₁₃ f).inv.app X ≫ (F.mapComp' f₀₂ f₂₃ f).hom.app X =
      (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom.app ((F.map f₀₁).obj X) ≫
        (F.map f₂₃).map ((F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv.app X) := by
  simpa using NatTrans.congr_app (F.mapComp'_inv_comp_mapComp'_hom
    f₀₁ f₁₂ f₂₃ f₀₂ f₁₃ f h₀₂ h₁₃ hf) X

@[reassoc]
lemma mapComp'_inv_app_map_obj_comp_mapComp'_inv_app (hf : f₀₁ ≫ f₁₃ = f) (X : F.obj b₀) :
    (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).inv.app ((F.map f₀₁).obj X) ≫ (F.mapComp' f₀₁ f₁₃ f).inv.app X =
    (F.map f₂₃).map ((F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv.app X) ≫
      (F.mapComp' f₀₂ f₂₃ f).inv.app X := by
  simpa using NatTrans.congr_app (F.whiskerLeft_mapComp'_inv_comp_mapComp'_inv
    f₀₁ f₁₂ f₂₃ f₀₂ f₁₃ f h₀₂ h₁₃ hf) X

@[reassoc]
lemma mapComp'_hom_app_comp_map_map_mapComp'_hom_app (hf : f₀₂ ≫ f₂₃ = f) (X : F.obj b₀) :
    (F.mapComp' f₀₂ f₂₃ f).hom.app X ≫ (F.map f₂₃).map ((F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom.app X) =
      (F.mapComp' f₀₁ f₁₃ f).hom.app X ≫
        (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom.app ((F.map f₀₁).obj X) := by
  simpa using NatTrans.congr_app (F.mapComp'_hom_comp_mapComp'_hom_whiskerRight
    f₀₁ f₁₂ f₂₃ f₀₂ f₁₃ f h₀₂ h₁₃ hf) X

@[reassoc]
lemma map_map_mapComp'_inv_app_comp_mapComp'_inv_app (hf : f₀₂ ≫ f₂₃ = f) (X : F.obj b₀) :
    (F.map f₂₃).map ((F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv.app X) ≫ (F.mapComp' f₀₂ f₂₃ f).inv.app X =
    (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).inv.app ((F.map f₀₁).obj X) ≫
      (F.mapComp' f₀₁ f₁₃ f).inv.app X := by
  simpa using NatTrans.congr_app (F.mapComp'_inv_whiskerRight_comp_mapComp'_inv
    f₀₁ f₁₂ f₂₃ f₀₂ f₁₃ f h₀₂ h₁₃ hf) X

@[reassoc]
lemma mapComp'₀₁₃_inv_app (hf : f₀₁ ≫ f₁₃ = f) (X : F.obj b₀) :
    (F.mapComp' f₀₁ f₁₃ f hf).inv.app X =
      (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom.app ((F.map f₀₁).obj X) ≫
        (F.map f₂₃).map ((F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv.app X) ≫
          (F.mapComp' f₀₂ f₂₃ f).inv.app X := by
  rw [← F.mapComp'_inv_app_comp_mapComp'_hom_app_assoc _ _ _ _ _ _ _ _ hf X,
    Iso.hom_inv_id_app, Category.comp_id]

@[reassoc]
lemma mapComp'₀₁₃_hom_app (hf : f₀₁ ≫ f₁₃ = f) (X : F.obj b₀) :
    (F.mapComp' f₀₁ f₁₃ f hf).hom.app X =
      (F.mapComp' f₀₂ f₂₃ f).hom.app X ≫
        (F.map f₂₃).map ((F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom.app X) ≫
          (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).inv.app ((F.map f₀₁).obj X) := by
  rw [← F.mapComp'_hom_app_comp_mapComp'_hom_app_map_obj_assoc _ _ _ _ _ _ h₀₂ h₁₃ hf X]
  simp

@[reassoc]
lemma mapComp'_inv_app_comp_mapComp'_hom_app' (hf : f₀₁ ≫ f₁₃ = f) (X : F.obj b₀) :
    (F.mapComp' f₀₂ f₂₃ f).inv.app X ≫ (F.mapComp' f₀₁ f₁₃ f).hom.app X =
    (F.map f₂₃).map ((F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom.app X) ≫
      (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).inv.app ((F.map f₀₁).obj X) := by
  simp [F.mapComp'₀₁₃_hom_app f₀₁ f₁₂ f₂₃ f₀₂ f₁₃ f h₀₂ h₁₃ hf]

@[reassoc]
lemma mapComp'_hom_app_comp_mapComp'_inv_app (hf : f₀₁ ≫ f₁₃ = f) (X : F.obj b₀) :
    (F.mapComp' f₀₂ f₂₃ f).inv.app X ≫ (F.mapComp' f₀₁ f₁₃ f).hom.app X =
      (F.map f₂₃).map ((F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom.app X) ≫
      (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).inv.app ((F.map f₀₁).obj X) := by
  simp [F.mapComp'₀₁₃_hom_app f₀₁ f₁₂ f₂₃ f₀₂ f₁₃ f h₀₂ h₁₃ hf]


end associativity

end Pseudofunctor

end CategoryTheory
