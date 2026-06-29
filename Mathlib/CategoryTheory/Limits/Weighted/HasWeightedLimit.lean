/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Yun Liu, Christian Merten, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Elements

/-!
# Weighted limits

-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory

open Limits

namespace Limits

variable {J : Type u} [Category.{v} J] {C : Type*} [Category* C]

abbrev WeightedCone (W : J ⥤ Type w) (F : J ⥤ C) :=
  Cone (CategoryOfElements.π W ⋙ F)

abbrev HasWeightedLimit (W : J ⥤ Type w) (F : J ⥤ C) : Prop :=
  HasLimit (CategoryOfElements.π W ⋙ F)

namespace WeightedCone

variable {W : J ⥤ Type w} {F : J ⥤ C}

protected abbrev π (c : WeightedCone W F) {j : J} (x : W.obj j) :
    c.pt ⟶ F.obj j :=
  (Cone.π c).app (Functor.elementsMk _ _ x)

variable (pt : C) (π : ∀ ⦃j : J⦄ (_ : W.obj j), pt ⟶ F.obj j)
  (hπ : ∀ ⦃j₁ j₂ : J⦄ (x : W.obj j₁) (f : j₁ ⟶ j₂),
    π x ≫ F.map f = π (W.map f x))

set_option backward.defeqAttrib.useBackward true in
@[simps pt]
def mk : WeightedCone W F where
  pt := pt
  π.app x := π x.snd
  π.naturality x₁ x₂ f := by simpa using (hπ x₁.snd f.val).symm

@[simp]
lemma mk_π {j : J} (x : W.obj j) :
    (mk pt π hπ).π x = π x := rfl

protected abbrev IsLimit (c : WeightedCone W F) := Limits.IsLimit c

namespace IsLimit

variable {c : WeightedCone W F} (hc : c.IsLimit) {Z : C}

section

variable
  (π : ∀ ⦃j : J⦄ (_ : W.obj j), Z ⟶ F.obj j)
  (hπ : ∀ ⦃j₁ j₂ : J⦄ (x : W.obj j₁) (f : j₁ ⟶ j₂),
    π x ≫ F.map f = π (W.map f x))

def lift : Z ⟶ c.pt :=
  Limits.IsLimit.lift hc (WeightedCone.mk Z π hπ)

@[reassoc (attr := simp)]
lemma fac {j : J} (x : W.obj j) :
    hc.lift π hπ ≫ c.π x = π x :=
  Limits.IsLimit.fac hc (WeightedCone.mk Z π hπ) (Functor.elementsMk _ _ x)

end

include hc in
lemma hom_ext {f g : Z ⟶ c.pt} (h : ∀ {j : J} (x : W.obj j), f ≫ c.π x = g ≫ c.π x) :
    f = g :=
  Limits.IsLimit.hom_ext hc (fun _ ↦ h _)

end IsLimit

open Opposite in
set_option backward.defeqAttrib.useBackward true in
@[simps]
protected abbrev coyoneda (F : J ⥤ C) (j : J) :
    WeightedCone (coyoneda.obj (op j)) F where
  pt := F.obj j
  π.app u := F.map u.snd
  π.naturality _ _ f := by
    dsimp
    simp only [← Functor.map_comp, Category.id_comp]
    congr 1
    exact f.prop.symm

set_option backward.defeqAttrib.useBackward true in
def isLimitCoyoneda (F : J ⥤ C) (j : J) : (WeightedCone.coyoneda F j).IsLimit where
  lift s := WeightedCone.π s (𝟙 j)
  fac s x := by
    simpa using s.w (⟨x.snd, Category.id_comp _⟩ : Functor.elementsMk _ j (𝟙 j) ⟶ x)
  uniq s m hm := by
    simpa using hm (Functor.elementsMk _ j (𝟙 j))

end WeightedCone

end Limits

namespace Functor

variable {J : Type u} [Category.{v} J] (W : J ⥤ Type w) {C : Type*} [Category* C]

section

variable (F : J ⥤ C) [HasWeightedLimit W F]

noncomputable def weightedLimObj : C :=
  limit (CategoryOfElements.π W ⋙ F)

@[no_expose]
noncomputable def weightedLimObjπ ⦃j : J⦄ (x : W.obj j) :
    W.weightedLimObj F ⟶ F.obj j :=
  limit.π (CategoryOfElements.π W ⋙ F) (Functor.elementsMk _ _ x)

@[reassoc (attr := simp)]
lemma weightedLimObjObj_w ⦃j₁ j₂ : J⦄ (x : W.obj j₁)
    (f : j₁ ⟶ j₂) :
    W.weightedLimObjπ F x ≫ F.map f =
      W.weightedLimObjπ F (W.map f x) := by
  let g : Functor.elementsMk _ _ x ⟶ Functor.elementsMk _ _ (W.map f x) := ⟨f, rfl⟩
  exact limit.w (CategoryOfElements.π W ⋙ F) g

noncomputable abbrev weightedLimCone :
    WeightedCone W F :=
  WeightedCone.mk (W.weightedLimObj F)
    (fun j x ↦ W.weightedLimObjπ F x)
    (fun j₁ j₂ x f ↦ by simp)

@[no_expose]
noncomputable def isLimitWeightedLimCone :
    (W.weightedLimCone F).IsLimit :=
  limit.isLimit _

variable {W F} in
@[ext]
lemma weightedLim.hom_ext {Z : C} {f g : Z ⟶ W.weightedLimObj F}
    (h : ∀ {j : J} (x : W.obj j),
      f ≫ W.weightedLimObjπ F x = g ≫ W.weightedLimObjπ F x) :
    f = g :=
  (W.isLimitWeightedLimCone F).hom_ext h

end

@[no_expose]
noncomputable def weightedLimMap {F₁ F₂ : J ⥤ C}
    [HasWeightedLimit W F₁] [HasWeightedLimit W F₂] (f : F₁ ⟶ F₂) :
    W.weightedLimObj F₁ ⟶ W.weightedLimObj F₂ :=
  limMap (whiskerLeft _ f)

@[reassoc (attr := simp)]
lemma weightedLimMap_π {F₁ F₂ : J ⥤ C}
    [HasWeightedLimit W F₁] [HasWeightedLimit W F₂] (f : F₁ ⟶ F₂)
    ⦃j : J⦄ (x : W.obj j) :
    W.weightedLimMap f ≫ W.weightedLimObjπ F₂ x =
      W.weightedLimObjπ F₁ x ≫ f.app j :=
  limit.lift_π ..

@[simp]
lemma weightedLimMap_id (F : J ⥤ C) [HasWeightedLimit W F] :
    W.weightedLimMap (𝟙 F) = 𝟙 _ := by
  cat_disch

@[reassoc]
lemma weightedLimMap_comp {F₁ F₂ F₃ : J ⥤ C}
    [HasWeightedLimit W F₁] [HasWeightedLimit W F₂] [HasWeightedLimit W F₃]
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃):
    W.weightedLimMap f ≫ W.weightedLimMap g = W.weightedLimMap (f ≫ g) := by
  cat_disch

variable (C) in
abbrev HasWeightedLimits (W : J ⥤ Type w) (C : Type*) [Category* C] : Prop :=
    ∀ (F : J ⥤ C), HasWeightedLimit W F

variable [W.HasWeightedLimits C]

@[implicit_reducible, simps]
noncomputable def weightedLim : (J ⥤ C) ⥤ C where
  obj F := W.weightedLimObj F
  map f := W.weightedLimMap f

end Functor

end CategoryTheory
