/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Monoidal.Limits.Shapes.Pullback

/-!
# Monoidal structure on the arrow category of a cartesian closed category.

If `C` is a braided, cartesian closed category with pushouts and an initial object, then `Arrow C`
has a symmetric monoidal category structure given by the pushout-product (the Leibniz construction
given by the tensor product on `C`).

If `C` also has pullbacks, then `Arrow C` has a monoidal closed structure given by the pullback-hom
(the Leibniz construction given by the internal hom on `C`).

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits MonoidalCategory Functor PushoutObjObj

variable {C : Type u} [Category.{v} C]

attribute [local simp] PushoutObjObj.ι ofHasPushout_pt ofHasPushout_inl ofHasPushout_inr

namespace MonoidalCategory

namespace Arrow

/-- The Leibniz functor associated to the tensor product on a monoidal category. This is the
bifunctor of arrow categories that sends `f : A ⟶ B` and `g : X ⟶ Y` to the canonical map from the
pushout of `f ◁ X` and `A ▷ g` to `B ⊗ Y`, induced by the following diagram:
```
  A ⊗ X --> B ⊗ X
     |          |
     v          v
  A ⊗ Y --> B ⊗ Y
```
-/
noncomputable
abbrev pushoutProduct [HasPushouts C] [MonoidalCategory C] := (curriedTensor C).leibnizPushout

/-- Notation for the pushout-product of morphisms. -/
notation3 f " □ " g:10 => (pushoutProduct.obj f).obj g

/-- The Leibniz functor associated to the internal hom on a monoidal closed category. This is the
bifunctor of arrow categories that sends `f : A ⟶ B` and `g : X ⟶ Y` to the canonical map from
`B ⟹ X` to the pullback of `(ihom A).map g : A ⟹ X ⟶ A ⟹ Y` and
`(pre f).app Y : B ⟹ Y ⟶ A ⟹ Y`, induced by the following diagram:
```
  B ⟹ X --> A ⟹ X
     |          |
     v          v
  B ⟹ Y --> A ⟹ Y
```
-/
noncomputable
abbrev pullbackHom [HasPullbacks C] [MonoidalCategory C] [MonoidalClosed C] :
    (Arrow C)ᵒᵖ ⥤ Arrow C ⥤ Arrow C := MonoidalClosed.internalHom.leibnizPullback

/-- Notation for the pullback-hom of morphisms. -/
notation3 f " ⋔ " g:10 => (pullbackHom.obj f).obj g

section PushoutProduct

variable [HasPushouts C]

section Monoidal

variable [MonoidalCategory C] (X₁ X₂ X₃ : Arrow C) {W : C}

/-- Left-whiskering the pushout-product of `X₁` and `X₂` with `W : C` is isomorphic to the
  pushout-product of `W ◁ X₁` and `X₂`. -/
@[simps!]
noncomputable
def PushoutProduct.whiskerLeft_iso
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) (tensorLeft W)] :
    Arrow.mk (W ◁ (X₁ □ X₂).hom) ≅ (W ◁ X₁.hom) □ X₂ :=
  Arrow.isoMk (((tensorLeft W).map_isPushout
    (IsPushout.of_hasPushout (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom))).isoPushout ≪≫
    HasColimit.isoOfNatIso (spanExt (α_ W _ _).symm (α_ W _ _).symm (α_ W _ _).symm
    (associator_inv_naturality_middle W _ _).symm (associator_inv_naturality_right W _ _).symm))
  (α_ W _ _).symm
  (((tensorLeft W).map_isPushout
    (IsPushout.of_hasPushout (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom))).hom_ext (by simp) (by simp))

/-- Right-whiskering the pushout-product of `X₁` and `X₂` with `W : C` is isomorphic to the
  pushout-product of `X₁` and `X₂ ▷ W`. -/
@[simps!]
noncomputable
def PushoutProduct.whiskerRight_iso
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) (tensorRight W)] :
    Arrow.mk ((X₁ □ X₂).hom ▷ W) ≅ X₁ □ (X₂.hom ▷ W) :=
  Arrow.isoMk
    (((tensorRight W).map_isPushout
      (IsPushout.of_hasPushout (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom))).isoPushout ≪≫
      HasColimit.isoOfNatIso (spanExt (α_ _ _ W) (α_ _ _ W) (α_ _ _ W)
      (associator_naturality_left _ _ W).symm (associator_naturality_middle _ _ W).symm))
    (α_ _ _ W)
    (((tensorRight W).map_isPushout
      (IsPushout.of_hasPushout (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom))).hom_ext (by simp) (by simp))

/-- The pushout-product is associative: `(X₁ □ X₂) □ X₃ ≅ X₁ □ X₂ □ X₃`. -/
@[simps!]
noncomputable
def PushoutProduct.associator
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) (tensorRight X₃.left)]
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) (tensorRight X₃.right)]
    [PreservesColimit (span (X₂.hom ▷ X₃.left) (X₂.left ◁ X₃.hom)) (tensorLeft X₁.left)]
    [PreservesColimit (span (X₂.hom ▷ X₃.left) (X₂.left ◁ X₃.hom)) (tensorLeft X₁.right)] :
    ((X₁ □ X₂) □ X₃) ≅ X₁ □ X₂ □ X₃ := by
  dsimp
  refine Arrow.isoMk ?_ (α_ _ _ _) ?_
  · refine Iso.mk ?_ ?_ ?_ ?_
    · exact pushout.desc ((α_ _ _ _).hom ≫ _ ◁ pushout.inl _ _ ≫ pushout.inl _ _)
        ((whiskerRight_iso _ _).hom.left ≫
          pushout.desc (_ ◁ pushout.inr _ _ ≫ pushout.inl _ _) (pushout.inr _ _)
          (by simp [Limits.pushout.associator_naturality_left_condition]))
        (((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
          (by simp [Limits.pushout.whiskerLeft_condition_assoc, ← whisker_exchange_assoc])
          (by simp [← whisker_exchange_assoc, Limits.pushout.associator_naturality_left_condition]))
    · exact pushout.desc ((whiskerLeft_iso _ _).hom.left ≫
          pushout.desc (pushout.inl _ _) ((pushout.inl _ _ ▷ _) ≫ pushout.inr _ _)
          (by simp [Limits.pushout.associator_inv_naturality_right_condition]))
        ((α_ _ _ _).inv ≫ (pushout.inr _ _) ▷ _ ≫ pushout.inr _ _)
        (((tensorLeft _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
          (by simp [whisker_exchange_assoc,
            Limits.pushout.associator_inv_naturality_right_condition])
          (by simp [whisker_exchange_assoc, Limits.pushout.condition_whiskerRight_assoc]))
    · apply pushout.hom_ext
      · simp
      · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext <;> simp
    · apply pushout.hom_ext
      · apply ((tensorLeft _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext <;> simp
      · simp
  · apply pushout.hom_ext
    · simp [← MonoidalCategory.whiskerLeft_comp]
    · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
      · simp [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.comp_whiskerRight_assoc]
      · simp [← MonoidalCategory.comp_whiskerRight_assoc]

/-- The pushout-product is commutative: `X₁ □ X₂ ≅ X₂ □ X₁`. -/
@[simps!]
noncomputable
def PushoutProduct.braiding [BraidedCategory C] (X₁ X₂ : Arrow C) : (X₁ □ X₂) ≅ X₂ □ X₁ :=
  Arrow.isoMk (pushoutSymmetry _ _ ≪≫
    (HasColimit.isoOfNatIso (spanExt (β_ _ _) (β_ _ _) (β_ _ _)
    (BraidedCategory.braiding_naturality_right _ _).symm
    (BraidedCategory.braiding_naturality_left _ _).symm))) (β_ _ _) (by cat_disch)

end Monoidal

section CartesianMonoidalClosed

variable [HasInitial C] [CartesianMonoidalCategory C] [MonoidalClosed C]

/-- If `C` is a CCC with pushouts and an initial object, then `X □ (⊥_ C ⟶ 𝟙_ C) ≅ X`. -/
@[simp]
noncomputable
def PushoutProduct.rightUnitor (X : Arrow C) :
    (X □ initial.to (𝟙_ C)) ≅ X := by
  refine Arrow.isoMk ?_ (ρ_ X.right) ?_
  · refine Iso.mk ?_ ((ρ_ X.left).inv ≫ pushout.inr _ _) ?_ ?_
    · refine pushout.desc ?_ (ρ_ X.left).hom ?_
      · exact (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).to _
      · apply (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).hom_ext
    · apply pushout.hom_ext
      · apply (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).hom_ext
      · simp
    · simp
  · apply pushout.hom_ext
    · apply (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).hom_ext
    · simp

/-- If `C` is a braided CCC with pushouts and an initial object, then `(⊥_ C ⟶ 𝟙_ C) □ X ≅ X`. -/
@[simp]
noncomputable
def PushoutProduct.leftUnitor [BraidedCategory C]
    (X : Arrow C) : (initial.to (𝟙_ C) □ X) ≅ X :=
  braiding _ _ ≪≫ rightUnitor _

end CartesianMonoidalClosed

end PushoutProduct

noncomputable section

local instance [MonoidalCategory C] [MonoidalClosed C] :
    ∀ S : C, PreservesColimitsOfSize (tensorLeft S) := fun S ↦
  (ihom.adjunction S).leftAdjoint_preservesColimits

local instance [MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C] :
    ∀ S : C, PreservesColimitsOfSize (tensorRight S) := fun S ↦
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight S)

@[simps]
instance [HasPushouts C] [HasInitial C] [CartesianMonoidalCategory C] [MonoidalClosed C]
    [BraidedCategory C] : MonoidalCategoryStruct (Arrow C) where
  tensorObj X Y := X □ Y
  whiskerLeft X _ _ f := (pushoutProduct.obj X).map f
  whiskerRight f X := (pushoutProduct.map f).app X
  tensorUnit := initial.to (𝟙_ C)
  associator _ _ _ := PushoutProduct.associator ..
  leftUnitor := PushoutProduct.leftUnitor
  rightUnitor := PushoutProduct.rightUnitor

variable [HasPushouts C] [HasInitial C] [CartesianMonoidalCategory C] [MonoidalClosed C]
  [BraidedCategory C]

lemma PushoutProduct.tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Arrow C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by
  ext
  · apply pushout.hom_ext <;> simp [whisker_exchange_assoc]
  · simp [whisker_exchange_assoc]

lemma PushoutProduct.associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Arrow C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) := by
  ext
  · apply pushout.hom_ext
    · simp [whisker_exchange_assoc]
    · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
      · suffices _ ◁ _ ◁ f₃.right ≫ (α_ _ _ _).inv ≫ f₁.right ▷ _ ▷ _ ≫ (α_ _ _ _).hom ≫
          _ ◁ f₂.left ▷ _ ≫ _ ◁ pushout.inr _ _ = _ ◁ f₂.left ▷ _ ≫ _ ◁ _ ◁ f₃.right ≫
          _ ◁ pushout.inr _ _ ≫ f₁.right ▷ pushout (Y₂.hom ▷ Y₃.left) (Y₂.left ◁ Y₃.hom) by
          simp [← whisker_exchange_assoc, reassoc_of% this]
        rw [← MonoidalCategory.whiskerLeft_comp_assoc, whisker_exchange, whisker_exchange_assoc,
          ← whisker_exchange, associator_inv_naturality_right_assoc, whisker_exchange_assoc,
          ← associator_inv_naturality_left_assoc, associator_naturality_right_assoc,
          Iso.inv_hom_id_assoc, MonoidalCategory.whiskerLeft_comp_assoc]
      · suffices ((α_ _ _ _).hom ≫ _ ◁ _ ◁ f₃.right ≫ (α_ _ _ _).inv ≫ f₁.left ▷ _ ▷ _ ≫
          (α_ _ _ _).hom ≫ _ ◁ f₂.right ▷ _ = f₁.left ▷ _ ▷ _ ≫ (α_ _ _ _).hom ≫
          _ ◁ f₂.right ▷ _ ≫ _ ◁ _ ◁ f₃.right) by
          simp [← whisker_exchange_assoc, reassoc_of% this]
        cat_disch
  · simp

lemma PushoutProduct.leftUnitor_naturality {X Y : Arrow C} (f : X ⟶ Y) :
    𝟙_ _ ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  ext
  · apply pushout.hom_ext
    · simp
    · apply (initialIsInitial.ofIso (mulZero initialIsInitial).symm).hom_ext
  · simp

lemma PushoutProduct.rightUnitor_naturality {X Y : Arrow C} (f : X ⟶ Y) :
    f ▷ 𝟙_ _ ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  ext
  · apply pushout.hom_ext
    · apply (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).hom_ext
    · simp
  · exact MonoidalCategory.rightUnitor_naturality f.right

lemma PushoutProduct.pentagon (W X Y Z : Arrow C) :
    (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
      (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
  ext
  · apply pushout.hom_ext
    · simp
    · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
      · simp
      · apply ((tensorRight _ ⋙ tensorRight _).map_isPushout
          (IsPushout.of_hasPushout _ _)).hom_ext <;> simp [associator_naturality_left_assoc]
  · exact MonoidalCategory.pentagon ..

lemma PushoutProduct.triangle (X Y : Arrow C) :
    (α_ X (𝟙_ _) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
  ext
  · apply pushout.hom_ext
    · simp
    · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
      · apply (initialIsInitial.ofIso ((initialIsoIsInitial ?_) ≪≫ (mulZero ?_).symm)).hom_ext
        <;> exact initialIsInitial.ofIso (zeroMul initialIsInitial).symm
      · simp [← comp_whiskerRight_assoc]
  · simp

instance : MonoidalCategory (Arrow C) where
  tensorHom_comp_tensorHom := PushoutProduct.tensorHom_comp_tensorHom
  associator_naturality := PushoutProduct.associator_naturality
  leftUnitor_naturality := PushoutProduct.leftUnitor_naturality
  rightUnitor_naturality := PushoutProduct.rightUnitor_naturality
  pentagon := PushoutProduct.pentagon
  triangle := PushoutProduct.triangle

instance [HasPullbacks C] : MonoidalClosed (Arrow C) where
  closed X := {
    rightAdj := pullbackHom.obj (Opposite.op X)
    adj := LeibnizAdjunction.adj _ _ (MonoidalClosed.internalHomAdjunction₂) X }

@[simps -isSimp]
instance braidedCategory : BraidedCategory (Arrow C) where
  braiding := PushoutProduct.braiding
  hexagon_forward _ _ _ := by
    ext
    · apply pushout.hom_ext
      · simp
      · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext <;> simp
    · exact BraidedCategory.hexagon_forward ..
  hexagon_reverse _ _ _ := by
    ext
    · apply pushout.hom_ext
      · apply ((tensorLeft _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext <;> simp
      · simp
    · exact BraidedCategory.hexagon_reverse ..

attribute [local simp] braidedCategory_braiding in
@[simps! -isSimp]
instance : SymmetricCategory (Arrow C) where

end

end MonoidalCategory.Arrow

end CategoryTheory
