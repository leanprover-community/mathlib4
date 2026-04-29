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
# Leibniz constructions associated to monoidal categories.

In a monoidal category with pushouts, the pushout-product is the Leibniz functor associated to the
tensor product. This is the bifunctor of arrow categories that sends `f : A ⟶ B` and `g : X ⟶ Y`
to the canonical map from the pushout of `f ◁ X` and `A ▷ g` to `B ⊗ Y`, induced by the following
diagram:
```
  A ⊗ X --> B ⊗ X
     |          |
     v          v
  A ⊗ Y --> B ⊗ Y
```

In a monoidal closed category with pullbacks, the pullback-hom is the the Leibniz functor associated
to the internal hom. This is the bifunctor of arrow categories that sends `f : A ⟶ B` and
`g : X ⟶ Y` to the canonical map from `B ⟹ X` to the pullback of
`(ihom A).map g : A ⟹ X ⟶ A ⟹ Y` and `(pre f).app Y : B ⟹ Y ⟶ A ⟹ Y`, induced by the
following diagram:
```
  B ⟹ X --> A ⟹ X
     |          |
     v          v
  B ⟹ Y --> A ⟹ Y
```

In `Mathlib.CategoryTheory.Monoidal.Arrow`, these constructions are used to define a
monoidal (closed) structure on arrow categories.

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Limits MonoidalCategory Functor PushoutObjObj

variable {C : Type u} [Category.{v} C]

attribute [local simp] PushoutObjObj.ι ofHasPushout_pt ofHasPushout_inl ofHasPushout_inr
  PullbackObjObj.ofHasPullback_π

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
abbrev pushoutProduct [HasPushouts C] [MonoidalCategory C] :
    Arrow C ⥤ Arrow C ⥤ Arrow C := (curriedTensor C).leibnizPushout

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

namespace PushoutProduct

section

variable [HasPushouts C]

section Monoidal

variable [MonoidalCategory C] (X₁ X₂ X₃ : Arrow C) {W : C}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Left-whiskering the pushout-product of `X₁` and `X₂` with `W : C` is isomorphic to the
  pushout-product of `W ◁ X₁` and `X₂`. -/
@[simps!]
noncomputable
def whiskerLeftIso
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) (tensorLeft W)] :
    Arrow.mk (W ◁ (X₁ □ X₂).hom) ≅ (W ◁ X₁.hom) □ X₂ :=
  Arrow.isoMk
    (((tensorLeft W).map_isPushout
      (IsPushout.of_hasPushout (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom))).isoPushout ≪≫
      HasColimit.isoOfNatIso (spanExt (α_ W _ _).symm (α_ W _ _).symm (α_ W _ _).symm
      (associator_inv_naturality_middle W _ _).symm (associator_inv_naturality_right W _ _).symm))
    (α_ W _ _).symm
    (((tensorLeft W).map_isPushout
      (IsPushout.of_hasPushout (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom))).hom_ext (by
      simp) (by simp))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Right-whiskering the pushout-product of `X₁` and `X₂` with `W : C` is isomorphic to the
  pushout-product of `X₁` and `X₂ ▷ W`. -/
@[simps!]
noncomputable
def whiskerRightIso
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

-- helper instance for `PushoutProduct.associator`
local instance {F : C ⥤ C}
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) F] :
    PreservesColimit (span (((curriedTensor C).map X₁.hom).app X₂.left)
      (((curriedTensor C).obj X₁.left).map X₂.hom)) F := by
  simpa only [curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The pushout-product is associative: `(X₁ □ X₂) □ X₃ ≅ X₁ □ X₂ □ X₃`. -/
@[simps!]
noncomputable
def associator
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) (tensorRight X₃.left)]
    [PreservesColimit (span (X₁.hom ▷ X₂.left) (X₁.left ◁ X₂.hom)) (tensorRight X₃.right)]
    [PreservesColimit (span (X₂.hom ▷ X₃.left) (X₂.left ◁ X₃.hom)) (tensorLeft X₁.left)]
    [PreservesColimit (span (X₂.hom ▷ X₃.left) (X₂.left ◁ X₃.hom)) (tensorLeft X₁.right)] :
    ((X₁ □ X₂) □ X₃) ≅ X₁ □ X₂ □ X₃ := by
  refine Arrow.isoMk ?_ (α_ _ _ _) ?_
  · refine Iso.mk ?_ ?_ ?_ ?_
    · exact pushout.desc ((α_ _ _ _).hom ≫ _ ◁ pushout.inl _ _ ≫ pushout.inl _ _)
        ((whiskerRightIso _ _).hom.left ≫
          pushout.desc (_ ◁ pushout.inr _ _ ≫ pushout.inl _ _) (pushout.inr _ _)
          (by simp [Limits.pushout.associator_naturality_left_condition]))
        (((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
          (by simp [Limits.pushout.whiskerLeft_condition_assoc, ← whisker_exchange_assoc])
          (by simp [← whisker_exchange_assoc, Limits.pushout.associator_naturality_left_condition]))
    · exact pushout.desc ((whiskerLeftIso _ _).hom.left ≫
          pushout.desc (pushout.inl _ _) ((pushout.inl _ _ ▷ _) ≫ pushout.inr _ _)
          (by simp [Limits.pushout.associator_inv_naturality_right_condition]))
        ((α_ _ _ _).inv ≫ (pushout.inr _ _) ▷ _ ≫ pushout.inr _ _)
        (((tensorLeft _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
          (by simp [whisker_exchange_assoc,
            Limits.pushout.associator_inv_naturality_right_condition])
          (by simp [whisker_exchange_assoc, Limits.pushout.condition_whiskerRight_assoc]))
    · apply pushout.hom_ext (by simp)
      apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext <;> simp
    · refine pushout.hom_ext ?_ (by simp)
      apply ((tensorLeft _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext <;> simp
  · apply pushout.hom_ext (by simp [← MonoidalCategory.whiskerLeft_comp])
    · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
      · simp [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.comp_whiskerRight_assoc]
      · simp [← MonoidalCategory.comp_whiskerRight_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The pushout-product is commutative: `X₁ □ X₂ ≅ X₂ □ X₁`. -/
@[simps!]
noncomputable
def braiding [BraidedCategory C] (X₁ X₂ : Arrow C) : (X₁ □ X₂) ≅ X₂ □ X₁ :=
  Arrow.isoMk (pushoutSymmetry _ _ ≪≫
    HasColimit.isoOfNatIso (spanExt (β_ _ _) (β_ _ _) (β_ _ _)
    (BraidedCategory.braiding_naturality_right _ _).symm
    (BraidedCategory.braiding_naturality_left _ _).symm)) (β_ _ _) (by cat_disch)

end Monoidal

section CartesianMonoidalClosed

variable [CartesianMonoidalCategory C] [MonoidalClosed C]

noncomputable section

/-- The arrow isomorphism `X □ (∅ ⟶ W) ≅ X ▷ W` in a CCC with pushouts and an
initial object. -/
@[simps!]
def isInitialIso (X : Arrow C) {I : C} (i : IsInitial I) {W : C} :
    (X □ i.to W) ≅ X.hom ▷ W :=
  haveI : IsIso (X.hom ▷ I) :=
    isIso_of_isInitial (i.ofIso (zeroMul i).symm) (i.ofIso (zeroMul i).symm) _
  haveI : IsPushout (X.hom ▷ I) (_ ◁ i.to W) ((i.ofIso (zeroMul i).symm).to _) (𝟙 _) :=
    .of_horiz_isIso (sq := ⟨(i.ofIso (zeroMul i).symm).hom_ext ..⟩)
  Arrow.isoMk' _ _ this.isoPushout.symm (Iso.refl _)
    (pushout.hom_ext ((i.ofIso (zeroMul i).symm).hom_ext _ _) (by simp))

/-- The arrow isomorphism `(∅ ⟶ W) □ X ≅ W ◁ X` in a braided CCC with pushouts and
an initial object. -/
@[simps!]
def isInitialIso' [BraidedCategory C] (X : Arrow C) {I : C} (i : IsInitial I) {W : C} :
    (i.to W □ X) ≅ Arrow.mk (W ◁ X.hom) :=
  haveI : IsIso (I ◁ X.hom) :=
    isIso_of_isInitial (i.ofIso (mulZero i).symm) (i.ofIso (mulZero i).symm) _
  haveI : IsPushout (i.to W ▷ _) (I ◁ X.hom) (𝟙 _) ((i.ofIso (mulZero i).symm).to _) :=
    .of_vert_isIso (sq := ⟨(i.ofIso (mulZero i).symm).hom_ext ..⟩)
  Arrow.isoMk' _ _ this.isoPushout.symm (Iso.refl _)
    (pushout.hom_ext (by simp) ((i.ofIso (mulZero i).symm).hom_ext _ _))

/-- The arrow isomorphism `X □ (∅ ⟶ ⋆) ≅ X` in a CCC with pushouts, an initial object, and a
terminal object. -/
@[simps!]
def isInitialIsTerminalIso (X : Arrow C) {I : C} (i : IsInitial I) {T : C} (t : IsTerminal T) :
    (X □ i.to T) ≅ X :=
  (isInitialIso X i) ≪≫ Arrow.isoMk' _ _
    (MonoidalCategory.whiskerLeftIso X.left
      (t.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit) ≪≫ ρ_ X.left)
    (MonoidalCategory.whiskerLeftIso X.right
      (t.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit) ≪≫ ρ_ X.right)
    (by simp [← whisker_exchange_assoc])

/-- The arrow isomorphism `X □ (∅ ⟶ ⋆) ≅ X` in a CCC with pushouts, an initial object, and a
terminal object. -/
@[simps!]
def isInitialIsTerminalIso' (X : Arrow C) {I : C} (i : IsInitial I) {T : C} (t : IsTerminal T) :
    (X □ t.from I) ≅ X :=
  (mapIso _ (Arrow.isoMk' _ _ (Iso.refl _) (Iso.refl _) (i.hom_ext _ _))) ≪≫
    (isInitialIsTerminalIso X i t)

end

variable [HasInitial C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `C` is a CCC with pushouts and an initial object, then `X □ (⊥_ C ⟶ 𝟙_ C) ≅ X`. -/
@[simp]
noncomputable
def rightUnitor (X : Arrow C) :
    (X □ initial.to (𝟙_ C)) ≅ X := by
  refine Arrow.isoMk ?_ (ρ_ X.right) ?_
  · refine Iso.mk ?_ ((ρ_ X.left).inv ≫ pushout.inr _ _) ?_ ?_
    · refine pushout.desc ?_ (ρ_ X.left).hom ?_
      · exact (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).to _
      · apply (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).hom_ext
    · refine pushout.hom_ext ?_ (by simp)
      apply (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).hom_ext
    · simp
  · refine pushout.hom_ext ?_ (by simp)
    apply (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).hom_ext

/-- If `C` is a braided CCC with pushouts and an initial object, then `(⊥_ C ⟶ 𝟙_ C) □ X ≅ X`. -/
@[simp]
noncomputable
def leftUnitor [BraidedCategory C]
    (X : Arrow C) : (initial.to (𝟙_ C) □ X) ≅ X :=
  braiding _ _ ≪≫ rightUnitor _

end CartesianMonoidalClosed

end

end PushoutProduct

namespace PullbackHom

variable [HasPullbacks C]

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- The arrow isomorphism `(f : A ⟶ B) ⋔ (W ⟶ ⋆) ≅ (B ⟹ W ⟶ A ⟹ W)` in a monoidal closed
category with pullbacks and a terminal object. -/
@[simps!]
def isTerminalIso [MonoidalCategory C] [MonoidalClosed C]
    (X : Arrow C) {T : C} (t : IsTerminal T) {W : C} :
    ((Opposite.op X) ⋔ Arrow.mk (t.from W)) ≅ Arrow.mk ((MonoidalClosed.pre X.hom).app W) :=
  haveI : IsIso ((MonoidalClosed.pre X.hom).app T) :=
    isIso_of_isTerminal (IsTerminal.isTerminalObj (ihom _) _ t)
      (IsTerminal.isTerminalObj (ihom _) _ t) _
  haveI : IsPullback (𝟙 _) ((IsTerminal.isTerminalObj (ihom _) _ t).from _)
      ((ihom X.left).map (t.from W)) ((MonoidalClosed.pre X.hom).app T) :=
    .of_horiz_isIso (sq := ⟨(IsTerminal.isTerminalObj (ihom _) _ t).hom_ext ..⟩)
  Arrow.isoMk' _ _ (Iso.refl _) this.isoPullback.symm ((this.isoPullback).eq_comp_inv.2
    (pullback.hom_ext (by simp) ((IsTerminal.isTerminalObj (ihom _) _ t).hom_ext ..)))

open CartesianMonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
/-- The arrow isomorphism `(∅ ⟶ W) ⋔ (f : A ⟶ B) ≅ (W ⟹ A ⟶ W ⟹ B)` in a braided CCC with
pullbacks and an initial object. -/
@[simps!]
def isInitialIso [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    (X : Arrow C) {I : C} (i : IsInitial I) {W : C} :
    (Opposite.op (Arrow.mk (i.to W)) ⋔ X) ≅ Arrow.mk ((ihom W).map X.hom) :=
  haveI : IsIso ((ihom I).map X.hom) :=
    isIso_of_isTerminal (isTerminalTensorUnit.ofIso (powZero i).symm)
      (isTerminalTensorUnit.ofIso (powZero i).symm) _
  haveI : IsPullback ((isTerminalTensorUnit.ofIso (powZero i).symm).from _) (𝟙 _)
      ((ihom I).map X.hom) ((MonoidalClosed.pre (i.to W)).app X.right) :=
    .of_vert_isIso (sq := ⟨(isTerminalTensorUnit.ofIso (powZero i).symm).hom_ext ..⟩)
  Arrow.isoMk' _ _ (Iso.refl _) this.isoPullback.symm ((this.isoPullback).eq_comp_inv.2
    (pullback.hom_ext ((isTerminalTensorUnit.ofIso (powZero i).symm).hom_ext ..) (by simp)))

end

end PullbackHom

end CategoryTheory.MonoidalCategory.Arrow
