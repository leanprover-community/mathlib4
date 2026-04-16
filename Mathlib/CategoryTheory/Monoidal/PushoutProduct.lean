/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
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

noncomputable section Iso

open CartesianMonoidalCategory

variable [CartesianMonoidalCategory C] [MonoidalClosed C]

set_option backward.isDefEq.respectTransparency false in
def _root_.CategoryTheory.Limits.pushout.isInitialWhiskerLeftIso
    {A B : C} (f : A ⟶ B) {I : C} (i : IsInitial I) {W : C} :
    pushout (f ▷ I) (A ◁ i.to W) ≅ A ⊗ W where
  hom := pushout.desc ((i.ofIso (zeroMul i).symm).to _) (𝟙 _)
    ((i.ofIso (zeroMul i).symm).hom_ext _ _)
  inv := pushout.inr _ _
  hom_inv_id := pushout.hom_ext ((i.ofIso (zeroMul i).symm).hom_ext _ _) (by simp)

set_option backward.isDefEq.respectTransparency false in
def _root_.CategoryTheory.Limits.pushout.isInitialWhiskerRightIso [BraidedCategory C]
    {A B : C} (f : A ⟶ B) {I : C} (i : IsInitial I) {W : C} :
    pushout (i.to W ▷ A) (I ◁ f) ≅ W ⊗ A where
  hom := pushout.desc (𝟙 _) ((i.ofIso (mulZero i).symm).to _)
    ((i.ofIso (mulZero i).symm).hom_ext _ _)
  inv := pushout.inl _ _
  hom_inv_id := pushout.hom_ext (by simp) ((i.ofIso (mulZero i).symm).hom_ext _ _)

set_option backward.isDefEq.respectTransparency false in
def isInitialIsoWhiskerRight (X : Arrow C) {I : C} (i : IsInitial I) {W : C} :
    (X □ i.to W) ≅ Arrow.mk (X.hom ▷ W) :=
  Arrow.isoMk' _ _ (pushout.isInitialWhiskerLeftIso X.hom i) (Iso.refl _) (pushout.hom_ext
    ((i.ofIso (zeroMul i).symm).hom_ext _ _) (by simp [pushout.isInitialWhiskerLeftIso]))

-- not strictly necessary
set_option backward.isDefEq.respectTransparency false in
def isInitialIsoWhiskerLeft [BraidedCategory C] (X : Arrow C) {I : C} (i : IsInitial I) {W : C} :
    (i.to W □ X) ≅ Arrow.mk (W ◁ X.hom) :=
  Arrow.isoMk' _ _ (pushout.isInitialWhiskerRightIso X.hom i) (Iso.refl _) (pushout.hom_ext
    (by simp [pushout.isInitialWhiskerRightIso]) ((i.ofIso (mulZero i).symm).hom_ext _ _))

def isInitialIsTerminalIso (X : Arrow C) {I : C} (i : IsInitial I) {T : C} (t : IsTerminal T) :
    (X □ i.to T) ≅ X :=
  (isInitialIsoWhiskerRight X i) ≪≫ Arrow.isoMk' _ _
    (whiskerLeftIso X.left (t.uniqueUpToIso isTerminalTensorUnit) ≪≫ ρ_ X.left)
    (whiskerLeftIso X.right (t.uniqueUpToIso isTerminalTensorUnit) ≪≫ ρ_ X.right)
    (by simp [← whisker_exchange_assoc])

def isInitialIsTerminalIso' (X : Arrow C) {I : C} (i : IsInitial I) {T : C} (t : IsTerminal T) :
    (X □ t.from I) ≅ X :=
  ((pushoutProduct.obj X).mapIso (Arrow.isoMk' _ _ (Iso.refl _) (Iso.refl _) (i.hom_ext _ _))) ≪≫
    (isInitialIsTerminalIso X i t)

end Iso

section Monoidal

variable [MonoidalCategory C] (X₁ X₂ X₃ : Arrow C) {W : C}

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

variable [HasInitial C] [CartesianMonoidalCategory C] [MonoidalClosed C]

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

noncomputable section Iso

open CartesianClosed

def _root_.CategoryTheory.terminalPow [MonoidalCategory C]
    {A : C} [Closed A] {T : C} (t : IsTerminal T) :
    (ihom A).obj T ≅ T where
  hom := t.from _
  inv := MonoidalClosed.curry (t.from _)
  hom_inv_id := by
    rw [← MonoidalClosed.curry_natural_left, MonoidalClosed.curry_eq_iff]
    apply t.hom_ext

set_option backward.isDefEq.respectTransparency false in
def _root_.CategoryTheory.Limits.pullback.ihomMapIsTerminalIso
    [MonoidalCategory C] [MonoidalClosed C]
    {A B : C} (f : A ⟶ B) {T : C} (t : IsTerminal T) {W : C} :
    pullback ((ihom A).map (t.from W)) ((MonoidalClosed.pre f).app T) ≅ A ⟹ W where
  hom := pullback.fst _ _
  inv := pullback.lift (𝟙 _) (MonoidalClosed.curry (t.from _)) (by
      rw [MonoidalClosed.curry_pre_app, MonoidalClosed.eq_curry_iff]
      exact t.hom_ext _ _)
  hom_inv_id := pullback.hom_ext (by simp) ((t.ofIso (terminalPow t).symm).hom_ext _ _)

set_option backward.isDefEq.respectTransparency false in
def _root_.CategoryTheory.Limits.pullback.preIsInitialIso
    [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B : C} (f : A ⟶ B) {I : C} (i : IsInitial I) {W : C} :
    pullback ((ihom I).map f) ((MonoidalClosed.pre (i.to W)).app B) ≅ W ⟹ B where
  hom := pullback.snd _ _
  inv := pullback.lift (MonoidalClosed.curry ((i.ofIso (mulZero i).symm).to _)) (𝟙 _) (by
      rw [← MonoidalClosed.curry_natural_right, MonoidalClosed.curry_eq_iff]
      exact (i.ofIso (mulZero i).symm).hom_ext _ _)
  hom_inv_id := pullback.hom_ext (by
    simp only [Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
      ← MonoidalClosed.curry_natural_left, MonoidalClosed.curry_eq_iff]
    exact (i.ofIso (mulZero i).symm).hom_ext _ _) (by simp)

set_option backward.isDefEq.respectTransparency false in
def isTerminalIso [MonoidalCategory C] [MonoidalClosed C]
    (X : Arrow C) {T : C} (t : IsTerminal T) {W : C} :
    ((.op X) ⋔ Arrow.mk (t.from W)) ≅
      Arrow.mk ((MonoidalClosed.pre X.hom).app W) :=
  Arrow.isoMk' _ _ (Iso.refl _) (pullback.ihomMapIsTerminalIso X.hom t)
    (by simp [PullbackObjObj.ofHasPullback_π, pullback.ihomMapIsTerminalIso])

set_option backward.isDefEq.respectTransparency false in
def isInitialIso [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    (X : Arrow C) {I : C} (i : IsInitial I) {W : C} :
    ((.op (Arrow.mk (i.to W))) ⋔ X) ≅
      Arrow.mk ((ihom W).map X.hom) :=
  Arrow.isoMk' _ _ (Iso.refl _) (pullback.preIsInitialIso X.hom i)
    (by simp [PullbackObjObj.ofHasPullback_π, pullback.preIsInitialIso])

end Iso

end PullbackHom

/-
/-- `X □ Y` lifts against `Z` if and only if `Y` lifts against `X ⋔ Z`. -/
lemma pushoutProduct_hasLiftingProperty_iff [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C] {X Y Z : Arrow C} :
    HasLiftingProperty (X □ Y).hom Z.hom ↔ HasLiftingProperty Y.hom ((.op X) ⋔ Z).hom :=
  ParametrizedAdjunction.hasLiftingProperty_iff MonoidalClosed.internalHomAdjunction₂
    (PushoutObjObj.ofHasPushout ..) (PullbackObjObj.ofHasPullback ..)
-/

/-- `f □ g` lifts against `h` if and only if `g` lifts against `f ⋔ h`. -/
lemma pushoutProduct_hasLiftingProperty_iff [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C]
    {A B K L X Y : C} {f : A ⟶ B} {g : K ⟶ L} {h : X ⟶ Y} :
    HasLiftingProperty (f □ g).hom h ↔ HasLiftingProperty g ((.op f) ⋔ h).hom :=
  ParametrizedAdjunction.hasLiftingProperty_iff MonoidalClosed.internalHomAdjunction₂
    (PushoutObjObj.ofHasPushout ..) (PullbackObjObj.ofHasPullback ..)

/-- `f □ g` lifts against `h` if and only if `f` lifts against `g ⋔ h`. -/
lemma pushoutProduct_hasLiftingProperty_iff' [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B K L X Y : C} {f : A ⟶ B} {g : K ⟶ L} {h : X ⟶ Y} :
    HasLiftingProperty (f □ g).hom h ↔ HasLiftingProperty f ((.op g) ⋔ h).hom := by
  rw [← pushoutProduct_hasLiftingProperty_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_left (PushoutProduct.braiding _ _) h

/-- `f □ g` lifts against `X ⟶ ⋆` if and only if `g` lifts against `(pre f).app X`. -/
lemma hasLiftingProperty_pushoutProduct_isTerminal_iff [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C]
    {A B K L X Y : C} {f : A ⟶ B} {g : K ⟶ L}
    (t : IsTerminal Y) :
    HasLiftingProperty (f □ g).hom (t.from X) ↔
      HasLiftingProperty g ((MonoidalClosed.pre f).app X) := by
  rw [pushoutProduct_hasLiftingProperty_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_right g (PullbackHom.isTerminalIso _ t)

open CartesianClosed in
/-- `(∅ ⟶ B) □ g` lifts against `X ⟶ ⋆` if and only if `g` lifts against `(B ⟹ X) ⟶ ⋆`. -/
lemma hasLiftingProperty_pushoutProduct_isInitial_isTerminal_iff [HasPushouts C] [HasPullbacks C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B K L X Y : C} {g : K ⟶ L}
    (i : IsInitial A) (t : IsTerminal Y) :
    HasLiftingProperty (i.to B □ g).hom (t.from X) ↔
      HasLiftingProperty g (t.from (B ⟹ X)) := by
  change HasLiftingProperty (ofHasPushout ..).ι _ ↔ _
  rw [HasLiftingProperty.iff_of_arrow_iso_left (PushoutProduct.isInitialIsoWhiskerLeft _ _)]
  have := Adjunction.hasLiftingProperty_iff (ihom.adjunction B) g (t.from X)
  dsimp at this ⊢
  rw [this]
  exact HasLiftingProperty.iff_of_arrow_iso_right g
    (Arrow.isoMk' _ _ (Iso.refl _) (terminalPow t) (t.hom_ext _ _))

open CartesianClosed in
/-- `f □ (∅ ⟶ L)` lifts against `X ⟶ ⋆` if and only if `f` lifts against `(L ⟹ X) ⟶ ⋆`. -/
lemma hasLiftingProperty_pushoutProduct_isInitial_isTerminal_iff' [HasPushouts C] [HasPullbacks C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B K L X Y : C} {f : A ⟶ B}
    (i : IsInitial K) (t : IsTerminal Y) :
    HasLiftingProperty (f □ i.to L).hom (t.from X) ↔
      HasLiftingProperty f (t.from (L ⟹ X)) := by
  rw [← hasLiftingProperty_pushoutProduct_isInitial_isTerminal_iff i t]
  exact HasLiftingProperty.iff_of_arrow_iso_left (PushoutProduct.braiding _ _) (t.from X)

end CategoryTheory.MonoidalCategory.Arrow
