/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Adhesive.Subobject
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.BicartesianSq
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

/-- The Leibniz functor associated to the tensor product on a monoidal category. -/
@[simp]
noncomputable
abbrev pushoutProduct [HasPushouts C] [MonoidalCategory C] := (curriedTensor C).leibnizPushout

/-- Notation for the pushout-product of morphisms. -/
notation3 f " □ " g:10 => (pushoutProduct.obj f).obj g

/-- The Leibniz functor associated to the internal hom on a monoidal closed category. -/
@[simp]
noncomputable
abbrev pullbackHom [HasPullbacks C] [MonoidalCategory C] [MonoidalClosed C] :
    (Arrow C)ᵒᵖ ⥤ Arrow C ⥤ Arrow C := MonoidalClosed.internalHom.leibnizPullback

/-- Notation for the pullback-hom of morphisms. -/
notation3 f " ⋔ " g:10 => (pullbackHom.obj f).obj g

section PushoutProduct

variable [HasPushouts C]

section Monoidal

open CartesianMonoidalCategory in
def isPullback_whisker_exchange [CartesianMonoidalCategory C] {A B X Y : C}
    (f : A ⟶ B) (g : X ⟶ Y) : IsPullback (f ▷ X) (A ◁ g) (B ◁ g) (f ▷ Y) where
  w := (whisker_exchange f g).symm
  isLimit' := ⟨by
    refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
    · intro s
      exact lift (s.π.app WalkingCospan.right ≫ fst _ _) (s.π.app WalkingCospan.left ≫ snd _ _)
    · intro s
      ext
      · simpa [PullbackCone.π_app_right] using (s.condition =≫ fst _ _).symm
      · simp
    · intro s
      ext
      · simp
      · simpa [PullbackCone.π_app_left] using s.condition =≫ snd _ _
    · intro _ _ h₁ h₂
      ext
      · simp [← h₂]
      · simp [← h₁]⟩

open CartesianMonoidalCategory in
local instance [CartesianMonoidalCategory C] (X : C) : PreservesMonomorphisms (tensorLeft X) where
  preserves f hf := {
    right_cancellation _ _ w := by
      apply CartesianMonoidalCategory.hom_ext
      · simpa using w =≫ fst _ _
      · simpa [cancel_mono_assoc_iff] using w =≫ snd _ _}

open CartesianMonoidalCategory in
local instance [CartesianMonoidalCategory C] (X : C) : PreservesMonomorphisms (tensorRight X) :=
  let := BraidedCategory.ofCartesianMonoidalCategory (C := C)
  preservesMonomorphisms.of_iso (BraidedCategory.tensorLeftIsoTensorRight _)

open Adhesive in
def isPullback_of_mono_desc_mono [MonoidalCategory C] [Adhesive C] {X₁ X₂ X₃ X₄ : C}
    {a : X₁ ⟶ X₂} {b : X₁ ⟶ X₃} {c : X₂ ⟶ X₄} {d : X₃ ⟶ X₄} (w : a ≫ c = b ≫ d)
    [Mono a] [h : Mono (pushout.desc c d w)] : IsPullback a b c d := by
  refine ?_
  exact {
  w := w
  isLimit' := ⟨by
    refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
    · intro s
      apply (isPullback_of_isPushout_of_mono_left (.of_hasPushout a b)).lift
        (s.π.app WalkingCospan.left) (s.π.app WalkingCospan.right)
      · apply h.right_cancellation
        simp [s.condition]
    · simp
    · simp
    · intro _ _ h₁ h₂
      apply (isPullback_of_isPushout_of_mono_left (.of_hasPushout a b)).hom_ext
      · simp [← h₁]
      · simp [← h₂]⟩}

open Adhesive in
def isPullback_of_mono_desc_mono' [MonoidalCategory C] [Adhesive C] {X₁ X₂ X₃ X₄ : C}
    {a : X₁ ⟶ X₂} {b : X₁ ⟶ X₃} {c : X₂ ⟶ X₄} {d : X₃ ⟶ X₄} (w : a ≫ c = b ≫ d)
    [Mono b] [Mono (pushout.desc c d w)] : IsPullback a b c d :=
  let : Mono (pushout.desc d c w.symm) := by
    convert show Mono ((pushoutSymmetry a b).inv ≫ (pushout.desc c d w)) by infer_instance
    ext <;> simp
  IsPullback.flip (isPullback_of_mono_desc_mono w.symm)

instance mono_desc_of_isPullback_mono_mono [MonoidalCategory C] [Adhesive C] {X₁ X₂ X₃ X₄ : C}
    {a : X₁ ⟶ X₂} {b : X₁ ⟶ X₃} {c : X₂ ⟶ X₄} {d : X₃ ⟶ X₄} (w : a ≫ c = b ≫ d)
    [Mono c] [Mono d] (h : IsPullback a b c d) : Mono (pushout.desc c d w) := by
  let : pushout (pullback.fst c d) (pullback.snd c d) ≅ pushout a b := HasColimit.isoOfNatIso <|
    spanExt h.isoPullback.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  convert show Mono (this.inv ≫ (pushout.desc c d pullback.condition)) from mono_comp ..
  ext <;> simp [this]

instance [MonoidalCategory C] [Adhesive C] {A B X Y : C} {f : A ⟶ B} {g : X ⟶ Y}
    (h : IsPullback (f ▷ X) (A ◁ g) (B ◁ g) (f ▷ Y)) [Mono (f ▷ Y)] [Mono (B ◁ g)] :
    Mono (PushoutObjObj.ofHasPushout (curriedTensor C) f g).ι := by
  let : pushout (pullback.fst (B ◁ g) (f ▷ Y)) (pullback.snd (B ◁ g) (f ▷ Y)) ≅
      pushout (f ▷ X) (A ◁ g) := HasColimit.isoOfNatIso <|
    spanExt h.isoPullback.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  convert show Mono (this.inv ≫ (pushout.desc (B ◁ g) (f ▷ Y) pullback.condition)) by infer_instance
  ext <;> simp [this]

open CartesianMonoidalCategory in
instance [CartesianMonoidalCategory C] [Adhesive C] {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)
    [Mono f] [Mono g] : Mono (PushoutObjObj.ofHasPushout (curriedTensor C) f g).ι := by
  let : Mono (B ◁ g) := (Arrow.instPreservesMonomorphismsTensorLeft B).preserves g
  let : Mono (f ▷ Y) := (Arrow.instPreservesMonomorphismsTensorRight Y).preserves f
  convert mono_desc_of_isPullback_mono_mono (whisker_exchange f g).symm
    (isPullback_whisker_exchange f g)
  ext <;> simp


/--/

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

@[simp]
instance [HasPushouts C] [HasInitial C] [CartesianMonoidalCategory C] [MonoidalClosed C]
    [BraidedCategory C] : MonoidalCategory (Arrow C) where
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by
    ext
    · apply pushout.hom_ext <;> simp [whisker_exchange_assoc]
    · simp [whisker_exchange_assoc]
  associator_naturality {_ _ _ _ Y₂ Y₃} f₁ f₂ f₃ := by
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
  pentagon _ _ _ _ := by
    ext
    · apply pushout.hom_ext
      · simp
      · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
        · simp
        · apply ((tensorRight _ ⋙ tensorRight _).map_isPushout
            (IsPushout.of_hasPushout _ _)).hom_ext <;> simp [associator_naturality_left_assoc]
    · exact MonoidalCategory.pentagon ..
  leftUnitor_naturality f := by
    ext
    · apply pushout.hom_ext
      · simp
      · apply (initialIsInitial.ofIso (mulZero initialIsInitial).symm).hom_ext
    · simp
  rightUnitor_naturality f := by
    ext
    · apply pushout.hom_ext
      · apply (initialIsInitial.ofIso (zeroMul initialIsInitial).symm).hom_ext
      · simp
    · exact rightUnitor_naturality f.right
  triangle X Y := by
    ext
    · apply pushout.hom_ext
      · simp
      · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
        · apply (initialIsInitial.ofIso ((initialIsoIsInitial ?_) ≪≫ (mulZero ?_).symm)).hom_ext
          <;> exact initialIsInitial.ofIso (zeroMul initialIsInitial).symm
        · simp [← comp_whiskerRight_assoc]
    · simp

instance [HasInitial C] [HasPushouts C] [HasPullbacks C]
  [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C] :
    MonoidalClosed (Arrow C) where
  closed X := {
    rightAdj := pullbackHom.obj (Opposite.op X)
    adj := LeibnizAdjunction.adj _ _ (MonoidalClosed.internalHomAdjunction₂) X }

@[simps]
instance [HasInitial C] [HasPushouts C] [CartesianMonoidalCategory C] [MonoidalClosed C]
    [BraidedCategory C] : BraidedCategory (Arrow C) where
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

@[simps!]
instance [HasInitial C] [HasPushouts C] [CartesianMonoidalCategory C] [MonoidalClosed C]
    [BraidedCategory C] : SymmetricCategory (Arrow C) where

end

end MonoidalCategory.Arrow

end CategoryTheory
