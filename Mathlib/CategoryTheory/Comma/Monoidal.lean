/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# Monoidal structure on the arrow category

-/

universe v u

namespace CategoryTheory.Arrow

open Opposite Limits MonoidalCategory Functor PushoutProduct

variable {C : Type u} [Category.{v} C] [HasPushouts C] [CartesianMonoidalCategory C]
  (F : C ⥤ C ⥤ C) (G : Cᵒᵖ ⥤ C ⥤ C)
  {A B X Y Z W : C} (f : A ⟶ B) (g : X ⟶ Y) (h : Z ⟶ W)

notation3 f "□" g:10 => Functor.pushoutProduct (curriedTensor _) f g

@[simp]
def IsPushout_ofWhiskerLeft {Z X Y W : C} {f : Z ⟶ X} {g : Z ⟶ Y}
    [PreservesColimit (span f g) (tensorLeft W)] :
    IsPushout (W ◁ f) (W ◁ g)
      (W ◁ (pushout.inl f g)) (W ◁ (pushout.inr f g)) where
  w := by simp only [← MonoidalCategory.whiskerLeft_comp, pushout.condition]
  isColimit' := ⟨Limits.isColimitOfHasPushoutOfPreservesColimit (tensorLeft W) _ _⟩

@[simp]
def IsPushout_ofWhiskerRight {Z X Y W : C} {f : Z ⟶ X} {g : Z ⟶ Y}
    [PreservesColimit (span f g) (tensorRight W)] :
    IsPushout (f ▷ W) (g ▷ W)
      ((pushout.inl f g) ▷ W) ((pushout.inr f g) ▷ W) where
  w := by simp only [← MonoidalCategory.comp_whiskerRight, pushout.condition]
  isColimit' := ⟨Limits.isColimitOfHasPushoutOfPreservesColimit (tensorRight W) _ _⟩

omit [HasPushouts C] in
@[reassoc (attr := simp)]
lemma whisker_inl_desc {Z X Y P Q : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
    (w : f ≫ h = g ≫ k) :
    inl ▷ Q ≫ hP.desc h k w ▷ Q = h ▷ Q := by cat_disch

omit [HasPushouts C] in
@[reassoc (attr := simp)]
lemma whisker_inr_desc {Z X Y P Q : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
    (w : f ≫ h = g ≫ k) :
    inr ▷ Q ≫ hP.desc h k w ▷ Q = k ▷ Q := by cat_disch

@[reassoc]
lemma whisker_pushout_condition {X Y Z Q : C} {f : X ⟶ Y} {g : X ⟶ Z} :
    Q ◁ f ≫ Q ◁ (pushout.inl f g) = Q ◁ g ≫ Q ◁ pushout.inr _ _ := by
  simp [← MonoidalCategory.whiskerLeft_comp, pushout.condition]

namespace PushoutProduct

-- need (F.obj A).obj ((F.obj B).obj C) ≅ (F.obj ((F.obj A).obj B)).obj C for general F
@[simps!]
noncomputable
def tensorLeft_PushoutObjObj_iso
    [PreservesColimitsOfSize (tensorLeft W)] :
      W ⊗ (Arrow.mk (f □ g)).left ≅
      (Arrow.mk ((W ◁ f) □ g)).left := by
  refine (IsPushout_ofWhiskerLeft).isoPushout ≪≫ HasColimit.isoOfNatIso (spanExt ?_ ?_ ?_ ?_ ?_)
  · exact (α_ W A X).symm
  · exact (α_ W B X).symm
  · exact (α_ W A Y).symm
  · exact (associator_inv_naturality_middle W f X).symm
  · exact (associator_inv_naturality_right W A g).symm

@[simps!]
noncomputable
def PushoutObjObj_whiskerRight_iso [PreservesColimitsOfSize (tensorRight W)] :
    (Arrow.mk (f □ g)).left ⊗ W ≅
    (Arrow.mk (f □ (g ▷ W))).left := by
  refine IsPushout_ofWhiskerRight.isoPushout ≪≫
    HasColimit.isoOfNatIso (spanExt ?_ ?_ ?_ ?_ ?_)
  · exact α_ A X W
  · exact α_ B X W
  · exact α_ A Y W
  · exact (associator_naturality_left f X W).symm
  · exact (associator_naturality_middle A g W).symm

@[simps!]
noncomputable
def PushoutProduct.whiskerRight_iso [PreservesColimitsOfSize (tensorRight W)] :
    Arrow.mk ((f □ g) ▷ W) ≅ Arrow.mk (f □ (g ▷ W)) := by
  refine Arrow.isoMk (PushoutObjObj_whiskerRight_iso f g) (α_ B Y W) ?_
  · apply IsPushout_ofWhiskerRight.hom_ext
    all_goals simp

@[simps!]
noncomputable
def PushoutProduct.whiskerLeft_iso [PreservesColimitsOfSize (tensorLeft W)] :
    Arrow.mk (W ◁ (f □ g)) ≅ Arrow.mk ((W ◁ f) □ g) := by
  refine Arrow.isoMk (tensorLeft_PushoutObjObj_iso _ _) (α_ W B Y).symm ?_
  · apply IsPushout_ofWhiskerLeft.hom_ext
    all_goals simp [← MonoidalCategory.whiskerLeft_comp_assoc]

@[simp]
noncomputable
def associator_hom_left_aux [PreservesColimitsOfSize (tensorRight W)] :
    ((Arrow.mk (f □ g)).left) ⊗ W ⟶
    (Arrow.mk (f □ (g □ h))).left := by
  refine (PushoutObjObj_whiskerRight_iso _ _).hom ≫ pushout.desc ?_ ?_ ?_
  · exact (B ◁ pushout.inr _ _) ≫ pushout.inl _ _
  · exact pushout.inr _ _
  · dsimp
    rw [← whisker_exchange_assoc, pushout.condition,
      ← MonoidalCategory.whiskerLeft_comp_assoc, IsPushout.inr_desc]

@[simp]
noncomputable
def associator_hom_left
    [PreservesColimitsOfSize (tensorRight Z)]
    [PreservesColimitsOfSize (tensorRight W)] :
    (Arrow.mk ((f □ g) □ h)).left ⟶ (Arrow.mk (f □ (g □ h))).left := by
  refine pushout.desc ?_ ?_ ?_
  · exact (α_ B Y Z).hom ≫ (B ◁ pushout.inl _ _) ≫ pushout.inl _ _
  · exact associator_hom_left_aux ..
  · apply IsPushout_ofWhiskerRight.hom_ext
    · simp [whisker_pushout_condition_assoc, ← whisker_exchange_assoc]
    · simp only [curriedTensor_obj_obj, PushoutObjObj.ofHasPushout_pt, curriedTensor_map_app,
        curriedTensor_obj_map, PushoutObjObj.ofHasPushout_ι, mk_left, pushoutProduct,
        whisker_inr_desc_assoc, associator_hom_left_aux, PushoutObjObj_whiskerRight_iso_hom,
        Category.assoc, HasColimit.isoOfNatIso_hom_desc, ← whisker_exchange_assoc,
        tensor_whiskerLeft, IsPushout.inr_isoPushout_hom_assoc, colimit.ι_desc,
        Cocones.precompose_obj_pt, PushoutCocone.mk_pt, Cocones.precompose_obj_ι, NatTrans.comp_app,
        span_right, const_obj_obj, spanExt_hom_app_right, PushoutCocone.mk_ι_app,
        Iso.inv_hom_id_assoc]
      rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, pushout.condition,
        ← MonoidalCategory.whiskerLeft_comp_assoc, IsPushout.inl_desc]

@[simp]
noncomputable
def associator_inv_left
    [PreservesColimitsOfSize (tensorLeft A)]
    [PreservesColimitsOfSize (tensorLeft B)] :
     (Arrow.mk (f □ (g □ h))).left ⟶ (Arrow.mk ((f □ g) □ h)).left := by
  apply pushout.desc ?_ ?_ ?_
  · refine (tensorLeft_PushoutObjObj_iso g h).hom ≫ pushout.desc ?_ ?_ ?_
    · exact 𝟙 _ ≫ pushout.inl _ _
    · exact (pushout.inl _ _ ▷ W) ≫ pushout.inr _ _
    · dsimp [Functor.PushoutObjObj.ι]
      rw [Category.id_comp, whisker_exchange_assoc, ← pushout.condition,
        ← MonoidalCategory.comp_whiskerRight_assoc, IsPushout.inl_desc]
  · exact (α_ _ _ _).inv ≫ (pushout.inr _ _) ▷ _ ≫ pushout.inr _ _
  · dsimp
    apply IsPushout_ofWhiskerLeft.hom_ext
    · simp only [Category.id_comp, Category.assoc, HasColimit.isoOfNatIso_hom_desc,
        whisker_exchange_assoc, whiskerRight_tensor, IsPushout.inl_isoPushout_hom_assoc,
        colimit.ι_desc, Cocones.precompose_obj_pt, PushoutCocone.mk_pt, Cocones.precompose_obj_ι,
        NatTrans.comp_app, span_left, const_obj_obj, spanExt_hom_app_left, Iso.symm_hom,
        PushoutCocone.mk_ι_app, Iso.hom_inv_id_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
        IsPushout.inl_desc]
      rw [← associator_inv_naturality_left_assoc, associator_inv_naturality_right_assoc,
        whisker_exchange_assoc, ← pushout.condition, whiskerRight_tensor, whisker_inr_desc_assoc]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    · simp only [Category.id_comp, Category.assoc, HasColimit.isoOfNatIso_hom_desc,
        whisker_exchange_assoc, whiskerRight_tensor, IsPushout.inr_isoPushout_hom_assoc,
        colimit.ι_desc, Cocones.precompose_obj_pt, PushoutCocone.mk_pt, Cocones.precompose_obj_ι,
        NatTrans.comp_app, span_right, const_obj_obj, spanExt_hom_app_right, Iso.symm_hom,
        PushoutCocone.mk_ι_app, Iso.hom_inv_id_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
        IsPushout.inr_desc]
      rw [← associator_inv_naturality_left_assoc, associator_inv_naturality_middle_assoc,
        ← comp_whiskerRight_assoc, ← pushout.condition, whiskerRight_tensor, comp_whiskerRight]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]

@[simp]
noncomputable
def associator_iso_left
      [PreservesColimitsOfSize (tensorLeft A)]
      [PreservesColimitsOfSize (tensorLeft B)]
      [PreservesColimitsOfSize (tensorRight Z)]
      [PreservesColimitsOfSize (tensorRight W)] :
    (Arrow.mk ((f □ g) □ h)).left ≅ (Arrow.mk (f □ (g □ h))).left where
  hom := associator_hom_left f g h
  inv := associator_inv_left f g h
  hom_inv_id := by
    apply pushout.hom_ext
    · simp
    · exact IsPushout_ofWhiskerRight.hom_ext (by simp) (by simp)
  inv_hom_id := by
    apply pushout.hom_ext
    · exact IsPushout_ofWhiskerLeft.hom_ext (by simp) (by simp)
    · simp

@[simp]
noncomputable
def braiding_left_iso [BraidedCategory C] : (Arrow.mk (f □ g)).left ≅
    (Arrow.mk (g □ f)).left :=
  pushoutSymmetry (f ▷ X) (A ◁ g) ≪≫
    (HasColimit.isoOfNatIso (spanExt (β_ _ _) (β_ _ _) (β_ _ _)
    (BraidedCategory.braiding_naturality_right A g).symm
    (BraidedCategory.braiding_naturality_left f X).symm))

noncomputable
def braiding [BraidedCategory C] : Arrow.mk (f □ g) ≅ Arrow.mk (g □ f) :=
  Arrow.isoMk (braiding_left_iso f g) (β_ _ _) (by cat_disch)

@[simp]
noncomputable
def associator
    [PreservesColimitsOfSize (tensorLeft A)]
    [PreservesColimitsOfSize (tensorLeft B)]
    [PreservesColimitsOfSize (tensorRight Z)]
    [PreservesColimitsOfSize (tensorRight W)] :
    Arrow.mk ((f □ g) □ h) ≅ Arrow.mk (f □ g □ h) := by
  refine Arrow.isoMk (associator_iso_left _ _ _) (α_ _ _ _) ?_
  · apply pushout.hom_ext
    · simp [← MonoidalCategory.whiskerLeft_comp]
    · apply IsPushout_ofWhiskerRight.hom_ext
      · simp [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.comp_whiskerRight_assoc]
      · simp [← MonoidalCategory.comp_whiskerRight_assoc]

@[simp]
lemma associator_hom_eq
    [PreservesColimitsOfSize (tensorLeft A)]
    [PreservesColimitsOfSize (tensorLeft B)]
    [PreservesColimitsOfSize (tensorRight Z)]
    [PreservesColimitsOfSize (tensorRight W)] :
    (PushoutProduct.associator f g h).hom = sorry := by
  apply Arrow.hom_ext
  ·
    dsimp
    sorry
  · sorry

@[simps!]
noncomputable
def leftUnitor [HasInitial C] [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    (X : Arrow C) :
    ((leftBifunctor (curriedTensor C)).obj (mk (initial.to (𝟙_ C)))).obj X ≅ X := by
  refine Arrow.isoMk ?_ (λ_ X.right) ?_
  · dsimp
    refine Iso.mk ?_ ?_ ?_ ?_
    · refine pushout.desc (λ_ X.left).hom ?_ ?_
      · exact IsInitial.to (IsInitial.ofIso initialIsInitial (mulZero initialIsInitial).symm) _
      · apply (IsInitial.ofIso initialIsInitial (mulZero initialIsInitial).symm).hom_ext
    · exact (λ_ X.left).inv ≫ pushout.inl _ _
    · apply pushout.hom_ext
      · simp
      · apply (IsInitial.ofIso initialIsInitial (mulZero initialIsInitial).symm).hom_ext
    · simp
  · apply pushout.hom_ext
    · simp
    · apply (IsInitial.ofIso initialIsInitial (mulZero initialIsInitial).symm).hom_ext

@[simps!]
noncomputable
def rightUnitor [HasInitial C] [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    (X : Arrow C) :
    ((leftBifunctor (curriedTensor C)).obj X).obj (mk (initial.to (𝟙_ C))) ≅ X := by
  refine Arrow.isoMk ?_ (ρ_ X.right) ?_
  · dsimp
    refine Iso.mk ?_ ?_ ?_ ?_
    · refine pushout.desc ?_ (ρ_ X.left).hom ?_
      · exact IsInitial.to (IsInitial.ofIso initialIsInitial (zeroMul initialIsInitial).symm) _
      · apply (IsInitial.ofIso initialIsInitial (zeroMul initialIsInitial).symm).hom_ext
    · exact (ρ_ X.left).inv ≫ pushout.inr _ _
    · apply pushout.hom_ext
      · apply (IsInitial.ofIso initialIsInitial (zeroMul initialIsInitial).symm).hom_ext
      · simp
    · simp
  · apply pushout.hom_ext
    · apply (IsInitial.ofIso initialIsInitial (zeroMul initialIsInitial).symm).hom_ext
    · simp

@[simp]
lemma associator_naturality
    [∀ S : C, PreservesColimitsOfSize (tensorLeft S)]
    [∀ S : C, PreservesColimitsOfSize (tensorRight S)]
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Arrow C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    (((leftBifunctor _).map (((leftBifunctor _).map f₁).app X₂ ≫
    ((leftBifunctor _).obj Y₁).map f₂)).app X₃ ≫
    ((leftBifunctor _).obj (((leftBifunctor _).obj Y₁).obj Y₂)).map f₃) ≫
    (associator Y₁.hom Y₂.hom Y₃.hom).hom =
    (associator X₁.hom X₂.hom X₃.hom).hom ≫
    ((leftBifunctor _).map f₁).app (((leftBifunctor _).obj X₂).obj X₃) ≫
    ((leftBifunctor _).obj Y₁).map (((leftBifunctor _).map f₂).app X₃ ≫
    ((leftBifunctor _).obj Y₂).map f₃) := by
  apply Arrow.hom_ext
  · apply pushout.hom_ext
    · simp only [leftBifunctor_obj_obj_right, curriedTensor_obj_obj, id_obj,
        PushoutObjObj.ofHasPushout_pt, curriedTensor_map_app, curriedTensor_obj_map,
        PushoutObjObj.ofHasPushout_ι, mk_left, leftBifunctor_obj_obj_left,
        leftBifunctor_obj_obj_hom, map_comp, NatTrans.comp_app, Category.assoc, associator,
        associator_iso_left,
        associator_hom_left, associator_hom_left_aux, PushoutObjObj_whiskerRight_iso_hom,
        HasColimit.isoOfNatIso_hom_desc, associator_inv_left, tensorLeft_PushoutObjObj_iso_hom,
        Category.id_comp, comp_left, leftBifunctor_map_app_left, leftBifunctor_map_app_right,
        leftBifunctor_obj_map_right, whisker_assoc, leftBifunctor_obj_map_left, tensor_whiskerLeft,
        isoMk_hom_left, IsPushout.inl_desc_assoc, colimit.ι_desc, PushoutCocone.mk_pt,
        PushoutCocone.mk_ι_app, Iso.inv_hom_id_assoc, whiskerRight_tensor, colimit.ι_desc_assoc,
        span_left, IsPushout.inl_desc, whisker_exchange_assoc, Iso.hom_inv_id_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc]
    · apply IsPushout_ofWhiskerRight.hom_ext
      · simp only [id_obj, curriedTensor_obj_obj, PushoutObjObj.ofHasPushout_pt,
        curriedTensor_map_app, curriedTensor_obj_map, PushoutObjObj.ofHasPushout_ι, mk_left,
        leftBifunctor_obj_obj_left, leftBifunctor_obj_obj_right, leftBifunctor_obj_obj_hom,
        map_comp, NatTrans.comp_app, Category.assoc, associator, associator_iso_left,
        associator_hom_left, associator_hom_left_aux, PushoutObjObj_whiskerRight_iso_hom,
        HasColimit.isoOfNatIso_hom_desc, associator_inv_left, tensorLeft_PushoutObjObj_iso_hom,
        Category.id_comp, comp_left, leftBifunctor_map_app_left, leftBifunctor_map_app_right,
        leftBifunctor_obj_map_right, whisker_assoc, leftBifunctor_obj_map_left, tensor_whiskerLeft,
        isoMk_hom_left, IsPushout.inr_desc_assoc, colimit.ι_desc, PushoutCocone.mk_pt,
        PushoutCocone.mk_ι_app, ← whisker_exchange_assoc, whisker_inl_desc_assoc, comp_whiskerRight,
        IsPushout.inl_isoPushout_hom_assoc, Cocones.precompose_obj_pt, Cocones.precompose_obj_ι,
        span_left, const_obj_obj, spanExt_hom_app_left, Iso.inv_hom_id_assoc, whiskerRight_tensor,
        colimit.ι_desc_assoc, span_right, IsPushout.inl_desc_assoc, IsPushout.inl_desc,
        Iso.cancel_iso_hom_left, ← MonoidalCategory.whiskerLeft_comp_assoc]
        rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, IsPushout.inr_desc,
          associator_naturality_left_assoc, Iso.inv_hom_id_assoc]
        simp only [whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]
      · simp only [id_obj, curriedTensor_obj_obj, PushoutObjObj.ofHasPushout_pt,
        curriedTensor_map_app, curriedTensor_obj_map, PushoutObjObj.ofHasPushout_ι, mk_left,
        leftBifunctor_obj_obj_left, leftBifunctor_obj_obj_right, leftBifunctor_obj_obj_hom,
        map_comp, NatTrans.comp_app, Category.assoc, associator, associator_iso_left,
        associator_hom_left, associator_hom_left_aux, PushoutObjObj_whiskerRight_iso_hom,
        HasColimit.isoOfNatIso_hom_desc, associator_inv_left, tensorLeft_PushoutObjObj_iso_hom,
        Category.id_comp, comp_left, leftBifunctor_map_app_left, leftBifunctor_map_app_right,
        leftBifunctor_obj_map_right, whisker_assoc, leftBifunctor_obj_map_left, tensor_whiskerLeft,
        isoMk_hom_left, IsPushout.inr_desc_assoc, colimit.ι_desc, PushoutCocone.mk_pt,
        PushoutCocone.mk_ι_app, whisker_inr_desc_assoc, comp_whiskerRight, whiskerRight_tensor,
        colimit.ι_desc_assoc, span_right, IsPushout.inr_isoPushout_hom_assoc,
        Cocones.precompose_obj_pt, Cocones.precompose_obj_ι, const_obj_obj, spanExt_hom_app_right,
        IsPushout.inr_desc, Iso.hom_inv_id_assoc]
        rw [associator_naturality_left_assoc]
        simp only [whiskerRight_tensor, ← whisker_exchange_assoc, tensor_whiskerLeft,
          IsPushout.inr_isoPushout_hom_assoc, colimit.ι_desc, Cocones.precompose_obj_pt,
          PushoutCocone.mk_pt, Cocones.precompose_obj_ι, NatTrans.comp_app, span_right,
          const_obj_obj, spanExt_hom_app_right, PushoutCocone.mk_ι_app, Category.assoc,
          Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  · simp

@[simp]
lemma pentagon_aux
    [∀ S : C, PreservesColimitsOfSize (tensorLeft S)]
    [∀ S : C, PreservesColimitsOfSize (tensorRight S)]
    (W X Y Z : Arrow C) :
    pushout.inr (((W.hom □ X.hom) □ Y.hom) ▷ Z.left)
      ((mk ((W.hom □ X.hom) □ Y.hom)).left ◁ Z.hom) ≫
    (((leftBifunctor _).map (associator W.hom X.hom Y.hom).hom).app Z ≫
    (associator W.hom (X.hom □ Y.hom) Z.hom).hom ≫
    ((leftBifunctor _).obj W).map (associator X.hom Y.hom Z.hom).hom).left =
    pushout.inr (((W.hom □ X.hom) □ Y.hom) ▷ Z.left)
      ((mk ((W.hom □ X.hom) □ Y.hom)).left ◁ Z.hom) ≫
    ((associator (W.hom □ X.hom) Y.hom Z.hom).hom ≫
    (associator W.hom X.hom (Y.hom □ Z.hom)).hom).left := by
  have := PushoutProduct.whiskerRight_iso (W := Z.left) (W.hom □ X.hom) Y.hom
  sorry

@[simp]
lemma pentagon
    [∀ S : C, PreservesColimitsOfSize (tensorLeft S)]
    [∀ S : C, PreservesColimitsOfSize (tensorRight S)]
    (W X Y Z : Arrow C) :
    ((leftBifunctor _).map (associator W.hom X.hom Y.hom).hom).app Z ≫
    (associator W.hom (((leftBifunctor _).obj X).obj Y).hom Z.hom).hom ≫
    ((leftBifunctor _).obj W).map (associator X.hom Y.hom Z.hom).hom =
    (associator (((leftBifunctor _).obj W).obj X).hom Y.hom Z.hom).hom ≫
    (associator W.hom X.hom (((leftBifunctor _).obj Y).obj Z).hom).hom := by
  apply Arrow.hom_ext
  · apply pushout.hom_ext
    · simp only [id_obj, PushoutObjObj.ofHasPushout_pt, curriedTensor_obj_obj,
      curriedTensor_map_app, curriedTensor_obj_map, PushoutObjObj.ofHasPushout_ι, mk_right,
      leftBifunctor_obj_obj_left, mk_left, mk_hom, associator, associator_iso_left,
      associator_hom_left, associator_hom_left_aux, PushoutObjObj_whiskerRight_iso_hom,
      Category.assoc, HasColimit.isoOfNatIso_hom_desc, associator_inv_left,
      tensorLeft_PushoutObjObj_iso_hom, Category.id_comp, leftBifunctor_obj_obj_right,
      leftBifunctor_obj_obj_hom, comp_left, leftBifunctor_map_app_left, tensor_whiskerLeft,
      isoMk_hom_right, isoMk_hom_left, leftBifunctor_obj_map_left, IsPushout.inl_desc_assoc,
      colimit.ι_desc_assoc, span_left, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app,
      IsPushout.inl_desc, whiskerRight_tensor, colimit.ι_desc, Iso.inv_hom_id_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc]
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc, pentagon_assoc]
    · exact pentagon_aux ..
  · exact MonoidalCategory.pentagon W.right X.right Y.right Z.right

end PushoutProduct

noncomputable
instance [HasPushouts C] [HasInitial C] [CartesianMonoidalCategory C]
    [MonoidalClosed C] [BraidedCategory C]
    [∀ S : C, PreservesColimitsOfSize (tensorLeft S)]
    [∀ S : C, PreservesColimitsOfSize (tensorRight S)] : MonoidalCategory (Arrow C) where
  tensorObj X Y := ((leftBifunctor (curriedTensor C)).obj X).obj Y
  whiskerLeft X _ _ f := ((leftBifunctor (curriedTensor C)).obj X).map f
  whiskerRight f X := ((leftBifunctor (curriedTensor C)).map f).app X
  tensorUnit := initial.to (𝟙_ C)
  associator X Y Z := PushoutProduct.associator X.hom Y.hom Z.hom
  associator_naturality := PushoutProduct.associator_naturality
  pentagon := PushoutProduct.pentagon
  leftUnitor := PushoutProduct.leftUnitor
  leftUnitor_naturality f := by
    apply Arrow.hom_ext
    · apply pushout.hom_ext
      · simp
      · apply (IsInitial.ofIso initialIsInitial (mulZero initialIsInitial).symm).hom_ext
    · exact leftUnitor_naturality f.right
  rightUnitor := PushoutProduct.rightUnitor
  rightUnitor_naturality f := by
    apply Arrow.hom_ext
    · apply pushout.hom_ext
      · apply (IsInitial.ofIso initialIsInitial (zeroMul initialIsInitial).symm).hom_ext
      · simp
    · exact rightUnitor_naturality f.right
  triangle X Y := by
    apply Arrow.hom_ext
    · apply pushout.hom_ext
      · simp [← MonoidalCategory.whiskerLeft_comp_assoc]
      · apply IsPushout_ofWhiskerRight.hom_ext
        · apply (IsInitial.ofIso initialIsInitial ((initialIsoIsInitial ?_) ≪≫
            (mulZero ?_).symm)).hom_ext
          all_goals exact IsInitial.ofIso initialIsInitial (zeroMul initialIsInitial).symm
        · simp [← comp_whiskerRight_assoc]
    · exact MonoidalCategory.triangle X.right Y.right

end CategoryTheory.Arrow
