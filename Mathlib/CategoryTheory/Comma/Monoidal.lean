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

namespace CategoryTheory

open Opposite Limits MonoidalCategory Functor PushoutObjObj

variable {C : Type u} [Category.{v} C]

section IsPushout

namespace IsPushout

variable [MonoidalCategory C] {Z X Y P W : C} {f : Z ⟶ X} {g : Z ⟶ Y}
    {inl : X ⟶ P} {inr : Y ⟶ P} (hP : IsPushout f g inl inr)
    {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k)

@[reassoc (attr := simp)]
lemma whiskerLeft_inl_desc {Q : C} :
    Q ◁ inl ≫ Q ◁ hP.desc h k w = Q ◁ h := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
lemma whiskerLeft_inr_desc {Q : C} :
    Q ◁ inr ≫ Q ◁ hP.desc h k w = Q ◁ k := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
lemma inl_desc_whiskerRight {Q : C} :
    inl ▷ Q ≫ hP.desc h k w ▷ Q = h ▷ Q := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
lemma inr_desc_whiskerRight {Q : C} :
    inr ▷ Q ≫ hP.desc h k w ▷ Q = k ▷ Q := by
  simp [← comp_whiskerRight]

@[reassoc]
lemma whiskerLeft_w (hP : IsPushout f g inl inr) {Q : C} :
    Q ◁ f ≫ Q ◁ inl = Q ◁ g ≫ Q ◁ inr := by
  simp [← MonoidalCategory.whiskerLeft_comp, hP.w]

@[reassoc]
lemma w_whiskerRight (hP : IsPushout f g inl inr) {Q : C} :
    f ▷ Q ≫ inl ▷ Q = g ▷ Q ≫ inr ▷ Q := by
  simp [← MonoidalCategory.comp_whiskerRight, hP.w]

end IsPushout

end IsPushout

section Pushout

variable [HasPushouts C] [MonoidalCategory C]
  {A B X Y Z W : C} (f : A ⟶ B) (g : X ⟶ Y) (h : Z ⟶ W)

---change
@[reassoc]
lemma pushout_temp₁ {P : C} {h₁ : Y ⊗ Z ⟶ P} {h₂ : A ⊗ P ⟶ A ⊗ Y ⊗ W} :
    f ▷ Y ▷ Z ≫ (α_ B Y Z).hom ≫ B ◁ h₁ ≫ pushout.inl (f ▷ P) h₂ =
      (α_ A Y Z).hom ≫ A ◁ h₁ ≫ h₂ ≫ pushout.inr (f ▷ P) h₂ := by
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, pushout.condition]

---change
@[reassoc]
lemma pushout_temp₂ {P : C} {h₁ : P ⟶ B ⊗ Y} {h₂ : A ⊗ Y ⟶ P} :
    A ◁ Y ◁ h ≫ (α_ A Y W).inv ≫
      h₂ ▷ W ≫ pushout.inr (h₁ ▷ Z) (P ◁ h) =
    (α_ A Y Z).inv ≫
      (h₂ ≫ h₁) ▷ Z ≫ pushout.inl (h₁ ▷ Z) (P ◁ h) := by
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ← pushout.condition,
    ← comp_whiskerRight_assoc]

end Pushout

@[simp]
noncomputable
abbrev pushoutProduct [HasPushouts C] [MonoidalCategory C] := (curriedTensor C).leibnizPushout

notation3 X₁ " □ " X₂:10 => ((curriedTensor _).leibnizPushout.obj X₁).obj X₂

namespace Arrow

section Monoidal

variable [HasPushouts C] [MonoidalCategory C]
  {A B X Y Z W : C} (f : A ⟶ B) (g : X ⟶ Y) (h : Z ⟶ W)

@[simps!]
noncomputable
def PushoutProduct.tensorLeft_PushoutObjObj_iso
    [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorLeft W)] :
    W ⊗ (pushout (f ▷ X) (A ◁ g)) ≅
      (pushout ((W ◁ f) ▷ X) ((W ⊗ A) ◁ g)) := by
  refine ((tensorLeft W).map_isPushout (IsPushout.of_hasPushout _ _)).isoPushout ≪≫
  --refine (PreservesPushout.iso (tensorLeft W) _ _).symm ≪≫
    HasColimit.isoOfNatIso (spanExt ?_ ?_ ?_ ?_ ?_)
  · exact (α_ W A X).symm
  · exact (α_ W B X).symm
  · exact (α_ W A Y).symm
  · exact (associator_inv_naturality_middle W f X).symm
  · exact (associator_inv_naturality_right W A g).symm

@[simps!]
noncomputable
def PushoutProduct.PushoutObjObj_whiskerRight_iso
    [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight W)] :
    (pushout (f ▷ X) (A ◁ g)) ⊗ W ≅
    (pushout (f ▷ (X ⊗ W)) (A ◁ g ▷ W)) := by
  refine ((tensorRight W).map_isPushout (IsPushout.of_hasPushout _ _)).isoPushout ≪≫
  --refine (PreservesPushout.iso (tensorRight W) _ _).symm ≪≫
    HasColimit.isoOfNatIso (spanExt ?_ ?_ ?_ ?_ ?_)
  · exact α_ A X W
  · exact α_ B X W
  · exact α_ A Y W
  · exact (associator_naturality_left f X W).symm
  · exact (associator_naturality_middle A g W).symm

@[simps!]
noncomputable
def PushoutProduct.whiskerRight_iso [PreservesColimitsOfSize (tensorRight W)] :
    Arrow.mk ((f □ g).hom ▷ W) ≅ (f □ (g ▷ W)) := by
  refine Arrow.isoMk (PushoutObjObj_whiskerRight_iso f g) (α_ B Y W) ?_
  · apply ((tensorRight W).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
    all_goals simp [PushoutObjObj.ι]

@[simps!]
noncomputable
def PushoutProduct.whiskerLeft_iso [PreservesColimitsOfSize (tensorLeft W)] :
    Arrow.mk (W ◁ (f □ g).hom) ≅ ((W ◁ f) □ g) := by
  refine Arrow.isoMk (tensorLeft_PushoutObjObj_iso _ _) (α_ W B Y).symm ?_
  · apply ((tensorLeft W).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
    all_goals simp [PushoutObjObj.ι]

@[simp]
noncomputable
def PushoutProduct.associator_hom_left_aux
    [PreservesColimitsOfSize (tensorRight Z)]
    [PreservesColimitsOfSize (tensorRight W)] :
    (ofHasPushout (curriedTensor C) (f □ g).hom h).pt ⟶
      (ofHasPushout (curriedTensor C) f (g □ h).hom).pt := by
  refine pushout.desc ?_ ?_ ?_
  · exact (α_ B Y Z).hom ≫ (B ◁ pushout.inl _ _) ≫ pushout.inl _ _
  · refine (PushoutObjObj_whiskerRight_iso _ _).hom ≫
      pushout.desc ((B ◁ pushout.inr _ _) ≫ pushout.inl _ _) (pushout.inr _ _) ?_
    · dsimp [PushoutObjObj.ι]
      rw [← whisker_exchange_assoc, pushout.condition,
        ← MonoidalCategory.whiskerLeft_comp_assoc, IsPushout.inr_desc]
  · apply ((tensorRight Z).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
    · simp [PushoutObjObj.ι, (IsPushout.of_hasPushout ..).whiskerLeft_w_assoc,
        ← whisker_exchange_assoc]
    · simp [PushoutObjObj.ι, ← whisker_exchange_assoc, pushout_temp₁]

@[simp]
noncomputable
def PushoutProduct.associator_inv_left_aux
    [PreservesColimitsOfSize (tensorLeft A)]
    [PreservesColimitsOfSize (tensorLeft B)] :
    (ofHasPushout (curriedTensor C) f (g □ h).hom).pt ⟶
      (ofHasPushout (curriedTensor C) (f □ g).hom h).pt := by
  refine pushout.desc ?_ ?_ ?_
  · refine (tensorLeft_PushoutObjObj_iso g h).hom ≫ pushout.desc ?_ ?_ ?_
    · exact 𝟙 _ ≫ pushout.inl _ _
    · exact (pushout.inl _ _ ▷ W) ≫ pushout.inr _ _
    · dsimp [PushoutObjObj.ι]
      rw [Category.id_comp, whisker_exchange_assoc, ← pushout.condition,
        ← MonoidalCategory.comp_whiskerRight_assoc, IsPushout.inl_desc]
  · exact (α_ _ _ _).inv ≫ (pushout.inr _ _) ▷ _ ≫ pushout.inr _ _
  · apply ((tensorLeft A).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
    · simp [PushoutObjObj.ι, whisker_exchange_assoc, pushout_temp₂]
    · simp [PushoutObjObj.ι, whisker_exchange_assoc, ← comp_whiskerRight_assoc, pushout.condition]

@[simps]
noncomputable
def PushoutProduct.associator_iso_left
    [PreservesColimitsOfSize (tensorLeft A)]
    [PreservesColimitsOfSize (tensorLeft B)]
    [PreservesColimitsOfSize (tensorRight Z)]
    [PreservesColimitsOfSize (tensorRight W)] :
    (ofHasPushout (curriedTensor C) (f □ g).hom h).pt ≅
      (ofHasPushout (curriedTensor C) f (g □ h).hom).pt where
  hom := associator_hom_left_aux f g h
  inv := associator_inv_left_aux f g h
  hom_inv_id := by
    apply pushout.hom_ext
    · simp
    · exact ((tensorRight W).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
        (by simp) (by simp)
  inv_hom_id := by
    apply pushout.hom_ext
    · exact ((tensorLeft B).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
        (by simp) (by simp)
    · simp

@[simps!]
noncomputable
def PushoutProduct.associator
    [∀ S : C, PreservesColimitsOfSize (tensorLeft S)]
    [∀ S : C, PreservesColimitsOfSize (tensorRight S)] (X₁ X₂ X₃ : Arrow C) :
    ((X₁ □ X₂) □ X₃) ≅ (X₁ □ (X₂ □ X₃)) := by
  refine Arrow.isoMk (associator_iso_left X₁.hom X₂.hom X₃.hom) (α_ _ _ _) ?_
  · apply pushout.hom_ext
    · simp [← MonoidalCategory.whiskerLeft_comp]
    · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
      · simp [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.comp_whiskerRight_assoc]
      · simp [← MonoidalCategory.comp_whiskerRight_assoc]

omit [HasPushouts C] in
@[reassoc]
lemma _root_.CategoryTheory.MonoidalCategory.temp₁ (X₁ X₂ X₃ Y₁ Y₂ Y₃ : Arrow C)
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    (α_ X₁.left X₂.right X₃.right).hom ≫
    X₁.left ◁ X₂.right ◁ f₃.right ≫
    (α_ X₁.left X₂.right Y₃.right).inv ≫
    f₁.left ▷ X₂.right ▷ Y₃.right ≫
    (α_ Y₁.left X₂.right Y₃.right).hom ≫
    Y₁.left ◁ f₂.right ▷ Y₃.right =
    f₁.left ▷ X₂.right ▷ X₃.right ≫
    (α_ Y₁.left X₂.right X₃.right).hom ≫
    Y₁.left ◁ f₂.right ▷ X₃.right ≫
    Y₁.left ◁ Y₂.right ◁ f₃.right := by
  rw [associator_inv_naturality_right_assoc, associator_naturality_left_assoc,
    associator_naturality_right_assoc, associator_naturality_left_assoc, Iso.cancel_iso_hom_left,
    Iso.inv_comp_eq, Iso.cancel_iso_hom_left, whisker_exchange_assoc,
    ← MonoidalCategory.whiskerLeft_comp, whisker_exchange, MonoidalCategory.whiskerLeft_comp]

omit [HasPushouts C] in
@[reassoc]
lemma temp₂ (X₁ X₂ X₃ Y₁ Y₃ : Arrow C) (f₁ : X₁ ⟶ Y₁) (f₃ : X₃ ⟶ Y₃) :
    X₁.right ◁ X₂.left ◁ f₃.right ≫
    (α_ X₁.right X₂.left Y₃.right).inv ≫
    f₁.right ▷ X₂.left ▷ Y₃.right ≫
    (α_ Y₁.right X₂.left Y₃.right).hom =
    (α_ X₁.right X₂.left X₃.right).inv ≫
    f₁.right ▷ X₂.left ▷ X₃.right ≫
    (α_ Y₁.right X₂.left X₃.right).hom ≫
    Y₁.right ◁ X₂.left ◁ f₃.right := by
  sorry
  --cat_disch

@[reassoc]
lemma temp₃ (X₁ X₂ X₃ Y₁ Y₂ Y₃ : Arrow C) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    X₁.right ◁ X₂.left ◁ f₃.right ≫
    (α_ X₁.right X₂.left Y₃.right).inv ≫
    f₁.right ▷ X₂.left ▷ Y₃.right ≫
    (α_ Y₁.right X₂.left Y₃.right).hom ≫
    Y₁.right ◁ f₂.left ▷ Y₃.right ≫
    Y₁.right ◁ pushout.inr (Y₂.hom ▷ Y₃.left) (Y₂.left ◁ Y₃.hom) =
    X₁.right ◁ f₂.left ▷ X₃.right ≫
    X₁.right ◁ Y₂.left ◁ f₃.right ≫
    X₁.right ◁ pushout.inr (Y₂.hom ▷ Y₃.left) (Y₂.left ◁ Y₃.hom) ≫
    f₁.right ▷ pushout (Y₂.hom ▷ Y₃.left) (Y₂.left ◁ Y₃.hom) := by
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [whisker_exchange, whisker_exchange_assoc, ← whisker_exchange]
  simp [temp₂_assoc]

lemma PushoutProduct.associator_naturality
    [∀ S : C, PreservesColimitsOfSize (tensorLeft S)]
    [∀ S : C, PreservesColimitsOfSize (tensorRight S)]
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Arrow C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((pushoutProduct.map ((pushoutProduct.map f₁).app X₂ ≫
    (pushoutProduct.obj Y₁).map f₂)).app X₃ ≫
    (pushoutProduct.obj (Y₁ □ Y₂)).map f₃) ≫
    (associator Y₁ Y₂ Y₃).hom =
    (associator X₁ X₂ X₃).hom ≫
    (pushoutProduct.map f₁).app (X₂ □ X₃) ≫
    (pushoutProduct.obj Y₁).map ((pushoutProduct.map f₂).app X₃ ≫
    (pushoutProduct.obj Y₂).map f₃) := by
  apply Arrow.hom_ext
  · apply pushout.hom_ext
    · simp [whisker_exchange_assoc]
    · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
      · simp [← whisker_exchange_assoc, temp₃_assoc]
      · simp [← whisker_exchange_assoc, temp₁_assoc]
  · simp

lemma PushoutProduct.pentagon_aux
    [∀ S : C, PreservesColimitsOfSize (tensorLeft S)]
    [∀ S : C, PreservesColimitsOfSize (tensorRight S)]
    (W X Y Z : Arrow C) :
    pushout.inr (((W □ X) □ Y).hom ▷ Z.left) (((W □ X) □ Y).left ◁ Z.hom) ≫
    ((pushoutProduct.map (associator W X Y).hom).app Z ≫
    (associator W (X □ Y) Z).hom ≫
    (pushoutProduct.obj W).map (associator X Y Z).hom).left =
    pushout.inr (((W □ X) □ Y).hom ▷ Z.left) (((W □ X) □ Y).left ◁ Z.hom) ≫
    ((associator (W □ X) Y Z).hom ≫
    (associator W X (Y □ Z)).hom).left := by
  apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
  · simp only [id_obj, leibnizPushout_obj_obj, ofHasPushout_pt, curriedTensor_obj_obj,
    curriedTensor_map_app, curriedTensor_obj_map, mk_right, flip_obj_obj, pushoutProduct, mk_left,
    mk_hom, flip_obj_map, leibnizPushout_map_app, leibnizPushout_obj_map, comp_left,
    mapArrowLeft_left, ofHasPushout_ι, tensor_whiskerLeft, ofHasPushout_inl, ofHasPushout_inr,
    associator_hom_right, associator_hom_left, mapArrowRight_left, IsPushout.inr_desc_assoc,
    Category.assoc, colimit.ι_desc_assoc, span_right, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app,
    whiskerRight_tensor, IsPushout.inl_isoPushout_hom_assoc, span_left, Cocones.precompose_obj_pt,
    Cocones.precompose_obj_ι, NatTrans.comp_app, const_obj_obj, spanExt_hom_app_left,
    colimit.ι_desc, Iso.inv_hom_id_assoc, ← comp_whiskerRight_assoc]
    simp only [comp_whiskerRight, whisker_assoc, Category.assoc, IsPushout.inl_isoPushout_hom_assoc,
      colimit.ι_desc_assoc, span_left, Cocones.precompose_obj_pt, PushoutCocone.mk_pt,
      Cocones.precompose_obj_ι, NatTrans.comp_app, const_obj_obj, spanExt_hom_app_left,
      PushoutCocone.mk_ι_app, IsPushout.inl_desc, Iso.inv_hom_id_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc]
    cat_disch
  · apply ((tensorRight _ ⋙ tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
    · simp only [id_obj, curriedTensor_obj_obj, comp_obj, flip_obj_obj, pushoutProduct,
      leibnizPushout_obj_obj, ofHasPushout_pt, curriedTensor_map_app, curriedTensor_obj_map,
      mk_left, mk_right, mk_hom, Functor.comp_map, flip_obj_map, leibnizPushout_map_app,
      leibnizPushout_obj_map, comp_left, mapArrowLeft_left, ofHasPushout_ι, tensor_whiskerLeft,
      ofHasPushout_inl, ofHasPushout_inr, associator_hom_right, associator_hom_left,
      mapArrowRight_left, IsPushout.inr_desc_assoc, Category.assoc, colimit.ι_desc_assoc,
      span_right, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, whiskerRight_tensor,
      IsPushout.inr_isoPushout_hom_assoc, Cocones.precompose_obj_pt, Cocones.precompose_obj_ι,
      NatTrans.comp_app, const_obj_obj, spanExt_hom_app_right, colimit.ι_desc,
      ← comp_whiskerRight_assoc]
      simp only [IsPushout.inl_isoPushout_hom_assoc, colimit.ι_desc, Cocones.precompose_obj_pt,
        PushoutCocone.mk_pt, Cocones.precompose_obj_ι, NatTrans.comp_app, span_left, const_obj_obj,
        spanExt_hom_app_left, PushoutCocone.mk_ι_app, comp_whiskerRight, whisker_assoc,
        Category.assoc, colimit.ι_desc_assoc, IsPushout.inl_desc, Iso.inv_hom_id_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc, associator_naturality_left_assoc]
      cat_disch
    · simp only [id_obj, curriedTensor_obj_obj, comp_obj, flip_obj_obj, pushoutProduct,
      leibnizPushout_obj_obj, ofHasPushout_pt, curriedTensor_map_app, curriedTensor_obj_map,
      mk_left, mk_right, mk_hom, Functor.comp_map, flip_obj_map, leibnizPushout_map_app,
      leibnizPushout_obj_map, comp_left, mapArrowLeft_left, ofHasPushout_ι, tensor_whiskerLeft,
      ofHasPushout_inl, ofHasPushout_inr, associator_hom_right, associator_hom_left,
      mapArrowRight_left, IsPushout.inr_desc_assoc, Category.assoc, colimit.ι_desc_assoc,
      span_right, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, whiskerRight_tensor,
      IsPushout.inr_isoPushout_hom_assoc, Cocones.precompose_obj_pt, Cocones.precompose_obj_ι,
      NatTrans.comp_app, const_obj_obj, spanExt_hom_app_right, colimit.ι_desc,
      ← comp_whiskerRight_assoc, associator_naturality_left_assoc]
      cat_disch

lemma PushoutProduct.pentagon
    [∀ S : C, PreservesColimitsOfSize (tensorLeft S)]
    [∀ S : C, PreservesColimitsOfSize (tensorRight S)]
    (W X Y Z : Arrow C) :
    (pushoutProduct.map (associator W X Y).hom).app Z ≫
      (associator W (X □ Y) Z).hom ≫
        (pushoutProduct.obj W).map (associator X Y Z).hom =
    (associator (W □ X) Y Z).hom ≫
      (associator W X (Y □ Z)).hom := by
  apply Arrow.hom_ext
  · apply pushout.hom_ext
    · simp only [leibnizPushout_obj_obj, id_obj, ofHasPushout_pt, curriedTensor_obj_obj,
        curriedTensor_map_app, curriedTensor_obj_map, mk_left, mk_right, mk_hom, pushoutProduct,
        leibnizPushout_map_app, leibnizPushout_obj_map, comp_left, mapArrowLeft_left,
        ofHasPushout_ι, tensor_whiskerLeft, ofHasPushout_inl, ofHasPushout_inr,
        associator_hom_right, associator_hom_left, mapArrowRight_left, IsPushout.inl_desc_assoc,
        Category.assoc, colimit.ι_desc_assoc, span_left, PushoutCocone.mk_pt,
        PushoutCocone.mk_ι_app, IsPushout.inl_desc, ← MonoidalCategory.whiskerLeft_comp_assoc,
        colimit.ι_desc, whiskerRight_tensor, Iso.inv_hom_id_assoc]
      rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, pentagon_assoc]
    · apply pentagon_aux
  · exact MonoidalCategory.pentagon W.right X.right Y.right Z.right

@[simps!]
noncomputable
def PushoutProduct.braiding_left_iso [BraidedCategory C] :
    (ofHasPushout (curriedTensor C) f g).pt ≅
      (ofHasPushout (curriedTensor C) g f).pt :=
  pushoutSymmetry (f ▷ X) (A ◁ g) ≪≫
    (HasColimit.isoOfNatIso (spanExt (β_ _ _) (β_ _ _) (β_ _ _)
    (BraidedCategory.braiding_naturality_right A g).symm
    (BraidedCategory.braiding_naturality_left f X).symm))

@[simps!]
noncomputable
def PushoutProduct.braiding [BraidedCategory C] (X Y : Arrow C) : (X □ Y) ≅ (Y □ X) :=
  Arrow.isoMk (braiding_left_iso X.hom Y.hom) (β_ _ _) (by cat_disch)

end Monoidal

section CartesianMonoidal

variable [HasInitial C] [HasPushouts C] [CartesianMonoidalCategory C] [MonoidalClosed C]
  {A B X Y Z W : C} (f : A ⟶ B) (g : X ⟶ Y) (h : Z ⟶ W)

@[simps!]
noncomputable
def PushoutProduct.leftUnitor [BraidedCategory C]
    (X : Arrow C) :
    (initial.to (𝟙_ C) □ X.hom) ≅ X := by
  refine Arrow.isoMk ?_ (λ_ X.right) ?_
  · refine Iso.mk ?_ ((λ_ X.left).inv ≫ pushout.inl _ _) ?_ ?_
    · refine pushout.desc (λ_ X.left).hom ?_ ?_
      · exact IsInitial.to (IsInitial.ofIso initialIsInitial (mulZero initialIsInitial).symm) _
      · apply (IsInitial.ofIso initialIsInitial (mulZero initialIsInitial).symm).hom_ext
    · apply pushout.hom_ext
      · simp
      · apply (IsInitial.ofIso initialIsInitial (mulZero initialIsInitial).symm).hom_ext
    · simp
  · apply pushout.hom_ext
    · simp
    · apply (IsInitial.ofIso initialIsInitial (mulZero initialIsInitial).symm).hom_ext

@[simps!]
noncomputable
def PushoutProduct.rightUnitor (X : Arrow C) :
    (X □ initial.to (𝟙_ C)) ≅ X := by
  refine Arrow.isoMk ?_ (ρ_ X.right) ?_
  · refine Iso.mk ?_ ((ρ_ X.left).inv ≫ pushout.inr _ _) ?_ ?_
    · refine pushout.desc ?_ (ρ_ X.left).hom ?_
      · exact IsInitial.to (IsInitial.ofIso initialIsInitial (zeroMul initialIsInitial).symm) _
      · apply (IsInitial.ofIso initialIsInitial (zeroMul initialIsInitial).symm).hom_ext
    · apply pushout.hom_ext
      · apply (IsInitial.ofIso initialIsInitial (zeroMul initialIsInitial).symm).hom_ext
      · simp
    · simp
  · apply pushout.hom_ext
    · apply (IsInitial.ofIso initialIsInitial (zeroMul initialIsInitial).symm).hom_ext
    · simp

end CartesianMonoidal

section MonoidalClosed

variable [HasPushouts C] [HasPullbacks C] [MonoidalCategory C] [MonoidalClosed C]
  {A B X Y Z W : C} (f : A ⟶ B) (g : X ⟶ Y) (h : Z ⟶ W)

open MonoidalClosed

@[simps]
noncomputable
def LeibnizAdjunction.unit (X : Arrow C) :
    𝟭 (Arrow C) ⟶ pushoutProduct.obj X ⋙
      MonoidalClosed.internalHom.leibnizPullback.obj (op X) where
  app _ := {
    left := curry (pushout.inl _ _)
    right := pullback.lift (curry (pushout.inr _ _)) (curry (𝟙 _))
      (by simp [curry_pre_app, eq_curry_iff, uncurry_natural_right])
    w := by
      apply pullback.hom_ext
      · simp [curry_pre_app, pushout.condition, curry_natural_left]
      · simp [← curry_natural_right, curry_eq_iff, uncurry_natural_left] }
  naturality _ _ _ := by
    apply Arrow.hom_ext
    · simp [← curry_natural_right, eq_curry_iff, uncurry_natural_left]
    · apply pullback.hom_ext
      all_goals simp [← curry_natural_right, eq_curry_iff, uncurry_natural_left]

@[simps]
noncomputable
def LeibnizAdjunction.counit (X : Arrow C) :
    MonoidalClosed.internalHom.leibnizPullback.obj (op X) ⋙
      pushoutProduct.obj X ⟶ 𝟭 (Arrow C) where
  app _ := {
    left := by
      apply pushout.desc (uncurry (𝟙 _)) (uncurry (pullback.fst _ _))
        (by simp [uncurry_eq, ← MonoidalCategory.whiskerLeft_comp_assoc])
    right := uncurry (pullback.snd _ _)
    w := by
      apply pushout.hom_ext
      · simp [uncurry_eq, ← MonoidalCategory.whiskerLeft_comp_assoc]
      · simp [uncurry_eq, ← whisker_exchange_assoc, ← id_tensor_pre_app_comp_ev,
        ← MonoidalCategory.whiskerLeft_comp_assoc, ← pullback.condition] }
  naturality _ _ _ := by
    apply Arrow.hom_ext
    · apply pushout.hom_ext
      · simp [uncurry_id_eq_ev]
      · simp [uncurry_eq, ← MonoidalCategory.whiskerLeft_comp_assoc]
    · simp [uncurry_eq, ← MonoidalCategory.whiskerLeft_comp_assoc]

@[simps]
noncomputable
def LeibnizAdjunction.adj (X : Arrow C) :
    (curriedTensor C).leibnizPushout.obj X ⊣
      MonoidalClosed.internalHom.leibnizPullback.obj (op X) where
  unit := unit X
  counit := counit X
  left_triangle_components _ := by
    apply Arrow.hom_ext
    · apply pushout.hom_ext
      all_goals simp [uncurry_eq, ← MonoidalCategory.whiskerLeft_comp_assoc]
    · simp [uncurry_eq, ← MonoidalCategory.whiskerLeft_comp_assoc]
  right_triangle_components _ := by
    apply Arrow.hom_ext
    · simp [← curry_natural_right]
    · apply pullback.hom_ext
      all_goals simp [← curry_natural_right]

@[simps]
noncomputable
instance leibnizAdjunction₂ :
    ParametrizedAdjunction (curriedTensor C).leibnizPushout
      MonoidalClosed.internalHom.leibnizPullback where
  adj := LeibnizAdjunction.adj
  unit_whiskerRight_map _ := by
    ext
    · simp [← curry_natural_right, curry_pre_app]
    · apply pullback.hom_ext
      all_goals simp [← curry_natural_right, curry_pre_app]

end MonoidalClosed

@[simps]
noncomputable
instance [HasInitial C] [HasPushouts C] [CartesianMonoidalCategory C] [MonoidalClosed C]
    [BraidedCategory C]
    [∀ S : C, PreservesColimitsOfSize (tensorLeft S)]
    [∀ S : C, PreservesColimitsOfSize (tensorRight S)] : MonoidalCategory (Arrow C) where
  tensorObj X Y := (pushoutProduct.obj X).obj Y
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by
    apply Arrow.hom_ext
    · apply pushout.hom_ext
      all_goals simp [whisker_exchange_assoc]
    · simp [whisker_exchange_assoc]
  whiskerLeft X _ _ f := (pushoutProduct.obj X).map f
  whiskerRight f X := (pushoutProduct.map f).app X
  tensorUnit := initial.to (𝟙_ C)
  associator := PushoutProduct.associator
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
      · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
        · apply (IsInitial.ofIso initialIsInitial ((initialIsoIsInitial ?_) ≪≫
            (mulZero ?_).symm)).hom_ext
          all_goals exact IsInitial.ofIso initialIsInitial (zeroMul initialIsInitial).symm
        · simp [← comp_whiskerRight_assoc]
    · exact MonoidalCategory.triangle X.right Y.right

noncomputable
instance [HasInitial C] [HasPushouts C] [HasPullbacks C]
  [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
  [∀ (S : C), PreservesColimitsOfSize (tensorLeft S)]
  [∀ (S : C), PreservesColimitsOfSize (tensorRight S)] : MonoidalClosed (Arrow C) where
  closed X := {
    rightAdj := MonoidalClosed.internalHom.leibnizPullback.obj (op X)
    adj := LeibnizAdjunction.adj X }

lemma PushoutProduct.hexagon_forward [HasInitial C] [HasPushouts C]
    [CartesianMonoidalCategory C] [MonoidalClosed C]
    [BraidedCategory C]
    [∀ S : C, PreservesColimitsOfSize (tensorLeft S)]
    [∀ S : C, PreservesColimitsOfSize (tensorRight S)] (X Y Z : Arrow C) :
    (α_ X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
      (braiding X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫
      Y ◁ (braiding X Z).hom := by
  apply Arrow.hom_ext
  · apply pushout.hom_ext
    · simp only [tensorObj_def, pushoutProduct, leibnizPushout_obj_obj, id_obj, ofHasPushout_pt,
        curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map, mk_right, mk_left,
        mk_hom, associator_def, comp_left, associator_hom_left, braiding_hom_left,
        Category.assoc, HasColimit.isoOfNatIso_hom_desc, colimit.ι_desc_assoc, span_left,
        PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, inl_comp_pushoutSymmetry_hom_assoc,
        colimit.ι_desc, Cocones.precompose_obj_pt, Cocones.precompose_obj_ι, NatTrans.comp_app,
        span_right, const_obj_obj, spanExt_hom_app_right,
        BraidedCategory.braiding_naturality_right_assoc,
        BraidedCategory.braiding_tensor_right_hom, IsPushout.inl_isoPushout_hom_assoc,
        spanExt_hom_app_left, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, whiskerRight_def,
        leibnizPushout_map_app, whiskerLeft_def, leibnizPushout_obj_map, mapArrowLeft_left,
        ofHasPushout_ι, ofHasPushout_inl, ofHasPushout_inr, braiding_hom_right, map_comp,
        mapArrowRight_left, MonoidalCategory.whiskerLeft_comp, IsPushout.inl_desc_assoc,
        IsPushout.inl_desc]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc]
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc, inl_comp_pushoutSymmetry_hom,
        HasColimit.isoOfNatIso_ι_hom, span_right, spanExt_hom_app_right]
    · apply ((tensorRight _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
      · simp only [id_obj, curriedTensor_obj_obj, flip_obj_obj, tensorObj_def, pushoutProduct,
        leibnizPushout_obj_obj, ofHasPushout_pt, curriedTensor_map_app, curriedTensor_obj_map,
        mk_left, mk_right, mk_hom, flip_obj_map, associator_def, comp_left, associator_hom_left,
        braiding_hom_left, Category.assoc, HasColimit.isoOfNatIso_hom_desc, colimit.ι_desc_assoc,
        span_right, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, IsPushout.inl_isoPushout_hom_assoc,
        span_left, Cocones.precompose_obj_pt, Cocones.precompose_obj_ι, NatTrans.comp_app,
        const_obj_obj, spanExt_hom_app_left, inl_comp_pushoutSymmetry_hom_assoc, colimit.ι_desc,
        spanExt_hom_app_right, BraidedCategory.braiding_naturality_right_assoc,
        BraidedCategory.braiding_tensor_right_hom, IsPushout.inr_isoPushout_hom_assoc,
        Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, whiskerRight_def, leibnizPushout_map_app,
        whiskerLeft_def, leibnizPushout_obj_map, mapArrowLeft_left, ofHasPushout_ι,
        ofHasPushout_inl, ofHasPushout_inr, braiding_hom_right, map_comp, mapArrowRight_left,
        MonoidalCategory.whiskerLeft_comp, IsPushout.inr_desc_assoc, ← comp_whiskerRight_assoc]
        cat_disch
      · simp only [id_obj, curriedTensor_obj_obj, flip_obj_obj, tensorObj_def, pushoutProduct,
        leibnizPushout_obj_obj, ofHasPushout_pt, curriedTensor_map_app, curriedTensor_obj_map,
        mk_left, mk_right, mk_hom, flip_obj_map, associator_def, comp_left, associator_hom_left,
        braiding_hom_left, Category.assoc, HasColimit.isoOfNatIso_hom_desc, colimit.ι_desc_assoc,
        span_right, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, IsPushout.inr_isoPushout_hom_assoc,
        Cocones.precompose_obj_pt, Cocones.precompose_obj_ι, NatTrans.comp_app, const_obj_obj,
        spanExt_hom_app_right, inr_comp_pushoutSymmetry_hom_assoc, colimit.ι_desc, span_left,
        spanExt_hom_app_left, BraidedCategory.braiding_tensor_right_hom, Iso.inv_hom_id_assoc,
        Iso.hom_inv_id_assoc, whiskerRight_def, leibnizPushout_map_app, whiskerLeft_def,
        leibnizPushout_obj_map, mapArrowLeft_left, ofHasPushout_ι, ofHasPushout_inl,
        ofHasPushout_inr, braiding_hom_right, map_comp, mapArrowRight_left,
        MonoidalCategory.whiskerLeft_comp, IsPushout.inr_desc_assoc, ← comp_whiskerRight_assoc]
        simp only [HasColimit.isoOfNatIso_ι_hom, span_left, spanExt_hom_app_left, comp_whiskerRight,
          Category.assoc, IsPushout.inl_isoPushout_hom_assoc, colimit.ι_desc_assoc,
          Cocones.precompose_obj_pt, PushoutCocone.mk_pt, Cocones.precompose_obj_ι,
          NatTrans.comp_app, const_obj_obj, PushoutCocone.mk_ι_app, IsPushout.inl_desc,
          ← MonoidalCategory.whiskerLeft_comp_assoc]
        cat_disch
  · exact BraidedCategory.hexagon_forward X.right Y.right Z.right

lemma PushoutProduct.hexagon_reverse [HasInitial C] [HasPushouts C]
    [CartesianMonoidalCategory C] [MonoidalClosed C]
    [BraidedCategory C]
    [∀ S : C, PreservesColimitsOfSize (tensorLeft S)]
    [∀ S : C, PreservesColimitsOfSize (tensorRight S)] (X Y Z : Arrow C) :
    (α_ X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      X ◁ (braiding Y Z).hom ≫ (α_ X Z Y).inv ≫ (braiding X Z).hom ▷ Y := by
  apply Arrow.hom_ext
  · apply pushout.hom_ext
    · apply ((tensorLeft _).map_isPushout (IsPushout.of_hasPushout _ _)).hom_ext
      · simp only [id_obj, curriedTensor_obj_obj, tensorObj_def, pushoutProduct,
          leibnizPushout_obj_obj, ofHasPushout_pt, curriedTensor_map_app, curriedTensor_obj_map,
          mk_left, mk_right, mk_hom, associator_def, comp_left, associator_inv_left,
          braiding_hom_left, Category.assoc, HasColimit.isoOfNatIso_hom_desc, colimit.ι_desc_assoc,
          span_left, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, NatTrans.comp_app, const_obj_obj,
          IsPushout.inl_isoPushout_hom_assoc, Cocones.precompose_obj_pt, Cocones.precompose_obj_ι,
          spanExt_hom_app_left, Iso.symm_hom, inl_comp_pushoutSymmetry_hom_assoc, colimit.ι_desc,
          span_right, spanExt_hom_app_right, BraidedCategory.braiding_tensor_left_hom,
          Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, whiskerLeft_def, leibnizPushout_obj_map,
          whiskerRight_def, leibnizPushout_map_app, mapArrowRight_left, ofHasPushout_ι,
          ofHasPushout_inl, ofHasPushout_inr, MonoidalCategory.whiskerLeft_comp, braiding_hom_right,
          mapArrowLeft_left, map_comp, IsPushout.inl_desc_assoc]
        rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]
        simp only [inl_comp_pushoutSymmetry_hom, HasColimit.isoOfNatIso_ι_hom, span_right,
          spanExt_hom_app_right, MonoidalCategory.whiskerLeft_comp, Category.assoc,
          IsPushout.inr_isoPushout_hom_assoc, colimit.ι_desc_assoc, Cocones.precompose_obj_pt,
          PushoutCocone.mk_pt, Cocones.precompose_obj_ι, NatTrans.comp_app, const_obj_obj,
          Iso.symm_hom, PushoutCocone.mk_ι_app, IsPushout.inr_desc, ← comp_whiskerRight_assoc]
        cat_disch
      · simp only [id_obj, curriedTensor_obj_obj, tensorObj_def, pushoutProduct,
          leibnizPushout_obj_obj, ofHasPushout_pt, curriedTensor_map_app, curriedTensor_obj_map,
          mk_left, mk_right, mk_hom, associator_def, comp_left, associator_inv_left,
          braiding_hom_left, Category.assoc, HasColimit.isoOfNatIso_hom_desc, colimit.ι_desc_assoc,
          span_left, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, IsPushout.inl_desc_assoc,
          IsPushout.inr_isoPushout_hom_assoc, span_right, Cocones.precompose_obj_pt,
          Cocones.precompose_obj_ι, NatTrans.comp_app, const_obj_obj, spanExt_hom_app_right,
          Iso.symm_hom, inr_comp_pushoutSymmetry_hom_assoc, colimit.ι_desc, spanExt_hom_app_left,
          BraidedCategory.braiding_naturality_left_assoc, BraidedCategory.braiding_tensor_left_hom,
          IsPushout.inl_isoPushout_hom_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
          whiskerLeft_def, leibnizPushout_obj_map, whiskerRight_def, leibnizPushout_map_app,
          mapArrowRight_left, ofHasPushout_ι, ofHasPushout_inl, ofHasPushout_inr,
          MonoidalCategory.whiskerLeft_comp, braiding_hom_right, mapArrowLeft_left, map_comp]
        rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]
        cat_disch
    · simp only [id_obj, tensorObj_def, pushoutProduct, leibnizPushout_obj_obj, ofHasPushout_pt,
        curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map, mk_right, mk_left,
        mk_hom, associator_def, comp_left, associator_inv_left, braiding_hom_left,
        Category.assoc, HasColimit.isoOfNatIso_hom_desc, colimit.ι_desc_assoc, span_right,
        PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, inr_comp_pushoutSymmetry_hom_assoc,
        colimit.ι_desc, Cocones.precompose_obj_pt, Cocones.precompose_obj_ι, NatTrans.comp_app,
        span_left, const_obj_obj, spanExt_hom_app_left,
        BraidedCategory.braiding_naturality_left_assoc, BraidedCategory.braiding_tensor_left_hom,
        IsPushout.inr_isoPushout_hom_assoc, spanExt_hom_app_right, Iso.symm_hom,
        Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, whiskerLeft_def, leibnizPushout_obj_map,
        whiskerRight_def, leibnizPushout_map_app, mapArrowRight_left, ofHasPushout_ι,
        ofHasPushout_inl, ofHasPushout_inr, MonoidalCategory.whiskerLeft_comp, braiding_hom_right,
        mapArrowLeft_left, map_comp, IsPushout.inr_desc_assoc, IsPushout.inr_desc,
        ← comp_whiskerRight_assoc]
      cat_disch
  · exact BraidedCategory.hexagon_reverse X.right Y.right Z.right

@[simps]
noncomputable
instance [HasInitial C] [HasPushouts C]
    [CartesianMonoidalCategory C] [MonoidalClosed C]
    [BraidedCategory C]
    [∀ S : C, PreservesColimitsOfSize (tensorLeft S)]
    [∀ S : C, PreservesColimitsOfSize (tensorRight S)] : BraidedCategory (Arrow C) where
  braiding := PushoutProduct.braiding
  hexagon_forward := PushoutProduct.hexagon_forward
  hexagon_reverse := PushoutProduct.hexagon_reverse

noncomputable
instance [HasInitial C] [HasPushouts C]
    [CartesianMonoidalCategory C] [MonoidalClosed C]
    [BraidedCategory C]
    [∀ S : C, PreservesColimitsOfSize (tensorLeft S)]
    [∀ S : C, PreservesColimitsOfSize (tensorRight S)] : SymmetricCategory (Arrow C) where

end CategoryTheory.Arrow
