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
def IsPushout_ofWhiskerLeft [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorLeft W)] :
    IsPushout (W ◁ (f ▷ X)) (W ◁ (A ◁ g))
      (W ◁ (pushout.inl (f ▷ X) (A ◁ g))) (W ◁ (pushout.inr (f ▷ X) (A ◁ g))) where
  w := by simp only [← MonoidalCategory.whiskerLeft_comp, pushout.condition]
  isColimit' := ⟨Limits.isColimitOfHasPushoutOfPreservesColimit (tensorLeft W) _ _⟩

-- need (F.obj A).obj ((F.obj B).obj C) ≅ (F.obj ((F.obj A).obj B)).obj C for general F
@[simps!]
noncomputable
def tensorLeft_PushoutObjObj_iso
    [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorLeft W)] :
      W ⊗ (PushoutObjObj.ofHasPushout (curriedTensor C) f g).pt ≅
      (PushoutObjObj.ofHasPushout (curriedTensor C) (W ◁ f) g).pt := by
  refine (IsPushout_ofWhiskerLeft _ _).isoPushout ≪≫ HasColimit.isoOfNatIso (spanExt ?_ ?_ ?_ ?_ ?_)
  · exact (α_ W A X).symm
  · exact (α_ W B X).symm
  · exact (α_ W A Y).symm
  · exact (associator_inv_naturality_middle W f X).symm
  · exact (associator_inv_naturality_right W A g).symm

@[simp]
def IsPushout_ofWhiskerRight [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight W)] :
    IsPushout ((f ▷ X) ▷ W) ((A ◁ g) ▷ W)
      ((pushout.inl (f ▷ X) (A ◁ g)) ▷ W) ((pushout.inr (f ▷ X) (A ◁ g)) ▷ W) where
  w := by simp only [← MonoidalCategory.comp_whiskerRight, pushout.condition]
  isColimit' := ⟨Limits.isColimitOfHasPushoutOfPreservesColimit (tensorRight W) _ _⟩

@[simps!]
noncomputable
def PushoutObjObj_whiskerRight_iso [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight W)] :
    (PushoutObjObj.ofHasPushout (curriedTensor C) f g).pt ⊗ W ≅
    (PushoutObjObj.ofHasPushout (curriedTensor C) f (g ▷ W)).pt := by
  refine (IsPushout_ofWhiskerRight _ _).isoPushout ≪≫
    HasColimit.isoOfNatIso (spanExt ?_ ?_ ?_ ?_ ?_)
  · exact α_ A X W
  · exact α_ B X W
  · exact α_ A Y W
  · exact (associator_naturality_left f X W).symm
  · exact (associator_naturality_middle A g W).symm

@[simps!]
noncomputable
def PushoutProduct.whiskerRight_iso [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight W)] :
    Arrow.mk ((f □ g) ▷ W) ≅ Arrow.mk (f □ (g ▷ W)) := by
  refine Arrow.isoMk (PushoutObjObj_whiskerRight_iso f g) (α_ B Y W) ?_
  · apply (IsPushout_ofWhiskerRight _ _).hom_ext
    all_goals simp [← MonoidalCategory.comp_whiskerRight_assoc]

@[simps!]
noncomputable
def PushoutProduct.whiskerLeft_iso [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorLeft W)] :
    Arrow.mk (W ◁ (f □ g)) ≅ Arrow.mk ((W ◁ f) □ g) := by
  refine Arrow.isoMk (tensorLeft_PushoutObjObj_iso _ _) (α_ W B Y).symm ?_
  · apply (IsPushout_ofWhiskerLeft _ _).hom_ext
    all_goals simp [← MonoidalCategory.whiskerLeft_comp_assoc]

@[simp]
noncomputable
def pt_associator_iso_hom_aux [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight W)] :
    ((PushoutObjObj.ofHasPushout (curriedTensor C) f g).pt) ⊗ W ⟶
    (PushoutObjObj.ofHasPushout (curriedTensor C) f (g □ h)).pt := by
  refine (PushoutObjObj_whiskerRight_iso _ _).hom ≫ pushout.desc ?_ ?_ ?_
  · exact (B ◁ pushout.inr _ _) ≫ pushout.inl _ _
  · exact pushout.inr _ _
  · dsimp
    rw [← whisker_exchange_assoc, pushout.condition,
      ← MonoidalCategory.whiskerLeft_comp_assoc, IsPushout.inr_desc]

@[reassoc]
lemma temp_needed : B ◁ g ▷ Z ≫ B ◁ pushout.inl (g ▷ Z) (X ◁ h) =
    B ◁ X ◁ h ≫ B ◁ pushout.inr (g ▷ Z) (X ◁ h) := by
  rw [← MonoidalCategory.whiskerLeft_comp, pushout.condition,MonoidalCategory.whiskerLeft_comp]

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

@[simp]
noncomputable
def pt_associator_iso_hom
    [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight Z)]
    [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight W)] :
    (PushoutObjObj.ofHasPushout (curriedTensor C) (f □ g) h).pt ⟶
    (PushoutObjObj.ofHasPushout (curriedTensor C) f (g □ h)).pt := by
  refine pushout.desc ?_ ?_ ?_
  · exact (α_ B Y Z).hom ≫ (B ◁ pushout.inl _ _) ≫ pushout.inl _ _
  · exact pt_associator_iso_hom_aux ..
  · apply (IsPushout_ofWhiskerRight _ _).hom_ext
    · simp [whisker_pushout_condition_assoc, ← whisker_exchange_assoc]
    · simp [← whisker_exchange_assoc]
      rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, pushout.condition,
        ← MonoidalCategory.whiskerLeft_comp_assoc, IsPushout.inl_desc]

@[simp]
noncomputable
def pt_associator_iso_inv
    [PreservesColimit (span (g ▷ Z) (X ◁ h)) (tensorLeft A)]
    [PreservesColimit (span (g ▷ Z) (X ◁ h)) (tensorLeft B)] :
    (PushoutObjObj.ofHasPushout (curriedTensor C) f (g □ h)).pt ⟶
    (PushoutObjObj.ofHasPushout (curriedTensor C) (f □ g) h).pt := by
  apply pushout.desc ?_ ?_ ?_
  · refine (tensorLeft_PushoutObjObj_iso _ _).hom ≫ pushout.desc ?_ ?_ ?_
    · exact 𝟙 _ ≫ pushout.inl _ _
    · exact (pushout.inl _ _ ▷ W) ≫ pushout.inr _ _
    · dsimp [Functor.PushoutObjObj.ι]
      rw [Category.id_comp, whisker_exchange_assoc, ← pushout.condition,
        ← MonoidalCategory.comp_whiskerRight_assoc, IsPushout.inl_desc]
  · exact (α_ _ _ _).inv ≫ (pushout.inr _ _) ▷ _ ≫ pushout.inr _ _
  · dsimp [Functor.PushoutObjObj.ι]
    apply (IsPushout_ofWhiskerLeft _ _).hom_ext
    · rw [whisker_exchange_assoc]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc]
      simp only [whiskerRight_tensor, Category.id_comp, Category.assoc,
        HasColimit.isoOfNatIso_hom_desc, IsPushout.inl_isoPushout_hom_assoc, colimit.ι_desc,
        Cocones.precompose_obj_pt, PushoutCocone.mk_pt, Cocones.precompose_obj_ι,
        NatTrans.comp_app, span_left, Functor.const_obj_obj, spanExt_hom_app_left, Iso.symm_hom,
        PushoutCocone.mk_ι_app, Iso.hom_inv_id_assoc, IsPushout.inl_desc]
      rw [← congrFun (congrArg MonoidalCategoryStruct.whiskerRight ((IsPushout.of_hasPushout (f ▷ X) (A ◁ g)).inr_desc (B ◁ g) (f ▷ Y) (whisker_exchange f g).symm)) Z,
        MonoidalCategory.comp_whiskerRight, Category.assoc, pushout.condition, ← whisker_exchange_assoc]
      simp only [tensor_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc]
    · simp only [Category.id_comp, Category.assoc, HasColimit.isoOfNatIso_hom_desc,
        whisker_exchange_assoc, whiskerRight_tensor, IsPushout.inr_isoPushout_hom_assoc,
        colimit.ι_desc, Cocones.precompose_obj_pt, PushoutCocone.mk_pt, Cocones.precompose_obj_ι,
        NatTrans.comp_app, span_right, Functor.const_obj_obj, spanExt_hom_app_right, Iso.symm_hom,
        PushoutCocone.mk_ι_app, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc, pushout.condition,
        comp_whiskerRight, whisker_assoc, Iso.inv_hom_id_assoc, ←
        MonoidalCategory.whiskerLeft_comp_assoc, IsPushout.inr_desc]

@[simp]
noncomputable
def pt_associator_iso
      [PreservesColimit (span (g ▷ Z) (X ◁ h)) (tensorLeft A)]
      [PreservesColimit (span (g ▷ Z) (X ◁ h)) (tensorLeft B)]
      [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight Z)]
      [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight W)] :
    (PushoutObjObj.ofHasPushout (curriedTensor C) (f □ g) h).pt ≅
    (PushoutObjObj.ofHasPushout (curriedTensor C) f (g □ h)).pt where
  hom := pt_associator_iso_hom f g h
  inv := pt_associator_iso_inv f g h
  hom_inv_id := by
    apply pushout.hom_ext
    · simp
    · exact (IsPushout_ofWhiskerRight _ _).hom_ext (by simp) (by simp)
  inv_hom_id := by
    apply pushout.hom_ext
    · exact (IsPushout_ofWhiskerLeft _ _).hom_ext (by simp) (by simp)
    · simp

@[simp]
noncomputable
def pt_comm_iso [BraidedCategory C] : (PushoutObjObj.ofHasPushout (curriedTensor C) f g).pt ≅
    (PushoutObjObj.ofHasPushout (curriedTensor C) g f).pt :=
  pushoutSymmetry (f ▷ X) (A ◁ g) ≪≫
    (HasColimit.isoOfNatIso (spanExt (β_ _ _) (β_ _ _) (β_ _ _)
    (BraidedCategory.braiding_naturality_right A g).symm
    (BraidedCategory.braiding_naturality_left f X).symm))

noncomputable
def comm_iso [BraidedCategory C] : Arrow.mk (f □ g) ≅ Arrow.mk (g □ f) :=
  Arrow.isoMk (pt_comm_iso f g) (β_ _ _) (by cat_disch)

@[simps!]
noncomputable
def associator
    [PreservesColimit (span (g ▷ Z) (X ◁ h)) (tensorLeft A)]
    [PreservesColimit (span (g ▷ Z) (X ◁ h)) (tensorLeft B)]
    [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight Z)]
    [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight W)] :
    Arrow.mk ((f □ g) □ h) ≅ Arrow.mk (f □ g □ h) := by
  refine Arrow.isoMk (pt_associator_iso _ _ _) (α_ _ _ _) ?_
  · apply pushout.hom_ext
    · simp [← MonoidalCategory.whiskerLeft_comp]
    · apply (IsPushout_ofWhiskerRight _ _).hom_ext
      · simp [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.comp_whiskerRight_assoc]
      · simp [← MonoidalCategory.comp_whiskerRight_assoc]

noncomputable
instance [HasPushouts C] [HasInitial C] [CartesianMonoidalCategory C]
    [MonoidalClosed C] [BraidedCategory C]
    [∀ S : C, PreservesColimitsOfSize (tensorLeft S)]
    [∀ S : C, PreservesColimitsOfSize (tensorRight S)] : MonoidalCategory (Arrow C) where
  tensorObj X Y := ((leftBifunctor (curriedTensor C)).obj X).obj Y
  whiskerLeft X _ _ f := ((leftBifunctor (curriedTensor C)).obj X).map f
  whiskerRight f X := ((leftBifunctor (curriedTensor C)).map f).app X
  tensorUnit := (initial.to (𝟙_ C))
  associator X Y Z := Arrow.associator X.hom Y.hom Z.hom
  associator_naturality := by
    intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
    dsimp only
    apply Arrow.hom_ext
    · apply pushout.hom_ext
      · simp
        sorry
      · apply (IsPushout_ofWhiskerRight _ _).hom_ext
        · sorry
        · sorry
    · simp
  pentagon := by
    intro W X Y Z
    apply Arrow.hom_ext
    · apply pushout.hom_ext
      ·
        sorry
      · sorry
    · simp
  leftUnitor X := by
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
  leftUnitor_naturality := sorry
  rightUnitor X := by
    refine Arrow.isoMk ?_ (ρ_ X.right) ?_
    · sorry
    · sorry
end CategoryTheory.Arrow
