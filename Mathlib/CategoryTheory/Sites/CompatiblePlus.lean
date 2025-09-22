/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Plus

/-!

In this file, we prove that the plus functor is compatible with functors which
preserve the correct limits and colimits.

See `CategoryTheory/Sites/CompatibleSheafification` for the compatibility
of sheafification, which follows easily from the content in this file.

-/

noncomputable section

namespace CategoryTheory.GrothendieckTopology

open CategoryTheory Limits Opposite Functor

universe w₁ w₂ v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {D : Type w₁} [Category.{max v u} D]
variable {E : Type w₂} [Category.{max v u} E]
variable (F : D ⥤ E)
variable [∀ (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) D]
variable [∀ (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) E]
variable [∀ (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]
variable (P : Cᵒᵖ ⥤ D)

/-- The diagram used to define `P⁺`, composed with `F`, is isomorphic
to the diagram used to define `P ⋙ F`. -/
def diagramCompIso (X : C) : J.diagram P X ⋙ F ≅ J.diagram (P ⋙ F) X :=
  NatIso.ofComponents
    (fun W => by
      refine ?_ ≪≫ HasLimit.isoOfNatIso (W.unop.multicospanComp _ _).symm
      refine
        (isLimitOfPreserves F (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _))
    (by
      intro A B f
      dsimp
      ext g
      simp [← F.map_comp])

@[reassoc (attr := simp)]
theorem diagramCompIso_hom_ι (X : C) (W : (J.Cover X)ᵒᵖ) (i : W.unop.Arrow) :
    (J.diagramCompIso F P X).hom.app W ≫ Multiequalizer.ι ((unop W).index (P ⋙ F)) i =
    F.map (Multiequalizer.ι _ _) := by
  delta diagramCompIso
  simp

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ E]
variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]

/-- The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`. -/
def plusCompIso : J.plusObj P ⋙ F ≅ J.plusObj (P ⋙ F) :=
  NatIso.ofComponents
    (fun X => by
      refine ?_ ≪≫ HasColimit.isoOfNatIso (J.diagramCompIso F P X.unop)
      refine
        (isColimitOfPreserves F
              (colimit.isColimit (J.diagram P (unop X)))).coconePointUniqueUpToIso
          (colimit.isColimit _))
    (by
      intro X Y f
      apply (isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).hom_ext
      intro W
      dsimp [plusObj, plusMap]
      simp only [Functor.map_comp, Category.assoc]
      slice_rhs 1 2 =>
        erw [(isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).fac]
      slice_lhs 1 3 =>
        simp only [← F.map_comp]
        dsimp [colimMap, IsColimit.map, colimit.pre]
        simp only [colimit.ι_desc_assoc, colimit.ι_desc]
        dsimp [Cocones.precompose]
        simp only [Category.assoc, colimit.ι_desc]
        dsimp [Cocone.whisker]
        rw [F.map_comp]
      simp only [Category.assoc]
      slice_lhs 2 3 =>
        erw [(isColimitOfPreserves F (colimit.isColimit (J.diagram P Y.unop))).fac]
      dsimp
      simp only [HasColimit.isoOfNatIso_ι_hom_assoc, GrothendieckTopology.diagramPullback_app,
        colimit.ι_pre, HasColimit.isoOfNatIso_ι_hom, ι_colimMap_assoc]
      simp only [← Category.assoc]
      dsimp
      congr 1
      ext
      dsimp
      simp only [Category.assoc]
      rw [Multiequalizer.lift_ι, diagramCompIso_hom_ι, diagramCompIso_hom_ι, ← F.map_comp,
        Multiequalizer.lift_ι])

@[reassoc (attr := simp)]
theorem ι_plusCompIso_hom (X) (W) :
    F.map (colimit.ι _ W) ≫ (J.plusCompIso F P).hom.app X =
      (J.diagramCompIso F P X.unop).hom.app W ≫ colimit.ι _ W := by
  delta diagramCompIso plusCompIso
  simp only [Iso.trans_hom, NatIso.ofComponents_hom_app, ←
    Category.assoc]
  erw [(isColimitOfPreserves F (colimit.isColimit (J.diagram P (unop X)))).fac]
  simp

@[reassoc (attr := simp)]
theorem plusCompIso_whiskerLeft {F G : D ⥤ E} (η : F ⟶ G) (P : Cᵒᵖ ⥤ D)
    [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]
    [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ G]
    [∀ (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan G] :
    whiskerLeft _ η ≫ (J.plusCompIso G P).hom =
      (J.plusCompIso F P).hom ≫ J.plusMap (whiskerLeft _ η) := by
  ext X
  apply (isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).hom_ext
  intro W
  dsimp [plusObj, plusMap]
  simp only [ι_plusCompIso_hom, ι_colimMap, whiskerLeft_app, ι_plusCompIso_hom_assoc,
    NatTrans.naturality_assoc, GrothendieckTopology.diagramNatTrans_app]
  simp only [← Category.assoc]
  congr 1
  cat_disch

/-- The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`, functorially in `F`. -/
@[simps! hom_app inv_app]
def plusFunctorWhiskerLeftIso (P : Cᵒᵖ ⥤ D)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (whiskeringLeft _ _ E).obj (J.plusObj P) ≅ (whiskeringLeft _ _ _).obj P ⋙ J.plusFunctor E :=
  NatIso.ofComponents (fun _ => plusCompIso _ _ _) @fun _ _ _ => plusCompIso_whiskerLeft _ _ _

@[reassoc (attr := simp)]
theorem plusCompIso_whiskerRight {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    whiskerRight (J.plusMap η) F ≫ (J.plusCompIso F Q).hom =
      (J.plusCompIso F P).hom ≫ J.plusMap (whiskerRight η F) := by
  ext X
  apply (isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).hom_ext
  intro W
  dsimp [plusObj, plusMap]
  simp only [ι_colimMap, whiskerRight_app, ι_plusCompIso_hom_assoc,
    GrothendieckTopology.diagramNatTrans_app]
  simp only [← Category.assoc, ← F.map_comp]
  dsimp [colimMap, IsColimit.map]
  simp only [colimit.ι_desc]
  dsimp [Cocones.precompose]
  simp only [Functor.map_comp, Category.assoc, ι_plusCompIso_hom]
  simp only [← Category.assoc]
  congr 1
  dsimp only [diagram] -- Need to unfold `diagram` before `ext` applies.
  ext a
  dsimp
  simp only [diagramCompIso_hom_ι_assoc, Multiequalizer.lift_ι, diagramCompIso_hom_ι,
    Category.assoc]
  simp only [← F.map_comp, Multiequalizer.lift_ι]

/-- The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`, functorially in `P`. -/
@[simps! hom_app inv_app]
def plusFunctorWhiskerRightIso :
    J.plusFunctor D ⋙ (whiskeringRight _ _ _).obj F ≅
      (whiskeringRight _ _ _).obj F ⋙ J.plusFunctor E :=
  NatIso.ofComponents (fun _ => J.plusCompIso _ _) @fun _ _ _ => plusCompIso_whiskerRight _ _ _

@[reassoc (attr := simp)]
theorem whiskerRight_toPlus_comp_plusCompIso_hom :
    whiskerRight (J.toPlus _) _ ≫ (J.plusCompIso F P).hom = J.toPlus _ := by
  ext
  dsimp [toPlus]
  simp only [ι_plusCompIso_hom, Functor.map_comp, Category.assoc]
  simp only [← Category.assoc]
  congr 1
  dsimp only [diagram] -- Need to unfold `diagram` before `ext` applies.
  ext a
  rw [Category.assoc, diagramCompIso_hom_ι, ← F.map_comp]
  simp only [unop_op, limit.lift_π, Multifork.ofι_π_app, Functor.comp_obj, Functor.comp_map]

@[simp]
theorem toPlus_comp_plusCompIso_inv :
    J.toPlus _ ≫ (J.plusCompIso F P).inv = whiskerRight (J.toPlus _) _ := by simp [Iso.comp_inv_eq]

theorem plusCompIso_inv_eq_plusLift (hP : Presheaf.IsSheaf J (J.plusObj P ⋙ F)) :
    (J.plusCompIso F P).inv = J.plusLift (whiskerRight (J.toPlus _) _) hP := by
  apply J.plusLift_unique
  simp

end CategoryTheory.GrothendieckTopology
