/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Plus

#align_import category_theory.sites.compatible_plus from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!

In this file, we prove that the plus functor is compatible with functors which
preserve the correct limits and colimits.

See `CategoryTheory/Sites/CompatibleSheafification` for the compatibility
of sheafification, which follows easily from the content in this file.

-/

noncomputable section

namespace CategoryTheory.GrothendieckTopology

open CategoryTheory Limits Opposite

universe w₁ w₂ v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {D : Type w₁} [Category.{max v u} D]
variable {E : Type w₂} [Category.{max v u} E]
variable (F : D ⥤ E)

variable [∀ (α β : Type max v u) (fst snd : β → α), HasLimitsOfShape (WalkingMulticospan fst snd) D]
variable [∀ (α β : Type max v u) (fst snd : β → α), HasLimitsOfShape (WalkingMulticospan fst snd) E]
variable [∀ (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]
variable (P : Cᵒᵖ ⥤ D)

/-- The diagram used to define `P⁺`, composed with `F`, is isomorphic
to the diagram used to define `P ⋙ F`. -/
def diagramCompIso (X : C) : J.diagram P X ⋙ F ≅ J.diagram (P ⋙ F) X :=
  NatIso.ofComponents
    (fun W => by
      refine' _ ≪≫ HasLimit.isoOfNatIso (W.unop.multicospanComp _ _).symm
      -- ⊢ (diagram J P X ⋙ F).obj W ≅ limit (MulticospanIndex.multicospan (Cover.index …
      refine'
        (isLimitOfPreserves F (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _))
    (by
      intro A B f
      -- ⊢ (diagram J P X ⋙ F).map f ≫ ((fun W => IsLimit.conePointUniqueUpToIso (isLim …
      -- porting note: this used to work with `ext`
      -- See https://github.com/leanprover-community/mathlib4/issues/5229
      apply Multiequalizer.hom_ext
      -- ⊢ ∀ (a : (Cover.index B.unop (P ⋙ F)).L), ((diagram J P X ⋙ F).map f ≫ ((fun W …
      dsimp
      -- ⊢ ∀ (a : (Cover.index B.unop (P ⋙ F)).L), (F.map (Multiequalizer.lift (Cover.i …
      simp only [Functor.mapCone_π_app, Multiequalizer.multifork_π_app_left, Iso.symm_hom,
        Multiequalizer.lift_ι, eqToHom_refl, Category.comp_id,
        limit.conePointUniqueUpToIso_hom_comp,
        GrothendieckTopology.Cover.multicospanComp_hom_inv_left, HasLimit.isoOfNatIso_hom_π,
        Category.assoc]
      simp only [← F.map_comp, limit.lift_π, Multifork.ofι_π_app, implies_true])
      -- 🎉 no goals
#align category_theory.grothendieck_topology.diagram_comp_iso CategoryTheory.GrothendieckTopology.diagramCompIso

@[reassoc (attr := simp)]
theorem diagramCompIso_hom_ι (X : C) (W : (J.Cover X)ᵒᵖ) (i : W.unop.Arrow) :
  (J.diagramCompIso F P X).hom.app W ≫ Multiequalizer.ι ((unop W).index (P ⋙ F)) i =
  F.map (Multiequalizer.ι _ _) := by
  delta diagramCompIso
  -- ⊢ NatTrans.app (NatIso.ofComponents fun W => IsLimit.conePointUniqueUpToIso (i …
  dsimp
  -- ⊢ ((IsLimit.conePointUniqueUpToIso (isLimitOfPreserves F (limit.isLimit (Multi …
  simp
  -- 🎉 no goals
#align category_theory.grothendieck_topology.diagram_comp_iso_hom_ι CategoryTheory.GrothendieckTopology.diagramCompIso_hom_ι

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ E]
variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]

/-- The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`. -/
def plusCompIso : J.plusObj P ⋙ F ≅ J.plusObj (P ⋙ F) :=
  NatIso.ofComponents
    (fun X => by
      refine' _ ≪≫ HasColimit.isoOfNatIso (J.diagramCompIso F P X.unop)
      -- ⊢ (plusObj J P ⋙ F).obj X ≅ colimit (diagram J P X.unop ⋙ F)
      refine'
        (isColimitOfPreserves F
              (colimit.isColimit (J.diagram P (unop X)))).coconePointUniqueUpToIso
          (colimit.isColimit _))
    (by
      intro X Y f
      -- ⊢ (plusObj J P ⋙ F).map f ≫ ((fun X => IsColimit.coconePointUniqueUpToIso (isC …
      apply (isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).hom_ext
      -- ⊢ ∀ (j : (Cover J X.unop)ᵒᵖ), NatTrans.app (F.mapCocone (colimit.cocone (diagr …
      intro W
      -- ⊢ NatTrans.app (F.mapCocone (colimit.cocone (diagram J P X.unop))).ι W ≫ (plus …
      dsimp [plusObj, plusMap]
      -- ⊢ F.map (colimit.ι (diagram J P X.unop) W) ≫ F.map (colimMap (diagramPullback  …
      simp only [Functor.map_comp, Category.assoc]
      -- ⊢ F.map (colimit.ι (diagram J P X.unop) W) ≫ F.map (colimMap (diagramPullback  …
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
      -- ⊢ F.map (Multiequalizer.lift (Cover.index (Cover.pullback W.unop f.unop) P) (m …
      slice_lhs 2 3 =>
        erw [(isColimitOfPreserves F (colimit.isColimit (J.diagram P Y.unop))).fac]
      dsimp
      -- ⊢ F.map (Multiequalizer.lift (Cover.index (Cover.pullback W.unop f.unop) P) (m …
      simp only [HasColimit.isoOfNatIso_ι_hom_assoc, GrothendieckTopology.diagramPullback_app,
        colimit.ι_pre, HasColimit.isoOfNatIso_ι_hom, ι_colimMap_assoc]
      simp only [← Category.assoc]
      -- ⊢ (F.map (Multiequalizer.lift (Cover.index (Cover.pullback W.unop f.unop) P) ( …
      dsimp
      -- ⊢ (F.map (Multiequalizer.lift (Cover.index (Cover.pullback W.unop f.unop) P) ( …
      congr 1
      -- ⊢ F.map (Multiequalizer.lift (Cover.index (Cover.pullback W.unop f.unop) P) (m …
      ext
      -- ⊢ (F.map (Multiequalizer.lift (Cover.index (Cover.pullback W.unop f.unop) P) ( …
      dsimp
      -- ⊢ (F.map (Multiequalizer.lift (Cover.index (Cover.pullback W.unop f.unop) P) ( …
      simp only [Category.assoc]
      -- ⊢ F.map (Multiequalizer.lift (Cover.index (Cover.pullback W.unop f.unop) P) (m …
      erw [Multiequalizer.lift_ι, diagramCompIso_hom_ι, diagramCompIso_hom_ι, ← F.map_comp,
        Multiequalizer.lift_ι])
#align category_theory.grothendieck_topology.plus_comp_iso CategoryTheory.GrothendieckTopology.plusCompIso

@[reassoc (attr := simp)]
theorem ι_plusCompIso_hom (X) (W) :
    F.map (colimit.ι _ W) ≫ (J.plusCompIso F P).hom.app X =
      (J.diagramCompIso F P X.unop).hom.app W ≫ colimit.ι _ W := by
  delta diagramCompIso plusCompIso
  -- ⊢ F.map (colimit.ι (diagram J P X.unop) W) ≫ NatTrans.app (NatIso.ofComponents …
  simp only [IsColimit.descCoconeMorphism_Hom, IsColimit.uniqueUpToIso_hom,
    Cocones.forget_map, Iso.trans_hom, NatIso.ofComponents_hom_app, Functor.mapIso_hom, ←
    Category.assoc]
  erw [(isColimitOfPreserves F (colimit.isColimit (J.diagram P (unop X)))).fac]
  -- ⊢ NatTrans.app (colimit.cocone (diagram J P X.unop ⋙ F)).ι W ≫ (HasColimit.iso …
  simp only [Category.assoc, HasLimit.isoOfNatIso_hom_π, Iso.symm_hom,
    Cover.multicospanComp_hom_inv_left, eqToHom_refl, Category.comp_id,
    limit.conePointUniqueUpToIso_hom_comp, Functor.mapCone_π_app,
    Multiequalizer.multifork_π_app_left, Multiequalizer.lift_ι, Functor.map_comp, eq_self_iff_true,
    Category.assoc, Iso.trans_hom, Iso.cancel_iso_hom_left, NatIso.ofComponents_hom_app,
    colimit.cocone_ι, Category.assoc, HasColimit.isoOfNatIso_ι_hom]
#align category_theory.grothendieck_topology.ι_plus_comp_iso_hom CategoryTheory.GrothendieckTopology.ι_plusCompIso_hom

@[reassoc (attr := simp)]
theorem plusCompIso_whiskerLeft {F G : D ⥤ E} (η : F ⟶ G) (P : Cᵒᵖ ⥤ D)
    [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]
    [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ G]
    [∀ (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan G] :
    whiskerLeft _ η ≫ (J.plusCompIso G P).hom =
      (J.plusCompIso F P).hom ≫ J.plusMap (whiskerLeft _ η) := by
  ext X
  -- ⊢ NatTrans.app (whiskerLeft (plusObj J P) η ≫ (plusCompIso J G P).hom) X = Nat …
  apply (isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).hom_ext
  -- ⊢ ∀ (j : (Cover J X.unop)ᵒᵖ), NatTrans.app (F.mapCocone (colimit.cocone (diagr …
  intro W
  -- ⊢ NatTrans.app (F.mapCocone (colimit.cocone (diagram J P X.unop))).ι W ≫ NatTr …
  dsimp [plusObj, plusMap]
  -- ⊢ F.map (colimit.ι (diagram J P X.unop) W) ≫ NatTrans.app η (colimit (diagram  …
  simp only [ι_plusCompIso_hom, ι_colimMap, whiskerLeft_app, ι_plusCompIso_hom_assoc,
    NatTrans.naturality_assoc, GrothendieckTopology.diagramNatTrans_app]
  simp only [← Category.assoc]
  -- ⊢ (NatTrans.app η (multiequalizer (Cover.index W.unop P)) ≫ NatTrans.app (diag …
  congr 1
  -- ⊢ NatTrans.app η (multiequalizer (Cover.index W.unop P)) ≫ NatTrans.app (diagr …
  -- porting note: this used to work with `ext`
  -- See https://github.com/leanprover-community/mathlib4/issues/5229
  apply Multiequalizer.hom_ext
  -- ⊢ ∀ (a : (Cover.index W.unop (P ⋙ G)).L), (NatTrans.app η (multiequalizer (Cov …
  intro a
  -- ⊢ (NatTrans.app η (multiequalizer (Cover.index W.unop P)) ≫ NatTrans.app (diag …
  dsimp
  -- ⊢ (NatTrans.app η (multiequalizer (Cover.index W.unop P)) ≫ NatTrans.app (diag …
  simp
  -- ⊢ NatTrans.app η (multiequalizer (Cover.index W.unop P)) ≫ G.map (Multiequaliz …
  -- Porting note: in mathlib3 `simp` managed to apply this.
  erw [η.naturality]
  -- 🎉 no goals
#align category_theory.grothendieck_topology.plus_comp_iso_whisker_left CategoryTheory.GrothendieckTopology.plusCompIso_whiskerLeft

/-- The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`, functorially in `F`. -/
@[simps! hom_app inv_app]
def plusFunctorWhiskerLeftIso (P : Cᵒᵖ ⥤ D)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (whiskeringLeft _ _ E).obj (J.plusObj P) ≅ (whiskeringLeft _ _ _).obj P ⋙ J.plusFunctor E :=
  NatIso.ofComponents (fun _ => plusCompIso _ _ _) @fun _ _ _ => plusCompIso_whiskerLeft _ _ _
#align category_theory.grothendieck_topology.plus_functor_whisker_left_iso CategoryTheory.GrothendieckTopology.plusFunctorWhiskerLeftIso

@[reassoc (attr := simp)]
theorem plusCompIso_whiskerRight {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    whiskerRight (J.plusMap η) F ≫ (J.plusCompIso F Q).hom =
      (J.plusCompIso F P).hom ≫ J.plusMap (whiskerRight η F) := by
  ext X
  -- ⊢ NatTrans.app (whiskerRight (plusMap J η) F ≫ (plusCompIso J F Q).hom) X = Na …
  apply (isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).hom_ext
  -- ⊢ ∀ (j : (Cover J X.unop)ᵒᵖ), NatTrans.app (F.mapCocone (colimit.cocone (diagr …
  intro W
  -- ⊢ NatTrans.app (F.mapCocone (colimit.cocone (diagram J P X.unop))).ι W ≫ NatTr …
  dsimp [plusObj, plusMap]
  -- ⊢ F.map (colimit.ι (diagram J P X.unop) W) ≫ F.map (colimMap (diagramNatTrans  …
  simp only [ι_colimMap, whiskerRight_app, ι_plusCompIso_hom_assoc,
    GrothendieckTopology.diagramNatTrans_app]
  simp only [← Category.assoc, ← F.map_comp]
  -- ⊢ F.map (colimit.ι (diagram J P X.unop) W ≫ colimMap (diagramNatTrans J η X.un …
  dsimp [colimMap, IsColimit.map]
  -- ⊢ F.map (colimit.ι (diagram J P X.unop) W ≫ colimit.desc (diagram J P X.unop)  …
  simp only [colimit.ι_desc]
  -- ⊢ F.map (NatTrans.app ((Cocones.precompose (diagramNatTrans J η X.unop)).obj ( …
  dsimp [Cocones.precompose]
  -- ⊢ F.map (Multiequalizer.lift (Cover.index W.unop Q) (multiequalizer (Cover.ind …
  simp only [Functor.map_comp, Category.assoc, ι_plusCompIso_hom]
  -- ⊢ F.map (Multiequalizer.lift (Cover.index W.unop Q) (multiequalizer (Cover.ind …
  simp only [← Category.assoc]
  -- ⊢ (F.map (Multiequalizer.lift (Cover.index W.unop Q) (multiequalizer (Cover.in …
  congr 1
  -- ⊢ F.map (Multiequalizer.lift (Cover.index W.unop Q) (multiequalizer (Cover.ind …
  -- porting note: this used to work with `ext`
  -- See https://github.com/leanprover-community/mathlib4/issues/5229
  apply Multiequalizer.hom_ext
  -- ⊢ ∀ (a : (Cover.index W.unop (Q ⋙ F)).L), (F.map (Multiequalizer.lift (Cover.i …
  intro a
  -- ⊢ (F.map (Multiequalizer.lift (Cover.index W.unop Q) (multiequalizer (Cover.in …
  dsimp
  -- ⊢ (F.map (Multiequalizer.lift (Cover.index W.unop Q) (multiequalizer (Cover.in …
  simp only [diagramCompIso_hom_ι_assoc, Multiequalizer.lift_ι, diagramCompIso_hom_ι,
    Category.assoc]
  simp only [← F.map_comp, Multiequalizer.lift_ι]
  -- 🎉 no goals
#align category_theory.grothendieck_topology.plus_comp_iso_whisker_right CategoryTheory.GrothendieckTopology.plusCompIso_whiskerRight

/-- The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`, functorially in `P`. -/
@[simps! hom_app inv_app]
def plusFunctorWhiskerRightIso :
    J.plusFunctor D ⋙ (whiskeringRight _ _ _).obj F ≅
      (whiskeringRight _ _ _).obj F ⋙ J.plusFunctor E :=
  NatIso.ofComponents (fun _ => J.plusCompIso _ _) @fun _ _ _ => plusCompIso_whiskerRight _ _ _
#align category_theory.grothendieck_topology.plus_functor_whisker_right_iso CategoryTheory.GrothendieckTopology.plusFunctorWhiskerRightIso

@[reassoc (attr := simp)]
theorem whiskerRight_toPlus_comp_plusCompIso_hom :
    whiskerRight (J.toPlus _) _ ≫ (J.plusCompIso F P).hom = J.toPlus _ := by
  ext
  -- ⊢ NatTrans.app (whiskerRight (toPlus J P) F ≫ (plusCompIso J F P).hom) x✝ = Na …
  dsimp [toPlus]
  -- ⊢ F.map (Cover.toMultiequalizer ⊤ P ≫ colimit.ι (diagram J P x✝.unop) (op ⊤))  …
  simp only [ι_plusCompIso_hom, Functor.map_comp, Category.assoc]
  -- ⊢ F.map (Cover.toMultiequalizer ⊤ P) ≫ NatTrans.app (diagramCompIso J F P x✝.u …
  simp only [← Category.assoc]
  -- ⊢ (F.map (Cover.toMultiequalizer ⊤ P) ≫ NatTrans.app (diagramCompIso J F P x✝. …
  congr 1
  -- ⊢ F.map (Cover.toMultiequalizer ⊤ P) ≫ NatTrans.app (diagramCompIso J F P x✝.u …
  -- porting note: this used to work with `ext`
  -- See https://github.com/leanprover-community/mathlib4/issues/5229
  apply Multiequalizer.hom_ext
  -- ⊢ ∀ (a : (Cover.index (op ⊤).unop (P ⋙ F)).L), (F.map (Cover.toMultiequalizer  …
  delta Cover.toMultiequalizer
  -- ⊢ ∀ (a : (Cover.index (op ⊤).unop (P ⋙ F)).L), (F.map (Multiequalizer.lift (Co …
  simp only [diagramCompIso_hom_ι, Category.assoc, ← F.map_comp]
  -- ⊢ ∀ (a : (Cover.index (op ⊤).unop (P ⋙ F)).L), F.map (Multiequalizer.lift (Cov …
  simp only [unop_op, limit.lift_π, Multifork.ofι_π_app, Functor.comp_obj, Functor.comp_map,
    implies_true]
#align category_theory.grothendieck_topology.whisker_right_to_plus_comp_plus_comp_iso_hom CategoryTheory.GrothendieckTopology.whiskerRight_toPlus_comp_plusCompIso_hom

@[simp]
theorem toPlus_comp_plusCompIso_inv :
    J.toPlus _ ≫ (J.plusCompIso F P).inv = whiskerRight (J.toPlus _) _ := by simp [Iso.comp_inv_eq]
                                                                             -- 🎉 no goals
#align category_theory.grothendieck_topology.to_plus_comp_plus_comp_iso_inv CategoryTheory.GrothendieckTopology.toPlus_comp_plusCompIso_inv

theorem plusCompIso_inv_eq_plusLift (hP : Presheaf.IsSheaf J (J.plusObj P ⋙ F)) :
    (J.plusCompIso F P).inv = J.plusLift (whiskerRight (J.toPlus _) _) hP := by
  apply J.plusLift_unique
  -- ⊢ toPlus J (P ⋙ F) ≫ (plusCompIso J F P).inv = whiskerRight (toPlus J P) F
  simp [Iso.comp_inv_eq]
  -- 🎉 no goals
#align category_theory.grothendieck_topology.plus_comp_iso_inv_eq_plus_lift CategoryTheory.GrothendieckTopology.plusCompIso_inv_eq_plusLift

end CategoryTheory.GrothendieckTopology
