/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz

! This file was ported from Lean 3 source module category_theory.sites.left_exact
! leanprover-community/mathlib commit 59382264386afdbaf1727e617f5fdda511992eb9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-!
# Left exactness of sheafification
In this file we show that sheafification commutes with finite limits.
-/


open CategoryTheory Limits Opposite

universe w v u

variable {C : Type max v u} [Category.{v} C] {J : GrothendieckTopology C}

variable {D : Type w} [Category.{max v u} D]

variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]

noncomputable section

namespace CategoryTheory.GrothendieckTopology

/-- An auxiliary definition to be used in the proof of the fact that
`J.diagramFunctor D X` preserves limits. -/
@[simps]
def coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation {X : C} {K : Type max v u}
    [SmallCategory K] {F : K ⥤ Cᵒᵖ ⥤ D} {W : J.Cover X} (i : W.Arrow)
    (E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj (op W))) :
    Cone (F ⋙ (evaluation _ _).obj (op i.Y)) where
  pt := E.pt
  π :=
    { app := fun k => E.π.app k ≫ Multiequalizer.ι (W.index (F.obj k)) i
      naturality := by
        intro a b f
        dsimp
        rw [Category.id_comp, Category.assoc, ← E.w f]
        dsimp [diagramNatTrans]
        simp only [Multiequalizer.lift_ι, Category.assoc] }
#align category_theory.grothendieck_topology.cone_comp_evaluation_of_cone_comp_diagram_functor_comp_evaluation CategoryTheory.GrothendieckTopology.coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation

/-- An auxiliary definition to be used in the proof of the fact that
`J.diagramFunctor D X` preserves limits. -/
abbrev liftToDiagramLimitObj {X : C} {K : Type max v u} [SmallCategory K] [HasLimitsOfShape K D]
    {W : (J.Cover X)ᵒᵖ} (F : K ⥤ Cᵒᵖ ⥤ D)
    (E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj W)) :
    E.pt ⟶ (J.diagram (limit F) X).obj W :=
  Multiequalizer.lift ((unop W).index (limit F)) E.pt
    (fun i => (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op i.Y)) (limit.isLimit F)).lift
        (coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation.{w, v, u} i E))
    (by
      intro i
      change (_ ≫ _) ≫ _ = (_ ≫ _) ≫ _
      dsimp [evaluateCombinedCones]
      erw [Category.comp_id, Category.comp_id, Category.assoc, Category.assoc, ←
        (limit.lift F _).naturality, ← (limit.lift F _).naturality, ← Category.assoc, ←
        Category.assoc]
      congr 1
      refine' limit.hom_ext (fun j => _)
      erw [Category.assoc, Category.assoc, limit.lift_π, limit.lift_π, limit.lift_π_assoc,
        limit.lift_π_assoc, Category.assoc, Category.assoc, Multiequalizer.condition]
      rfl)
#align category_theory.grothendieck_topology.lift_to_diagram_limit_obj CategoryTheory.GrothendieckTopology.liftToDiagramLimitObj

instance preservesLimit_diagramFunctor (X : C) (K : Type max v u) [SmallCategory K] [HasLimitsOfShape K D] (F : K ⥤ Cᵒᵖ ⥤ D) :
    PreservesLimit F (J.diagramFunctor D X) :=
  preservesLimitOfEvaluation _ _ fun W =>
    preservesLimitOfPreservesLimitCone (limit.isLimit _)
      { lift := fun E => liftToDiagramLimitObj.{w, v, u} F E
        fac := by
          intro E k
          dsimp [diagramNatTrans]
          refine' Multiequalizer.hom_ext _ _ _ (fun a => _)
          simp only [Multiequalizer.lift_ι, Multiequalizer.lift_ι_assoc, Category.assoc]
          change (_ ≫ _) ≫ _ = _
          dsimp [evaluateCombinedCones]
          erw [Category.comp_id, Category.assoc, ← NatTrans.comp_app, limit.lift_π, limit.lift_π]
          rfl
        uniq := by
          intro E m hm
          refine' Multiequalizer.hom_ext _ _ _ (fun a => limit_obj_ext (fun j => _))
          delta liftToDiagramLimitObj
          erw [Multiequalizer.lift_ι, Category.assoc]
          change _ = (_ ≫ _) ≫ _
          dsimp [evaluateCombinedCones]
          erw [Category.comp_id, Category.assoc, ← NatTrans.comp_app, limit.lift_π, limit.lift_π]
          dsimp
          rw [← hm]
          dsimp [diagramNatTrans]
          simp }

instance preservesLimitsOfShape_diagramFunctor (X : C) (K : Type max v u) [SmallCategory K] [HasLimitsOfShape K D] :
    PreservesLimitsOfShape K (J.diagramFunctor D X) :=
  ⟨by apply preservesLimit_diagramFunctor.{w, v, u}⟩

instance preservesLimits_diagramFunctor (X : C) [HasLimits D] :
    PreservesLimits (J.diagramFunctor D X) := by
  constructor
  intro _ _
  apply preservesLimitsOfShape_diagramFunctor.{w, v, u}

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

variable [ConcreteCategory.{max v u} D]

variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]

/-- An auxiliary definition to be used in the proof that `J.plusFunctor D` commutes
with finite limits. -/
def liftToPlusObjLimitObj {K : Type max v u} [SmallCategory K] [FinCategory K]
    [HasLimitsOfShape K D] [PreservesLimitsOfShape K (forget D)]
    [ReflectsLimitsOfShape K (forget D)] (F : K ⥤ Cᵒᵖ ⥤ D) (X : C)
    (S : Cone (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))) :
    S.pt ⟶ (J.plusObj (limit F)).obj (op X) :=
  let e := colimitLimitIso (F ⋙ J.diagramFunctor D X)
  -- porting note: the next specific `have` had to be introduce to avoid universe problems
  have : PreservesLimit F (diagramFunctor J D X) :=
    preservesLimit_diagramFunctor.{w, v, u} X K F
  let t : J.diagram (limit F) X ≅ limit (F ⋙ J.diagramFunctor D X) :=
    (isLimitOfPreserves (J.diagramFunctor D X) (limit.isLimit F)).conePointUniqueUpToIso
      (limit.isLimit _)
  let p : (J.plusObj (limit F)).obj (op X) ≅ colimit (limit (F ⋙ J.diagramFunctor D X)) :=
    HasColimit.isoOfNatIso t
  let s :
    colimit (F ⋙ J.diagramFunctor D X).flip ≅ F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X) :=
    NatIso.ofComponents (fun k => colimitObjIsoColimitCompEvaluation _ k)
      (by
        intro i j f
        rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
        refine' colimit.hom_ext (fun w => _)
        dsimp [plusMap]
        erw [colimit.ι_map_assoc,
          colimitObjIsoColimitCompEvaluation_ι_inv (F ⋙ J.diagramFunctor D X).flip w j,
          colimitObjIsoColimitCompEvaluation_ι_inv_assoc (F ⋙ J.diagramFunctor D X).flip w i]
        rw [← (colimit.ι (F ⋙ J.diagramFunctor D X).flip w).naturality]
        rfl)
  limit.lift _ S ≫ (HasLimit.isoOfNatIso s.symm).hom ≫ e.inv ≫ p.inv
#align category_theory.grothendieck_topology.lift_to_plus_obj_limit_obj CategoryTheory.GrothendieckTopology.liftToPlusObjLimitObj

-- This lemma should not be used directly. Instead, one should use the fact that
-- `J.plus_functor D` preserves finite limits, along with the fact that
-- evaluation preserves limits.
theorem liftToPlusObjLimitObj_fac {K : Type max v u} [SmallCategory K] [FinCategory K]
    [HasLimitsOfShape K D] [PreservesLimitsOfShape K (forget D)]
    [ReflectsLimitsOfShape K (forget D)] (F : K ⥤ Cᵒᵖ ⥤ D) (X : C)
    (S : Cone (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))) (k) :
    liftToPlusObjLimitObj F X S ≫ (J.plusMap (limit.π F k)).app (op X) = S.π.app k := by
  dsimp only [lift_to_plus_obj_limit_obj]
  rw [← (limit.is_limit (F ⋙ J.plus_functor D ⋙ (evaluation Cᵒᵖ D).obj (op X))).fac S k,
    category.assoc]
  congr 1
  dsimp
  simp only [category.assoc]
  rw [← iso.eq_inv_comp, iso.inv_comp_eq, iso.inv_comp_eq]
  ext
  dsimp [plus_map]
  simp only [has_colimit.iso_of_nat_iso_ι_hom_assoc, ι_colim_map]
  dsimp [is_limit.cone_point_unique_up_to_iso, has_limit.iso_of_nat_iso, is_limit.map]
  rw [limit.lift_π]
  dsimp
  rw [ι_colimit_limit_iso_limit_π_assoc]
  simp_rw [← nat_trans.comp_app, ← category.assoc, ← nat_trans.comp_app]
  rw [limit.lift_π, category.assoc]
  congr 1
  rw [← iso.comp_inv_eq]
  erw [colimit.ι_desc]
  rfl
#align category_theory.grothendieck_topology.lift_to_plus_obj_limit_obj_fac CategoryTheory.GrothendieckTopology.liftToPlusObjLimitObj_fac

instance (K : Type max v u) [SmallCategory K] [FinCategory K] [HasLimitsOfShape K D]
    [PreservesLimitsOfShape K (forget D)] [ReflectsLimitsOfShape K (forget D)] :
    PreservesLimitsOfShape K (J.plusFunctor D) := by
  constructor; intro F; apply preserves_limit_of_evaluation; intro X
  apply preserves_limit_of_preserves_limit_cone (limit.is_limit F)
  refine' ⟨fun S => lift_to_plus_obj_limit_obj F X.unop S, _, _⟩
  · intro S k
    apply lift_to_plus_obj_limit_obj_fac
  · intro S m hm
    dsimp [lift_to_plus_obj_limit_obj]
    simp_rw [← category.assoc, iso.eq_comp_inv, ← iso.comp_inv_eq]
    ext
    simp only [limit.lift_π, category.assoc, ← hm]
    congr 1
    ext
    dsimp [plus_map, plus_obj]
    erw [colimit.ι_map, colimit.ι_desc_assoc, limit.lift_π]
    dsimp
    simp only [category.assoc]
    rw [ι_colimit_limit_iso_limit_π_assoc]
    simp only [nat_iso.of_components_inv_app, colimit_obj_iso_colimit_comp_evaluation_ι_app_hom,
      iso.symm_inv]
    dsimp [is_limit.cone_point_unique_up_to_iso]
    rw [← category.assoc, ← nat_trans.comp_app, limit.lift_π]
    rfl

instance [HasFiniteLimits D] [PreservesFiniteLimits (forget D)] [ReflectsIsomorphisms (forget D)] :
    PreservesFiniteLimits (J.plusFunctor D) := by
  apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{max v u}
  intro K _ _
  haveI : reflects_limits_of_shape K (forget D) := reflects_limits_of_shape_of_reflects_isomorphisms
  infer_instance

instance (K : Type max v u) [SmallCategory K] [FinCategory K] [HasLimitsOfShape K D]
    [PreservesLimitsOfShape K (forget D)] [ReflectsLimitsOfShape K (forget D)] :
    PreservesLimitsOfShape K (J.sheafification D) :=
  Limits.compPreservesLimitsOfShape _ _

instance [HasFiniteLimits D] [PreservesFiniteLimits (forget D)] [ReflectsIsomorphisms (forget D)] :
    PreservesFiniteLimits (J.sheafification D) :=
  Limits.compPreservesFiniteLimits _ _

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory

variable [∀ X : C, HasColimitsOfShape (J.cover X)ᵒᵖ D]

variable [ConcreteCategory.{max v u} D]

variable [∀ X : C, PreservesColimitsOfShape (J.cover X)ᵒᵖ (forget D)]

variable [PreservesLimits (forget D)]

variable [ReflectsIsomorphisms (forget D)]

variable (K : Type max v u)

variable [SmallCategory K] [FinCategory K] [HasLimitsOfShape K D]

instance : PreservesLimitsOfShape K (presheafToSheaf J D) := by
  constructor; intro F; constructor; intro S hS
  apply is_limit_of_reflects (Sheaf_to_presheaf J D)
  haveI : reflects_limits_of_shape K (forget D) := reflects_limits_of_shape_of_reflects_isomorphisms
  apply is_limit_of_preserves (J.sheafification D) hS

instance [HasFiniteLimits D] : PreservesFiniteLimits (presheafToSheaf J D) := by
  apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{max v u}
  intros ; skip; infer_instance

end CategoryTheory
