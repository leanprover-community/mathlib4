/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

#align_import category_theory.sites.left_exact from "leanprover-community/mathlib"@"59382264386afdbaf1727e617f5fdda511992eb9"

/-!
# Left exactness of sheafification
In this file we show that sheafification commutes with finite limits.
-/


open CategoryTheory Limits Opposite

universe w v u

-- porting note: was `C : Type max v u` which made most instances non automatically applicable
-- it seems to me it is better to declare `C : Type u`: it works better, and it is more general
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

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
        -- ⊢ ((Functor.const K).obj E.pt).map f ≫ (fun k => NatTrans.app E.π k ≫ Multiequ …
        dsimp
        -- ⊢ 𝟙 E.pt ≫ NatTrans.app E.π b ≫ Multiequalizer.ι (Cover.index W (F.obj b)) i = …
        rw [Category.id_comp, Category.assoc, ← E.w f]
        -- ⊢ (NatTrans.app E.π a ≫ (F ⋙ diagramFunctor J D X ⋙ (evaluation (Cover J X)ᵒᵖ  …
        dsimp [diagramNatTrans]
        -- ⊢ (NatTrans.app E.π a ≫ Multiequalizer.lift (Cover.index W (F.obj b)) (multieq …
        simp only [Multiequalizer.lift_ι, Category.assoc] }
        -- 🎉 no goals
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
      -- ⊢ (fun i => IsLimit.lift (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op i.Y)) …
      change (_ ≫ _) ≫ _ = (_ ≫ _) ≫ _
      -- ⊢ ((IsLimit.liftConeMorphism (IsLimit.ofIsoLimit (limit.isLimit (F ⋙ (evaluati …
      dsimp [evaluateCombinedCones]
      -- ⊢ ((limit.lift (F ⋙ (evaluation Cᵒᵖ D).obj (op (MulticospanIndex.fstTo (Cover. …
      erw [Category.comp_id, Category.comp_id, Category.assoc, Category.assoc, ←
        (limit.lift F _).naturality, ← (limit.lift F _).naturality, ← Category.assoc, ←
        Category.assoc]
      congr 1
      -- ⊢ limit.lift (F ⋙ (evaluation Cᵒᵖ D).obj (op (MulticospanIndex.fstTo (Cover.in …
      refine' limit.hom_ext (fun j => _)
      -- ⊢ (limit.lift (F ⋙ (evaluation Cᵒᵖ D).obj (op (MulticospanIndex.fstTo (Cover.i …
      erw [Category.assoc, Category.assoc, limit.lift_π, limit.lift_π, limit.lift_π_assoc,
        limit.lift_π_assoc, Category.assoc, Category.assoc, Multiequalizer.condition]
      rfl)
      -- 🎉 no goals
#align category_theory.grothendieck_topology.lift_to_diagram_limit_obj CategoryTheory.GrothendieckTopology.liftToDiagramLimitObj

instance preservesLimit_diagramFunctor
    (X : C) (K : Type max v u) [SmallCategory K] [HasLimitsOfShape K D] (F : K ⥤ Cᵒᵖ ⥤ D) :
    PreservesLimit F (J.diagramFunctor D X) :=
  preservesLimitOfEvaluation _ _ fun W =>
    preservesLimitOfPreservesLimitCone (limit.isLimit _)
      { lift := fun E => liftToDiagramLimitObj.{w, v, u} F E
        fac := by
          intro E k
          -- ⊢ (fun E => liftToDiagramLimitObj F E) E ≫ NatTrans.app ((diagramFunctor J D X …
          dsimp [diagramNatTrans]
          -- ⊢ liftToDiagramLimitObj F E ≫ Multiequalizer.lift (Cover.index W.unop (F.obj k …
          refine' Multiequalizer.hom_ext _ _ _ (fun a => _)
          -- ⊢ (liftToDiagramLimitObj F E ≫ Multiequalizer.lift (Cover.index W.unop (F.obj  …
          simp only [Multiequalizer.lift_ι, Multiequalizer.lift_ι_assoc, Category.assoc]
          -- ⊢ IsLimit.lift (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op a.Y)) (limit.is …
          change (_ ≫ _) ≫ _ = _
          -- ⊢ ((IsLimit.liftConeMorphism (IsLimit.ofIsoLimit (limit.isLimit (F ⋙ (evaluati …
          dsimp [evaluateCombinedCones]
          -- ⊢ ((limit.lift (F ⋙ (evaluation Cᵒᵖ D).obj (op a.Y)) (coneCompEvaluationOfCone …
          erw [Category.comp_id, Category.assoc, ← NatTrans.comp_app, limit.lift_π, limit.lift_π]
          -- ⊢ NatTrans.app (coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation a E). …
          rfl
          -- 🎉 no goals
        uniq := by
          intro E m hm
          -- ⊢ m = (fun E => liftToDiagramLimitObj F E) E
          refine' Multiequalizer.hom_ext _ _ _ (fun a => limit_obj_ext (fun j => _))
          -- ⊢ (m ≫ Multiequalizer.ι (Cover.index W.unop (limit.cone F).pt) a) ≫ NatTrans.a …
          delta liftToDiagramLimitObj
          -- ⊢ (m ≫ Multiequalizer.ι (Cover.index W.unop (limit.cone F).pt) a) ≫ NatTrans.a …
          erw [Multiequalizer.lift_ι, Category.assoc]
          -- ⊢ m ≫ Multiequalizer.ι (Cover.index W.unop (limit.cone F).pt) a ≫ NatTrans.app …
          change _ = (_ ≫ _) ≫ _
          -- ⊢ m ≫ Multiequalizer.ι (Cover.index W.unop (limit.cone F).pt) a ≫ NatTrans.app …
          dsimp [evaluateCombinedCones]
          -- ⊢ m ≫ Multiequalizer.ι (Cover.index W.unop (limit F)) a ≫ NatTrans.app (limit. …
          erw [Category.comp_id, Category.assoc, ← NatTrans.comp_app, limit.lift_π, limit.lift_π]
          -- ⊢ m ≫ Multiequalizer.ι (Cover.index W.unop (limit F)) a ≫ NatTrans.app (limit. …
          dsimp
          -- ⊢ m ≫ Multiequalizer.ι (Cover.index W.unop (limit F)) a ≫ NatTrans.app (limit. …
          rw [← hm]
          -- ⊢ m ≫ Multiequalizer.ι (Cover.index W.unop (limit F)) a ≫ NatTrans.app (limit. …
          dsimp [diagramNatTrans]
          -- ⊢ m ≫ Multiequalizer.ι (Cover.index W.unop (limit F)) a ≫ NatTrans.app (limit. …
          simp }
          -- 🎉 no goals

instance preservesLimitsOfShape_diagramFunctor
    (X : C) (K : Type max v u) [SmallCategory K] [HasLimitsOfShape K D] :
    PreservesLimitsOfShape K (J.diagramFunctor D X) :=
  ⟨by apply preservesLimit_diagramFunctor.{w, v, u}⟩
      -- 🎉 no goals

instance preservesLimits_diagramFunctor (X : C) [HasLimits D] :
    PreservesLimits (J.diagramFunctor D X) := by
  constructor
  -- ⊢ autoParam ({J_1 : Type (max u v)} → [inst : Category.{max u v, max u v} J_1] …
  intro _ _
  -- ⊢ PreservesLimitsOfShape J✝ (diagramFunctor J D X)
  apply preservesLimitsOfShape_diagramFunctor.{w, v, u}
  -- 🎉 no goals

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
        -- ⊢ (colimit (Functor.flip (F ⋙ diagramFunctor J D X))).map f ≫ ((fun k => colim …
        rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
        -- ⊢ ((fun k => colimitObjIsoColimitCompEvaluation (Functor.flip (F ⋙ diagramFunc …
        refine' colimit.hom_ext (fun w => _)
        -- ⊢ colimit.ι (diagram J (F.obj i) (op X).unop) w ≫ ((fun k => colimitObjIsoColi …
        dsimp [plusMap]
        -- ⊢ colimit.ι (diagram J (F.obj i) X) w ≫ (colimitObjIsoColimitCompEvaluation (F …
        erw [colimit.ι_map_assoc,
          colimitObjIsoColimitCompEvaluation_ι_inv (F ⋙ J.diagramFunctor D X).flip w j,
          colimitObjIsoColimitCompEvaluation_ι_inv_assoc (F ⋙ J.diagramFunctor D X).flip w i]
        rw [← (colimit.ι (F ⋙ J.diagramFunctor D X).flip w).naturality]
        -- ⊢ ((Functor.flip (F ⋙ diagramFunctor J D X)).obj w).map f ≫ NatTrans.app (coli …
        rfl)
        -- 🎉 no goals
  limit.lift _ S ≫ (HasLimit.isoOfNatIso s.symm).hom ≫ e.inv ≫ p.inv
#align category_theory.grothendieck_topology.lift_to_plus_obj_limit_obj CategoryTheory.GrothendieckTopology.liftToPlusObjLimitObj

-- This lemma should not be used directly. Instead, one should use the fact that
-- `J.plusFunctor D` preserves finite limits, along with the fact that
-- evaluation preserves limits.
theorem liftToPlusObjLimitObj_fac {K : Type max v u} [SmallCategory K] [FinCategory K]
    [HasLimitsOfShape K D] [PreservesLimitsOfShape K (forget D)]
    [ReflectsLimitsOfShape K (forget D)] (F : K ⥤ Cᵒᵖ ⥤ D) (X : C)
    (S : Cone (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))) (k) :
    liftToPlusObjLimitObj.{w, v, u} F X S ≫ (J.plusMap (limit.π F k)).app (op X) = S.π.app k := by
  dsimp only [liftToPlusObjLimitObj]
  -- ⊢ (limit.lift (F ⋙ plusFunctor J D ⋙ (evaluation Cᵒᵖ D).obj (op X)) S ≫ (HasLi …
  rw [← (limit.isLimit (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))).fac S k,
    Category.assoc]
  congr 1
  -- ⊢ ((HasLimit.isoOfNatIso (NatIso.ofComponents fun k => colimitObjIsoColimitCom …
  dsimp
  -- ⊢ ((HasLimit.isoOfNatIso (NatIso.ofComponents fun k => colimitObjIsoColimitCom …
  rw [Category.assoc, Category.assoc, ← Iso.eq_inv_comp, Iso.inv_comp_eq, Iso.inv_comp_eq]
  -- ⊢ NatTrans.app (plusMap J (limit.π F k)) (op X) = (HasColimit.isoOfNatIso (IsL …
  refine' colimit.hom_ext (fun j => _)
  -- ⊢ colimit.ι (diagram J (limit F) (op X).unop) j ≫ NatTrans.app (plusMap J (lim …
  dsimp [plusMap]
  -- ⊢ colimit.ι (diagram J (limit F) X) j ≫ colimMap (diagramNatTrans J (limit.π F …
  simp only [HasColimit.isoOfNatIso_ι_hom_assoc, ι_colimMap]
  -- ⊢ NatTrans.app (diagramNatTrans J (limit.π F k) X) j ≫ colimit.ι (diagram J (F …
  dsimp [IsLimit.conePointUniqueUpToIso, HasLimit.isoOfNatIso, IsLimit.map]
  -- ⊢ Multiequalizer.lift (Cover.index j.unop (F.obj k)) (multiequalizer (Cover.in …
  rw [limit.lift_π]
  -- ⊢ Multiequalizer.lift (Cover.index j.unop (F.obj k)) (multiequalizer (Cover.in …
  dsimp
  -- ⊢ Multiequalizer.lift (Cover.index j.unop (F.obj k)) (multiequalizer (Cover.in …
  rw [ι_colimitLimitIso_limit_π_assoc]
  -- ⊢ Multiequalizer.lift (Cover.index j.unop (F.obj k)) (multiequalizer (Cover.in …
  simp_rw [← Category.assoc, ← NatTrans.comp_app]
  -- ⊢ Multiequalizer.lift (Cover.index j.unop (F.obj k)) (multiequalizer (Cover.in …
  rw [limit.lift_π, Category.assoc]
  -- ⊢ Multiequalizer.lift (Cover.index j.unop (F.obj k)) (multiequalizer (Cover.in …
  congr 1
  -- ⊢ colimit.ι (diagram J (F.obj k) X) j = NatTrans.app (colimit.ι (Functor.flip  …
  rw [← Iso.comp_inv_eq]
  -- ⊢ colimit.ι (diagram J (F.obj k) X) j ≫ (colimitObjIsoColimitCompEvaluation (F …
  erw [colimit.ι_desc]
  -- ⊢ NatTrans.app (((evaluation K D).obj k).mapCocone (colimit.cocone (Functor.fl …
  rfl
  -- 🎉 no goals
#align category_theory.grothendieck_topology.lift_to_plus_obj_limit_obj_fac CategoryTheory.GrothendieckTopology.liftToPlusObjLimitObj_fac

instance preservesLimitsOfShape_plusFunctor
    (K : Type max v u) [SmallCategory K] [FinCategory K] [HasLimitsOfShape K D]
    [PreservesLimitsOfShape K (forget D)] [ReflectsLimitsOfShape K (forget D)] :
    PreservesLimitsOfShape K (J.plusFunctor D) := by
  constructor; intro F; apply preservesLimitOfEvaluation; intro X
  -- ⊢ autoParam ({K_1 : K ⥤ Cᵒᵖ ⥤ D} → PreservesLimit K_1 (plusFunctor J D)) _auto✝
               -- ⊢ PreservesLimit F (plusFunctor J D)
                        -- ⊢ (k : Cᵒᵖ) → PreservesLimit F (plusFunctor J D ⋙ (evaluation Cᵒᵖ D).obj k)
                                                          -- ⊢ PreservesLimit F (plusFunctor J D ⋙ (evaluation Cᵒᵖ D).obj X)
  apply preservesLimitOfPreservesLimitCone (limit.isLimit F)
  -- ⊢ IsLimit ((plusFunctor J D ⋙ (evaluation Cᵒᵖ D).obj X).mapCone (limit.cone F))
  refine' ⟨fun S => liftToPlusObjLimitObj.{w, v, u} F X.unop S, _, _⟩
  -- ⊢ ∀ (s : Cone (F ⋙ plusFunctor J D ⋙ (evaluation Cᵒᵖ D).obj X)) (j : K), (fun  …
  · intro S k
    -- ⊢ (fun S => liftToPlusObjLimitObj F X.unop S) S ≫ NatTrans.app ((plusFunctor J …
    apply liftToPlusObjLimitObj_fac
    -- 🎉 no goals
  · intro S m hm
    -- ⊢ m = (fun S => liftToPlusObjLimitObj F X.unop S) S
    dsimp [liftToPlusObjLimitObj]
    -- ⊢ m = limit.lift (F ⋙ plusFunctor J D ⋙ (evaluation Cᵒᵖ D).obj X) S ≫ (HasLimi …
    simp_rw [← Category.assoc, Iso.eq_comp_inv, ← Iso.comp_inv_eq]
    -- ⊢ ((m ≫ (HasColimit.isoOfNatIso (IsLimit.conePointUniqueUpToIso (isLimitOfPres …
    refine' limit.hom_ext (fun k => _)
    -- ⊢ (((m ≫ (HasColimit.isoOfNatIso (IsLimit.conePointUniqueUpToIso (isLimitOfPre …
    simp only [limit.lift_π, Category.assoc, ← hm]
    -- ⊢ m ≫ (HasColimit.isoOfNatIso (IsLimit.conePointUniqueUpToIso (isLimitOfPreser …
    congr 1
    -- ⊢ (HasColimit.isoOfNatIso (IsLimit.conePointUniqueUpToIso (isLimitOfPreserves  …
    refine' colimit.hom_ext (fun k => _)
    -- ⊢ colimit.ι (diagram J (limit.cone F).pt X.unop) k ≫ (HasColimit.isoOfNatIso ( …
    dsimp [plusMap, plusObj]
    -- ⊢ colimit.ι (diagram J (limit F) X.unop) k ≫ (HasColimit.isoOfNatIso (IsLimit. …
    erw [colimit.ι_map, colimit.ι_desc_assoc, limit.lift_π]
    -- ⊢ NatTrans.app ((Cocones.precompose (IsLimit.conePointUniqueUpToIso (isLimitOf …
    conv_lhs => dsimp
    -- ⊢ (NatTrans.app (IsLimit.conePointUniqueUpToIso (isLimitOfPreserves (diagramFu …
    simp only [Category.assoc]
    -- ⊢ NatTrans.app (IsLimit.conePointUniqueUpToIso (isLimitOfPreserves (diagramFun …
    rw [ι_colimitLimitIso_limit_π_assoc]
    -- ⊢ NatTrans.app (IsLimit.conePointUniqueUpToIso (isLimitOfPreserves (diagramFun …
    simp only [NatIso.ofComponents_inv_app, colimitObjIsoColimitCompEvaluation_ι_app_hom,
      Iso.symm_inv]
    conv_lhs =>
      dsimp [IsLimit.conePointUniqueUpToIso]
    rw [← Category.assoc, ← NatTrans.comp_app, limit.lift_π]
    -- ⊢ NatTrans.app (NatTrans.app ((diagramFunctor J D X.unop).mapCone (limit.cone  …
    rfl
    -- 🎉 no goals

instance preserveFiniteLimits_plusFunctor
    [HasFiniteLimits D] [PreservesFiniteLimits (forget D)] [ReflectsIsomorphisms (forget D)] :
    PreservesFiniteLimits (J.plusFunctor D) := by
  apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{max v u}
  -- ⊢ (J_1 : Type (max v u)) → {𝒥 : SmallCategory J_1} → FinCategory J_1 → Preserv …
  intro K _ _
  -- ⊢ PreservesLimitsOfShape K (plusFunctor J D)
  have : ReflectsLimitsOfShape K (forget D) := reflectsLimitsOfShapeOfReflectsIsomorphisms
  -- ⊢ PreservesLimitsOfShape K (plusFunctor J D)
  apply preservesLimitsOfShape_plusFunctor.{w, v, u}
  -- 🎉 no goals

instance preservesLimitsOfShape_sheafification
    (K : Type max v u) [SmallCategory K] [FinCategory K] [HasLimitsOfShape K D]
    [PreservesLimitsOfShape K (forget D)] [ReflectsLimitsOfShape K (forget D)] :
    PreservesLimitsOfShape K (J.sheafification D) :=
  Limits.compPreservesLimitsOfShape _ _

instance preservesFiniteLimits_sheafification
    [HasFiniteLimits D] [PreservesFiniteLimits (forget D)] [ReflectsIsomorphisms (forget D)] :
    PreservesFiniteLimits (J.sheafification D) :=
  Limits.compPreservesFiniteLimits _ _

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

variable [ConcreteCategory.{max v u} D]

variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]

variable [PreservesLimits (forget D)]

variable [ReflectsIsomorphisms (forget D)]

variable (K : Type max v u)

variable [SmallCategory K] [FinCategory K] [HasLimitsOfShape K D]

instance preservesLimitsOfShape_presheafToSheaf :
    PreservesLimitsOfShape K (presheafToSheaf J D) := by
  constructor; intro F; constructor; intro S hS
  -- ⊢ autoParam ({K_1 : K ⥤ Cᵒᵖ ⥤ D} → PreservesLimit K_1 (presheafToSheaf J D)) _ …
               -- ⊢ PreservesLimit F (presheafToSheaf J D)
                        -- ⊢ {c : Cone F} → IsLimit c → IsLimit ((presheafToSheaf J D).mapCone c)
                                     -- ⊢ IsLimit ((presheafToSheaf J D).mapCone S)
  apply isLimitOfReflects (sheafToPresheaf J D)
  -- ⊢ IsLimit ((sheafToPresheaf J D).mapCone ((presheafToSheaf J D).mapCone S))
  have : ReflectsLimitsOfShape K (forget D) := reflectsLimitsOfShapeOfReflectsIsomorphisms
  -- ⊢ IsLimit ((sheafToPresheaf J D).mapCone ((presheafToSheaf J D).mapCone S))
  -- porting note: the mathlib proof was by `apply is_limit_of_preserves (J.sheafification D) hS`
  have : PreservesLimitsOfShape K (presheafToSheaf J D ⋙ sheafToPresheaf J D) :=
    preservesLimitsOfShapeOfNatIso (J.sheafificationIsoPresheafToSheafCompSheafToPreasheaf D)
  exact isLimitOfPreserves (presheafToSheaf J D ⋙ sheafToPresheaf J D) hS
  -- 🎉 no goals

instance preservesfiniteLimits_presheafToSheaf [HasFiniteLimits D] :
    PreservesFiniteLimits (presheafToSheaf J D) := by
  apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{max v u}
  -- ⊢ (J_1 : Type (max v u)) → {𝒥 : SmallCategory J_1} → FinCategory J_1 → Preserv …
  intros
  -- ⊢ PreservesLimitsOfShape J✝ (presheafToSheaf J D)
  infer_instance
  -- 🎉 no goals

end CategoryTheory
