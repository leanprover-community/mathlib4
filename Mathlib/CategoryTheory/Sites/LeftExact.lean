/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Adhesive
import Mathlib.CategoryTheory.Sites.ConcreteSheafification

/-!
# Left exactness of sheafification
In this file we show that sheafification commutes with finite limits.
-/


open CategoryTheory Limits Opposite

universe s t w' w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

noncomputable section

namespace CategoryTheory.GrothendieckTopology

variable {D : Type w} [Category.{t} D]
variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]

/-- An auxiliary definition to be used in the proof of the fact that
`J.diagramFunctor D X` preserves limits. -/
@[simps]
def coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation {X : C} {K : Type s}
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

/-- Auxiliary definition for `liftToDiagramLimitObj`. -/
def liftToDiagramLimitObjAux {X : C} {K : Type s} [SmallCategory K] [HasLimitsOfShape K D]
    {W : (J.Cover X)ᵒᵖ} (F : K ⥤ Cᵒᵖ ⥤ D)
    (E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj W))
    (i : (unop W).Arrow) :
    E.pt ⟶ (limit F).obj (op i.Y) :=
  (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op i.Y)) (limit.isLimit F)).lift
        (coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation i E)

@[reassoc (attr := simp)]
lemma liftToDiagramLimitObjAux_fac {X : C} {K : Type s} [SmallCategory K]
    [HasLimitsOfShape K D] {W : (J.Cover X)ᵒᵖ} (F : K ⥤ Cᵒᵖ ⥤ D)
    (E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj W))
    (i : (unop W).Arrow) (k : K) :
    liftToDiagramLimitObjAux F E i ≫ (limit.π F k).app (op i.Y) = E.π.app k ≫
      Multiequalizer.ι ((unop W).index (F.obj k)) i :=
  IsLimit.fac _ _ _

/-- An auxiliary definition to be used in the proof of the fact that
`J.diagramFunctor D X` preserves limits. -/
abbrev liftToDiagramLimitObj {X : C} {K : Type s} [SmallCategory K] [HasLimitsOfShape K D]
    {W : (J.Cover X)ᵒᵖ} (F : K ⥤ Cᵒᵖ ⥤ D)
    (E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj W)) :
    E.pt ⟶ (J.diagram (limit F) X).obj W :=
  Multiequalizer.lift ((unop W).index (limit F)) E.pt (liftToDiagramLimitObjAux F E)
    (by
      intro i
      dsimp
      ext k
      dsimp
      simp only [Category.assoc, NatTrans.naturality, liftToDiagramLimitObjAux_fac_assoc]
      erw [Multiequalizer.condition]
      rfl)

instance preservesLimit_diagramFunctor
    (X : C) (K : Type s) [SmallCategory K] [HasLimitsOfShape K D] (F : K ⥤ Cᵒᵖ ⥤ D) :
    PreservesLimit F (J.diagramFunctor D X) :=
  preservesLimit_of_evaluation _ _ fun W =>
    preservesLimit_of_preserves_limit_cone (limit.isLimit _)
      { lift := fun E => liftToDiagramLimitObj.{_, t, w, v, u} F E
        fac := by
          intro E k
          dsimp [diagramNatTrans]
          refine Multiequalizer.hom_ext _ _ _ (fun a => ?_)
          simp only [Multiequalizer.lift_ι, Multiequalizer.lift_ι_assoc, Category.assoc,
            liftToDiagramLimitObjAux_fac]
        uniq := by
          intro E m hm
          refine Multiequalizer.hom_ext _ _ _ (fun a => limit_obj_ext (fun j => ?_))
          dsimp [liftToDiagramLimitObj]
          rw [Multiequalizer.lift_ι, Category.assoc, liftToDiagramLimitObjAux_fac, ← hm,
            Category.assoc]
          dsimp
          rw [limit.lift_π]
          dsimp }

instance preservesLimitsOfShape_diagramFunctor
    (X : C) (K : Type s) [SmallCategory K] [HasLimitsOfShape K D] :
    PreservesLimitsOfShape K (J.diagramFunctor D X) :=
  ⟨by apply preservesLimit_diagramFunctor.{s, t, w, v, u}⟩

instance preservesLimits_diagramFunctor (X : C) [HasLimitsOfSize.{max t u v, max t u v} D] :
    PreservesLimits (J.diagramFunctor D X) := by
  constructor
  intro _ _
  apply preservesLimitsOfShape_diagramFunctor.{max t u v}

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
variable [HasForget.{t} D]
variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]
variable [∀ X : C, Small.{t, max u v} (J.Cover X)ᵒᵖ]

/-- An auxiliary definition to be used in the proof that `J.plusFunctor D` commutes
with finite limits. -/
def liftToPlusObjLimitObj {K : Type s} [SmallCategory K] [FinCategory K]
    [HasLimitsOfShape K D] [PreservesLimitsOfShape K (forget D)]
    [ReflectsLimitsOfShape K (forget D)] (F : K ⥤ Cᵒᵖ ⥤ D) (X : C)
    (S : Cone (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))) :
    S.pt ⟶ (J.plusObj (limit F)).obj (op X) :=
  let x := (J.Cover X)ᵒᵖ
  let F' := F ⋙ J.diagramFunctor D X
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
        rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
        refine colimit.hom_ext (fun w => ?_)
        dsimp [plusMap]
        erw [colimit.ι_map_assoc,
          colimitObjIsoColimitCompEvaluation_ι_inv (F ⋙ J.diagramFunctor D X).flip w j,
          colimitObjIsoColimitCompEvaluation_ι_inv_assoc (F ⋙ J.diagramFunctor D X).flip w i]
        rw [← (colimit.ι (F ⋙ J.diagramFunctor D X).flip w).naturality]
        rfl)
  limit.lift _ S ≫ (HasLimit.isoOfNatIso s.symm).hom ≫ e.inv ≫ p.inv

-- This lemma should not be used directly. Instead, one should use the fact that
-- `J.plusFunctor D` preserves finite limits, along with the fact that
-- evaluation preserves limits.
theorem liftToPlusObjLimitObj_fac {K : Type s} [SmallCategory K] [FinCategory K]
    [HasLimitsOfShape K D] [PreservesLimitsOfShape K (forget D)]
    [ReflectsLimitsOfShape K (forget D)] (F : K ⥤ Cᵒᵖ ⥤ D) (X : C)
    (S : Cone (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))) (k) :
    liftToPlusObjLimitObj F X S ≫ (J.plusMap (limit.π F k)).app (op X) = S.π.app k := by
  dsimp only [liftToPlusObjLimitObj]
  rw [← (limit.isLimit (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))).fac S k,
    Category.assoc]
  congr 1
  dsimp
  rw [Category.assoc, Category.assoc, ← Iso.eq_inv_comp, Iso.inv_comp_eq, Iso.inv_comp_eq]
  refine colimit.hom_ext (fun j => ?_)
  dsimp [plusMap]
  simp only [HasColimit.isoOfNatIso_ι_hom_assoc, ι_colimMap]
  dsimp [IsLimit.conePointUniqueUpToIso, HasLimit.isoOfNatIso, IsLimit.map]
  rw [limit.lift_π]
  dsimp
  rw [ι_colimitLimitIso_limit_π_assoc]
  simp_rw [← Category.assoc, ← NatTrans.comp_app]
  rw [limit.lift_π, Category.assoc]
  congr 1
  rw [← Iso.comp_inv_eq]
  erw [colimit.ι_desc]
  rfl

instance preservesLimitsOfShape_plusFunctor
    (K : Type t) [SmallCategory K] [FinCategory K] [HasLimitsOfShape K D]
    [PreservesLimitsOfShape K (forget D)] [ReflectsLimitsOfShape K (forget D)] :
    PreservesLimitsOfShape K (J.plusFunctor D) := by
  constructor; intro F; apply preservesLimit_of_evaluation; intro X
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit F)
  refine ⟨fun S => liftToPlusObjLimitObj F X.unop S, ?_, ?_⟩
  · intro S k
    apply liftToPlusObjLimitObj_fac
  · intro S m hm
    dsimp [liftToPlusObjLimitObj]
    simp_rw [← Category.assoc, Iso.eq_comp_inv, ← Iso.comp_inv_eq]
    refine limit.hom_ext (fun k => ?_)
    simp only [limit.lift_π, Category.assoc, ← hm]
    congr 1
    refine colimit.hom_ext (fun k => ?_)
    dsimp [plusMap, plusObj]
    erw [colimit.ι_map, colimit.ι_desc_assoc, limit.lift_π]
    conv_lhs => dsimp
    simp only [Category.assoc]
    rw [ι_colimitLimitIso_limit_π_assoc]
    simp only [colimitObjIsoColimitCompEvaluation_ι_app_hom]
    conv_lhs =>
      dsimp [IsLimit.conePointUniqueUpToIso]
    rw [← Category.assoc, ← NatTrans.comp_app, limit.lift_π]
    rfl

instance preserveFiniteLimits_plusFunctor
    [HasFiniteLimits D] [PreservesFiniteLimits (forget D)] [(forget D).ReflectsIsomorphisms] :
    PreservesFiniteLimits (J.plusFunctor D) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{t}
  intro K _ _
  have : ReflectsLimitsOfShape K (forget D) := reflectsLimitsOfShape_of_reflectsIsomorphisms
  apply preservesLimitsOfShape_plusFunctor

instance preservesLimitsOfShape_sheafification
    (K : Type t) [SmallCategory K] [FinCategory K] [HasLimitsOfShape K D]
    [PreservesLimitsOfShape K (forget D)] [ReflectsLimitsOfShape K (forget D)] :
    PreservesLimitsOfShape K (J.sheafification D) :=
  Limits.comp_preservesLimitsOfShape _ _

instance preservesFiniteLimits_sheafification
    [HasFiniteLimits D] [PreservesFiniteLimits (forget D)] [(forget D).ReflectsIsomorphisms] :
    PreservesFiniteLimits (J.sheafification D) :=
  Limits.comp_preservesFiniteLimits _ _

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory

section

variable {D : Type w} [Category.{t} D]
variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
variable {FD : D → D → Type*} {CD : D → Type t}
variable [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{t} D FD]
variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]
variable [(forget D).ReflectsIsomorphisms]
variable [∀ {X : C} (S : J.Cover X), PreservesLimitsOfShape (WalkingMulticospan S.shape) (forget D)]
variable (K : Type w')
variable [SmallCategory K] [FinCategory K] [HasLimitsOfShape K D]

instance preservesLimitsOfShape_presheafToSheaf
    [PreservesLimits (forget D)] [∀ X : C, Small.{t, max u v} (J.Cover X)ᵒᵖ] :
    PreservesLimitsOfShape K (plusPlusSheaf J D) := by
  let e := (FinCategory.equivAsType K).symm.trans (AsSmall.equiv.{0, 0, t})
  haveI : HasLimitsOfShape (AsSmall.{t} (FinCategory.AsType K)) D :=
    Limits.hasLimitsOfShape_of_equivalence e
  haveI : FinCategory (AsSmall.{t} (FinCategory.AsType K)) := by
    constructor
    · change Fintype (ULift _)
      infer_instance
    · intro j j'
      change Fintype (ULift _)
      infer_instance
  refine @preservesLimitsOfShape_of_equiv _ _ _ _ _ _ _ _ e.symm _ (show _ from ?_)
  constructor; intro F; constructor; intro S hS; constructor
  apply isLimitOfReflects (sheafToPresheaf J D)
  have : ReflectsLimitsOfShape (AsSmall.{t} (FinCategory.AsType K)) (forget D) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  apply isLimitOfPreserves (J.sheafification D) hS

instance preservesFiniteLimits_presheafToSheaf [PreservesLimits (forget D)]
    [∀ X : C, Small.{t, max u v} (J.Cover X)ᵒᵖ] [HasFiniteLimits D] :
    PreservesFiniteLimits (plusPlusSheaf J D) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{t}
  intros
  infer_instance

variable (J D)

/-- `plusPlusSheaf` is isomorphic to an arbitrary choice of left adjoint. -/
def plusPlusSheafIsoPresheafToSheaf : plusPlusSheaf J D ≅ presheafToSheaf J D :=
  (plusPlusAdjunction J D).leftAdjointUniq (sheafificationAdjunction J D)

/-- `plusPlusFunctor` is isomorphic to `sheafification`. -/
def plusPlusFunctorIsoSheafification : J.sheafification D ≅ sheafification J D :=
  Functor.isoWhiskerRight (plusPlusSheafIsoPresheafToSheaf J D) (sheafToPresheaf J D)

/-- `plusPlus` is isomorphic to `sheafify`. -/
def plusPlusIsoSheafify (P : Cᵒᵖ ⥤ D) : J.sheafify P ≅ sheafify J P :=
  (sheafToPresheaf J D).mapIso ((plusPlusSheafIsoPresheafToSheaf J D).app P)

@[reassoc (attr := simp)]
lemma toSheafify_plusPlusIsoSheafify_hom (P : Cᵒᵖ ⥤ D) :
    J.toSheafify P ≫ (plusPlusIsoSheafify J D P).hom = toSheafify J P := by
  convert Adjunction.unit_leftAdjointUniq_hom_app
    (plusPlusAdjunction J D) (sheafificationAdjunction J D) P
  ext1 P
  dsimp [GrothendieckTopology.toSheafify, plusPlusAdjunction]
  rw [Category.comp_id]

instance [PreservesLimits (forget D)] [HasFiniteLimits D]
    [∀ X : C, Small.{t, max u v} (J.Cover X)ᵒᵖ] :
    HasSheafify J D :=
  HasSheafify.mk' J D (plusPlusAdjunction J D)

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
instance : HasSheafify J (Type max u v) := by
  infer_instance

end

variable {D : Type w} [Category.{w'} D]

instance [FinitaryExtensive D] [HasPullbacks D] [HasSheafify J D] :
    FinitaryExtensive (Sheaf J D) :=
  finitaryExtensive_of_reflective (sheafificationAdjunction _ _)

instance [Adhesive D] [HasPullbacks D] [HasPushouts D] [HasSheafify J D] :
    Adhesive (Sheaf J D) :=
  adhesive_of_reflective (sheafificationAdjunction _ _)

instance SheafOfTypes.finitary_extensive [HasSheafify J (Type w)] :
    FinitaryExtensive (Sheaf J (Type w)) :=
  inferInstance

instance SheafOfTypes.adhesive [HasSheafify J (Type w)] :
    Adhesive (Sheaf J (Type w)) :=
  inferInstance

instance SheafOfTypes.balanced [HasSheafify J (Type w)] :
    Balanced (Sheaf J (Type w)) :=
  inferInstance

end CategoryTheory
