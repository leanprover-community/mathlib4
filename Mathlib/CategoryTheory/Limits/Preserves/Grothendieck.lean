/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Grothendieck

/-!
# Colimits on Grothendieck constructions preserving limits

We characterize the condition in which colimits on Grothendieck constructions preserve limits: By
preserving limits on the Grothendieck construction's base category as well as on each of its fibers.
-/


universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Functor

namespace Limits

noncomputable section

variable {C : Type u₁} [Category.{v₁} C]
variable {H : Type u₂} [Category.{v₂} H]
variable {J : Type u₃} [Category.{v₃} J]
variable {F : C ⥤ Cat.{v₄, u₄}}

/-- If `colim` on each fiber `F.obj c` of a functor `F : C ⥤ Cat` preserves limits of shape `J`,
then the fiberwise colimit of the limit of a functor `K : J ⥤ Grothendieck F ⥤ H` is naturally
isomorphic to taking the limit of the composition `K ⋙ fiberwiseColim F H`. -/
@[simps!]
def fiberwiseColimitLimitIso (K : J ⥤ Grothendieck F ⥤ H)
    [∀ (c : C), HasColimitsOfShape (↑(F.obj c)) H] [HasLimitsOfShape J H]
    [∀ c, PreservesLimitsOfShape J (colim (J := F.obj c) (C := H))] :
    fiberwiseColimit (limit K) ≅ limit (K ⋙ fiberwiseColim F H) :=
  NatIso.ofComponents
    (fun c => HasColimit.isoOfNatIso
       (limitCompWhiskeringLeftIsoCompLimit K (Grothendieck.ι F c)).symm ≪≫
      preservesLimitIso colim _ ≪≫
      HasLimit.isoOfNatIso
        (associator _ _ _ ≪≫
        isoWhiskerLeft _ (fiberwiseColimCompEvaluationIso _).symm ≪≫
        (associator _ _ _).symm) ≪≫
      (limitObjIsoLimitCompEvaluation _ c).symm)
    fun {c₁ c₂} f => by
      simp only [fiberwiseColimit_obj, fiberwiseColimit_map, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, limitObjIsoLimitCompEvaluation_inv_limit_map]
      apply colimit.hom_ext
      intro d
      simp only [← Category.assoc]
      congr 1
      apply limit.hom_ext
      intro e
      simp [← NatTrans.comp_app_assoc]

variable (C) (F) in
/-- If `colim` on a category `C` preserves limits of shape `J` and if it does so for `colim` on
every `F.obj c` for a functor `F : C ⥤ Cat`, then `colim` on `Grothendieck F` also preserves limits
of shape `J`. -/
instance preservesLimitsOfShape_colim_grothendieck [HasColimitsOfShape C H] [HasLimitsOfShape J H]
    [∀ c, HasColimitsOfShape (↑(F.obj c)) H] [PreservesLimitsOfShape J (colim (J := C) (C := H))]
    [∀ c, PreservesLimitsOfShape J (colim (J := F.obj c) (C := H))] :
    PreservesLimitsOfShape J (colim (J := Grothendieck F) (C := H)) := by
  constructor
  intro K
  let i₂ := calc colimit (limit K)
    _ ≅ colimit (fiberwiseColimit (limit K)) := (colimitFiberwiseColimitIso _).symm
    _ ≅ colimit (limit (K ⋙ fiberwiseColim _ _)) :=
          HasColimit.isoOfNatIso (fiberwiseColimitLimitIso _)
    _ ≅ limit ((K ⋙ fiberwiseColim _ _) ⋙ colim) :=
          preservesLimitIso colim (K ⋙ fiberwiseColim _ _)
    _ ≅ limit (K ⋙ colim) :=
      HasLimit.isoOfNatIso
       (associator _ _ _ ≪≫ isoWhiskerLeft _ fiberwiseColimCompColimIso)
  haveI : IsIso (limit.post K colim) := by
    convert Iso.isIso_hom i₂
    ext
    simp only [colim_obj, Functor.comp_obj, limit.post_π, colim_map, Iso.trans_def,
      Iso.trans_assoc, Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π,
      fiberwiseColim_obj, isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_hom_app,
      whiskerLeft_app, fiberwiseColimCompColimIso_hom_app, Category.id_comp,
      preservesLimitIso_hom_π_assoc, i₂]
    ext
    simp only [ι_colimMap, Trans.trans, Iso.symm_hom, ι_colimitFiberwiseColimitIso_inv_assoc,
      HasColimit.isoOfNatIso_ι_hom_assoc, fiberwiseColimit_obj, fiberwiseColimitLimitIso_hom_app,
      ι_colimMap_assoc, Category.assoc, limitObjIsoLimitCompEvaluation_inv_π_app_assoc,
      Functor.comp_obj, fiberwiseColim_obj, HasLimit.isoOfNatIso_hom_π_assoc,
      whiskeringLeft_obj_obj, colim_obj, evaluation_obj_obj, Iso.trans_hom, isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.associator_hom_app, whiskerLeft_app,
      fiberwiseColimCompEvaluationIso_inv_app, Functor.associator_inv_app, Category.comp_id,
      Category.id_comp, preservesLimitIso_hom_π_assoc, colim_map, Grothendieck.ι_obj,
      ι_colimitFiberwiseColimitIso_hom]
    simp [← Category.assoc, ← NatTrans.comp_app]
  apply preservesLimit_of_isIso_post

end

end Limits

end CategoryTheory
