/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Limits

noncomputable section

variable {C : Type u₁} [Category.{v₁} C]
variable {H : Type u₂} [Category.{v₂} H]
variable {J : Type u₁} [Category.{v₁} J]
variable {F : C ⥤ Cat}

@[simps!]
def fiberwiseColimitLimitIso (K : J ⥤ Grothendieck F ⥤ H)
    [∀ (c : C), HasColimitsOfShape (↑(F.obj c)) H] [HasLimitsOfShape J H] [HasColimitsOfShape C H]
    [∀ c, PreservesLimitsOfShape J (colim (J := F.obj c) (C := H))] :
    fiberwiseColimit (limit K) ≅ limit (K ⋙ fiberwiseColim _ _) :=
  NatIso.ofComponents
    (fun c => HasColimit.isoOfNatIso
       (limitCompWhiskeringLeftIsoCompLimit K (Grothendieck.ι F c)).symm ≪≫
      preservesLimitIso colim _ ≪≫
      HasLimit.isoOfNatIso
        (Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (fiberwiseColimcompEvaluationIso _).symm ≪≫
        (Functor.associator _ _ _).symm) ≪≫
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
instance preservesLimitsOfShape_colim_Grothendieck [HasColimitsOfShape C H]
    [∀ c, HasColimitsOfShape (↑(F.obj c)) H] [∀ c, HasLimitsOfShape J ((F.obj c) ⥤ H)]
    [HasLimitsOfShape J H] [PreservesLimitsOfShape J (colim (J := C) (C := H))]
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
       (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ fiberwiseColimCompColimIso)
  haveI : IsIso (limit.post K colim) := by
    convert Iso.isIso_hom i₂
    apply limit.hom_ext
    intro d
    simp [i₂]
    apply colimit.hom_ext
    intro d'
    simp
    sorry
  apply preservesLimit_of_isIso_post

end

end Limits

end CategoryTheory
