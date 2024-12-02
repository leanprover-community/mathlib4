import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {H : Type u₂} [Category.{v₂} H]
variable {J : Type u₁} [Category.{v₁} J]
variable {F : C ⥤ Cat}

variable (C) (F) in
instance preservesLimitsOfShape_colim_Grothendieck [HasColimitsOfShape C H]
    [∀ c, HasColimitsOfShape (↑(F.obj c)) H]
    [hC : PreservesLimitsOfShape J (colim (J := C) (C := H))]
    [∀ c, PreservesLimitsOfShape J (colim (J := F.obj c) (C := H))] :
    PreservesLimitsOfShape J (colim (J := Grothendieck F) (C := H)) := by
  haveI : HasLimitsOfShape J (Grothendieck F ⥤ H) := sorry
  haveI : HasLimitsOfShape J (C ⥤ H) := sorry
  haveI : HasLimitsOfShape J H := sorry
  haveI : HasLimitsOfShape C H := sorry
  haveI : HasColimitsOfShape J (C ⥤ H) := sorry
  constructor
  intro K
  haveI : ∀ c, HasLimit (K ⋙ (whiskeringLeft (↑(F.obj c)) (Grothendieck F) H).obj (Grothendieck.ι F c)) := sorry
  let i₀ : ∀ c, Grothendieck.ι F c ⋙ limit K ≅
    limit (K ⋙ (whiskeringLeft _ _ _).obj (Grothendieck.ι F c)) := sorry
  let i₁ : fiberwiseColimit (limit K) ≅ limit (K ⋙ fiberwiseColimit') :=
    NatIso.ofComponents
      (fun c => HasColimit.isoOfNatIso (i₀ c) ≪≫
        preservesLimitIso colim _ ≪≫
        HasLimit.isoOfNatIso
          (Functor.associator _ _ _ ≪≫
          isoWhiskerLeft _ _ ≪≫
          (Functor.associator _ _ _).symm) ≪≫
        (limitObjIsoLimitCompEvaluation _ c).symm)
      _
  let i₂ := calc colimit (limit K)
    _ ≅ colimit (fiberwiseColimit (limit K)) := (colimitFiberwiseColimitIso _).symm
    _ ≅ colimit (limit (K ⋙ fiberwiseColimit')) := HasColimit.isoOfNatIso i₁
    _ ≅ limit ((K ⋙ fiberwiseColimit') ⋙ colim) :=
          preservesLimitIso colim (K ⋙ fiberwiseColimit')
    _ ≅ limit (K ⋙ colim) := by sorry  -- TODO functorialisation of `colimitFiberwiseColimitIso`
  haveI : IsIso (limit.post K colim) := by
    convert Iso.isIso_hom i₂
    apply colimit.hom_ext
    intro d
    ext d'
    sorry
  apply preservesLimit_of_isIso_post

#check limitCompWhiskeringRightIsoLimitComp
#check limitObjIsoLimitCompEvaluation
#check Functor.associator

end Limits

end CategoryTheory
