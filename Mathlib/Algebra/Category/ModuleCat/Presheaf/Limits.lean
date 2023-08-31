import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Limits

universe v₁ v₂ v₃ v u₁ u₂ u₃ u

namespace PresheafOfModules

open CategoryTheory Category Limits

-- let us not care too much about universes for now...

instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
  PreservesLimitsOfSize (ModuleCat.restrictScalars f) := sorry

instance {R : Type u₁} [Ring R] : HasLimitsOfSize (ModuleCat.{v} R) := sorry

noncomputable example (R : Type u) [Ring R] :
  PreservesLimits (forget₂ (ModuleCat.{v} R) AddCommGroupCat.{v}) :=
    @ModuleCat.forget₂AddCommGroupPreservesLimits R _

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {J : Type u₂} [Category.{v₂} J] (F : J ⥤ PresheafOfModules.{v} R)

def evaluationJointlyReflectsLimits (c : Cone F)
    (hc : ∀ (X : Cᵒᵖ), IsLimit ((evaluation.{v} R X).mapCone c)) : IsLimit c where
  lift s := Hom.mk'' (fun X => (hc X).lift ((evaluation.{v} R X).mapCone s)) (fun X Y f => by
    apply (isLimitOfPreserves (ModuleCat.restrictScalars (R.map f)) (hc Y)).hom_ext
    intro j
    simp only [Functor.mapCone_π_app, Category.assoc, ← Functor.map_comp]
    erw [IsLimit.fac, ← NatTrans.naturality, ← NatTrans.naturality, IsLimit.fac_assoc]
    rfl)
  fac s j := by
    ext1 X
    exact (hc X).fac ((evaluation.{v} R X).mapCone s) j
  uniq s m hm := by
    ext1 X
    exact (hc X).uniq ((evaluation.{v} R X).mapCone s) ((evaluation.{v} R X).map m) (fun j => by
      dsimp
      rw [← hm]
      rfl)

section

@[simps]

noncomputable def limitBundledMkStruct : BundledMkStruct R where
  obj X := limit (F ⋙ evaluation R X)
  map {X Y} f := limMap (whiskerLeft F (restriction R f)) ≫ (preservesLimitIso ((ModuleCat.restrictScalars (R.map f))) (F ⋙ evaluation R Y)).inv
  map_id := fun X => by
    dsimp
    simp only [← cancel_mono (preservesLimitIso ((ModuleCat.restrictScalars (R.map (𝟙 X)))) (F ⋙ evaluation R X)).hom]
    simp only [assoc, Iso.inv_hom_id, comp_id]
    apply limit.hom_ext
    intro j
    erw [limMap_π, assoc, preservesLimitsIso_hom_π]
    simp only [← cancel_mono ((ModuleCat.restrictScalarsId' (R.map (𝟙 X)) (R.map_id X)).hom.app ((F.obj j).obj X)),
      Functor.comp_obj, evaluation_obj, whiskerLeft_app, restriction_app_id,
      Functor.id_obj, assoc, Iso.inv_hom_id_app, comp_id, NatTrans.naturality,
      Functor.id_map, Iso.inv_hom_id_app_assoc]
  map_comp {X Y Z} f g := by
    dsimp
    simp only [← cancel_mono (preservesLimitIso ((ModuleCat.restrictScalars (R.map (f ≫ g)))) (F ⋙ evaluation R Z)).hom,
      assoc, Iso.inv_hom_id, comp_id]
    apply limit.hom_ext
    intro j
    simp only [limMap_π, Functor.comp_obj, evaluation_obj, whiskerLeft_app,
      Functor.map_comp, assoc, restriction_app_comp]
    erw [preservesLimitsIso_hom_π, ← NatTrans.naturality]
    dsimp
    simp only [← Functor.map_comp_assoc]
    erw [preservesLimitsIso_inv_π, limMap_π, Functor.map_comp_assoc,
      preservesLimitsIso_inv_π_assoc, limMap_π_assoc]
    rfl

noncomputable def limitCone : Cone F where
  pt := mk'' (limitBundledMkStruct F)
  π :=
    { app := fun j => Hom.mk'' (fun X => limit.π (F ⋙ evaluation R X) j) (fun X Y f => by
        dsimp
        simp only [assoc, preservesLimitsIso_inv_π]
        apply limMap_π)
      naturality := fun i j φ => by
        dsimp
        erw [id_comp]
        ext1 X
        simp only [mk''_obj, limitBundledMkStruct_obj, Hom.mk''_app, Hom.comp_app]
        exact (limit.w (F ⋙ evaluation R X) φ).symm }

noncomputable def isLimitLimitCone : IsLimit (limitCone F) :=
  evaluationJointlyReflectsLimits _ _ (fun _ => limit.isLimit _)

instance : HasLimitsOfShape J (PresheafOfModules.{v} R) where
  has_limit F := ⟨_, isLimitLimitCone F⟩

noncomputable instance (X : Cᵒᵖ) : PreservesLimitsOfShape J (evaluation R X) where
  preservesLimit :=
    preservesLimitOfPreservesLimitCone (isLimitLimitCone _) (limit.isLimit _)

#exit

end

end PresheafOfModules
