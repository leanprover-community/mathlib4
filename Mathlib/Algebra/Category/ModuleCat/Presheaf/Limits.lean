import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Limits

universe v₂ v₁ v u₃ u₂ u₁ u

namespace PresheafOfModules

open CategoryTheory Category Limits

-- let us not care too much about universes so far...

instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
  PreservesLimitsOfSize (ModuleCat.restrictScalars f) := sorry

instance {R : Type u₁} [Ring R] : HasLimitsOfSize (ModuleCat.{v} R) := sorry

section

variable {R : Type u₁} {S : Type u₃} [Ring R] [Ring S] (f : R →+* S)
  {J : Type u₂} [Category.{v₂} J] (F : J ⥤ ModuleCat.{v} S)

-- (if we do not have it already!) this should be generalized to any functor...
-- definition of the canonical map `G (limit F) ⟶ limit (F ⋙ G)` [first for any limit cone,
-- and then for the actual limit], then it is iso if `PreservesLimit...`
-- presumably, the various `Comparison` isos for the various shapes should be refactored to use this only...
noncomputable def restrictScalarsLimitIso :
    (ModuleCat.restrictScalars f).obj (limit F) ≅ limit (F ⋙ ModuleCat.restrictScalars f) :=
  IsLimit.conePointUniqueUpToIso
    (isLimitOfPreserves (ModuleCat.restrictScalars f) (limit.isLimit F))
      (limit.isLimit (F ⋙ ModuleCat.restrictScalars f))

@[reassoc (attr := simp)]
lemma restrictScalarsLimitIso_hom_π (j : J) :
    (restrictScalarsLimitIso f F).hom ≫ limit.π (F ⋙ ModuleCat.restrictScalars f) j =
      (ModuleCat.restrictScalars f).map (limit.π F j) := by
  dsimp only [restrictScalarsLimitIso]
  simp

@[reassoc (attr := simp)]
lemma restrictScalarsLimitIso_inv_map_π  (j : J) :
    (restrictScalarsLimitIso f F).inv ≫ (ModuleCat.restrictScalars f).map (limit.π F j) =
      limit.π (F ⋙ ModuleCat.restrictScalars f) j := by
  rw [← restrictScalarsLimitIso_hom_π, Iso.inv_hom_id_assoc]
end

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
  map {X Y} f := limMap (whiskerLeft F (restriction R f)) ≫ (restrictScalarsLimitIso (R.map f) (F ⋙ evaluation R Y)).inv
  map_id := fun X => by
    dsimp
    simp only [← cancel_mono (restrictScalarsLimitIso (R.map (𝟙 X)) (F ⋙ evaluation R X)).hom,
      assoc, Iso.inv_hom_id, comp_id]
    apply limit.hom_ext
    intro j
    simp only [Functor.comp_obj, evaluation_obj, limMap_π, whiskerLeft_app, assoc]
    erw [restrictScalarsLimitIso_hom_π, restriction_app_id]
    ext x
    dsimp
    rw [ModuleCat.restrictScalarsId'_inv_apply, ModuleCat.restrictScalarsId'_inv_apply]
  map_comp {X Y Z} f g := by
    dsimp
    simp only [← cancel_mono (restrictScalarsLimitIso (R.map (f ≫ g)) (F ⋙ evaluation R Z)).hom,
      assoc, Iso.inv_hom_id, comp_id]
    apply limit.hom_ext
    intro j
    simp only [Functor.comp_obj, evaluation_obj, limMap_π, whiskerLeft_app, Functor.map_comp, assoc]
    erw [restrictScalarsLimitIso_hom_π]
    sorry

noncomputable def limitCone : Cone F where
  pt := mk'' (limitBundledMkStruct F)
  π :=
    { app := fun j => Hom.mk'' (fun X => limit.π (F ⋙ evaluation R X) j) (fun X Y f => by
        dsimp
        simp only [Category.assoc, restrictScalarsLimitIso_inv_map_π]
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

end

end PresheafOfModules
