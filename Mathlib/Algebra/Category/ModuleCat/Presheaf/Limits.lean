import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.Limits

universe w' w v₁ v₂ v u₁ u₂ u

namespace AddCommGroupCat

open CategoryTheory

-- TODO: cleanup the ReflectsIsomorphisms instance for
-- `(forget₂ (ModuleCat.{v} R) AddCommGroupCat)`
--
-- show `ModuleCat.restrictScalars` preserves all limits

instance : (forget AddCommGroupCat).ReflectsIsomorphisms := inferInstance

lemma isIso_iff_bijective {M N : AddCommGroupCat} (f : M ⟶ N) :
    IsIso f ↔ Function.Bijective f := by
  constructor
  · intro hf
    rw [Function.bijective_iff_has_inverse]
    refine' ⟨inv f, fun x => by erw [← comp_apply, IsIso.hom_inv_id, id_apply],
      fun x => by erw [← comp_apply, IsIso.inv_hom_id, id_apply]⟩
  · intro H
    obtain ⟨g, hg₁, hg₂⟩ := Function.bijective_iff_has_inverse.1 H
    refine' ⟨AddMonoidHom.mk' g _, _, _⟩
    · intro a b
      change ∀ _, _ at hg₂
      apply H.injective
      simp only [map_add, hg₂]
    · ext x
      apply hg₁
    · ext x
      apply hg₂

end AddCommGroupCat

namespace ModuleCat

open CategoryTheory Limits

--instance (R : Type u) [Ring R] :
--    (forget (ModuleCat.{v} R)).ReflectsIsomorphisms := sorry

instance (R : Type u) [Ring R] :
    (forget₂ (ModuleCat.{v} R) AddCommGroupCat).ReflectsIsomorphisms :=
  ⟨fun {A B} f hf => by
    let F := forget₂ (ModuleCat.{v} R) AddCommGroupCat
    have hf' : Function.Bijective f :=
      (AddCommGroupCat.isIso_iff_bijective (F.map f)).1 inferInstance
    let g := inv (F.map f)
    have h₁ : ∀ (b : B), f (g b) = b := fun b => by
      change (g ≫ F.map f) b = b
      simp [g]
    refine' ⟨⟨⟨g, g.map_add⟩ , _⟩, _, _⟩
    · intro r b
      apply hf'.injective
      change f (g (r • b)) = f (r • _)
      rw [h₁, map_smul, h₁]
    · exact F.map_injective (IsIso.hom_inv_id (F.map f))
    · exact F.map_injective (IsIso.inv_hom_id (F.map f))⟩

lemma isIso_iff_bijective {R : Type*} [Ring R] {M N : ModuleCat R} (f : M ⟶ N) :
    IsIso f ↔ Function.Bijective f := by
  constructor
  · intro
    have h : IsIso ((forget₂ _ AddCommGroupCat).map f) := inferInstance
    rw [AddCommGroupCat.isIso_iff_bijective] at h
    exact h
  · intro hf
    have : IsIso ((forget₂ (ModuleCat R) AddCommGroupCat).map f) :=
      (AddCommGroupCat.isIso_iff_bijective _).2 hf
    exact isIso_of_reflects_iso f (forget₂ (ModuleCat R) AddCommGroupCat)

end ModuleCat

namespace PresheafOfModules

open CategoryTheory Category Limits

section Limits

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
  {J : Type u₂} [Category.{v₂} J] (F : J ⥤ PresheafOfModules.{w'} R)
  [∀ {X Y : Cᵒᵖ} (f : X ⟶ Y),
    PreservesLimitsOfShape J (ModuleCat.restrictScalars (R.map f))]
    -- note that `ModuleCat.restrictScalars` preserves all limits, regardless of universes
    -- so that this assumption shall be redundant

def evaluationJointlyReflectsLimits (c : Cone F)
    (hc : ∀ (X : Cᵒᵖ), IsLimit ((evaluation R X).mapCone c)) : IsLimit c where
  lift s := Hom.mk'' (fun X => (hc X).lift ((evaluation R X).mapCone s)) (fun X Y f => by
    apply (isLimitOfPreserves (ModuleCat.restrictScalars (R.map f)) (hc Y)).hom_ext
    intro j
    rw [Functor.mapCone_π_app, assoc, assoc, ← Functor.map_comp]
    erw [restrictionApp_naturality, IsLimit.fac, restrictionApp_naturality, IsLimit.fac_assoc]
    rfl)
  fac s j := by
    ext1 X
    exact (hc X).fac ((evaluation R X).mapCone s) j
  uniq s m hm := by
    ext1 X
    apply (hc X).uniq ((evaluation R X).mapCone s)
    intro j
    dsimp
    rw [← hm]
    rfl

section

-- this assumption should be found automatically in suitable universes
variable [∀ X, HasLimit (F ⋙ evaluation R X)]

instance {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    HasLimit (F ⋙ evaluation R Y ⋙ ModuleCat.restrictScalars (R.map f)) := by
  change HasLimit ((F ⋙ evaluation R Y) ⋙ ModuleCat.restrictScalars (R.map f))
  infer_instance

@[simps]
noncomputable def limitBundledCore : BundledCorePresheafOfModules R where
  obj X := limit (F ⋙ evaluation R X)
  map {X Y} f := limMap (whiskerLeft F (restriction R f)) ≫
    (preservesLimitIso (ModuleCat.restrictScalars (R.map f)) (F ⋙ evaluation R Y)).inv
  map_id X := by
    dsimp
    rw [← cancel_mono (preservesLimitIso _ _).hom, assoc, Iso.inv_hom_id, comp_id]
    apply limit.hom_ext
    intro j
    dsimp
    simp only [limMap_π, Functor.comp_obj, evaluation_obj, whiskerLeft_app,
      restriction_app, assoc]
    erw [preservesLimitsIso_hom_π]
    rw [← ModuleCat.restrictScalarsId'App_inv_naturality, restrictionApp_id]
    dsimp
  map_comp {X Y Z} f g := by
    dsimp
    rw [← cancel_mono (preservesLimitIso _ _).hom, assoc, assoc, assoc, assoc, Iso.inv_hom_id,
      comp_id]
    apply limit.hom_ext
    intro j
    simp only [Functor.comp_obj, evaluation_obj, limMap_π, whiskerLeft_app, restriction_app,
      Functor.map_comp, assoc, restrictionApp_comp]
    erw [preservesLimitsIso_hom_π, ← ModuleCat.restrictScalarsComp'App_inv_naturality]
    dsimp
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, assoc,
      preservesLimitsIso_inv_π]
    erw [limMap_π]
    dsimp
    simp only [Functor.map_comp, assoc, preservesLimitsIso_inv_π_assoc]
    erw [limMap_π_assoc]
    dsimp

noncomputable def limitConeπApp (j : J) : (limitBundledCore F).toPresheafOfModules ⟶ F.obj j :=
  PresheafOfModules.Hom.mk'' (fun X => limit.π (F ⋙ evaluation R X) j) (fun X Y f => by
    dsimp
    simp only [assoc, preservesLimitsIso_inv_π]
    apply limMap_π)

@[reassoc (attr := simp)]
lemma limitConeπApp_naturality {i j : J} (f : i ⟶ j) :
    limitConeπApp F i ≫ F.map f = limitConeπApp F j := by
  ext1 X
  exact limit.w (F ⋙ evaluation R X) f

@[simps]
noncomputable def limitCone : Cone F where
  pt := (limitBundledCore F).toPresheafOfModules
  π := { app := limitConeπApp F }

noncomputable def isLimitLimitCone : IsLimit (limitCone F) :=
  evaluationJointlyReflectsLimits _ _ (fun _ => limit.isLimit _)

instance hasLimit : HasLimit F := ⟨_, isLimitLimitCone F⟩

end

section

variable (R J)

-- this assumption should be found automatically in suitable universes
variable [∀ X, HasLimitsOfShape J (ModuleCat.{w'} (R.obj X))]

instance hasLimitsOfShape : HasLimitsOfShape J (PresheafOfModules.{w'} R) where

noncomputable def evaluationPreservesLimitsOfShape (X : Cᵒᵖ) :
    PreservesLimitsOfShape J (evaluation R X : PresheafOfModules.{w'} R ⥤ _) where
  preservesLimit {F} :=
    preservesLimitOfPreservesLimitCone (isLimitLimitCone F) (limit.isLimit _)

end

variable [∀ {X Y : Cᵒᵖ} (f : X ⟶ Y),
    PreservesFiniteLimits (ModuleCat.restrictScalars (R.map f))]
    -- this `PreservesLimitsOfShape` assumption is redundant

instance : HasFiniteLimits (PresheafOfModules.{w'} R) :=
  ⟨fun _ => inferInstance⟩

noncomputable instance (X : Cᵒᵖ) : PreservesFiniteLimits (evaluation.{w'} R X) where
  preservesFiniteLimits J _ _ := evaluationPreservesLimitsOfShape.{w'} R J X

end Limits

end PresheafOfModules
