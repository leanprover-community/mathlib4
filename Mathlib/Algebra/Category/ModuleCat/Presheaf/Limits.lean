import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Limits

universe v u₂ v₁ v₂ v₃ u₁ u₃ u

namespace AddCommGroupCat

open CategoryTheory

lemma isIso_iff_bijective {M N : AddCommGroupCat} (f : M ⟶ N) :
    IsIso f ↔ Function.Bijective f := by
  constructor
  · intro hf
    rw [Function.bijective_iff_has_inverse]
    exact ⟨inv f, fun x => by rw [← comp_apply, IsIso.hom_inv_id, id_apply],
      fun x => by rw [← comp_apply, IsIso.inv_hom_id, id_apply]⟩
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

instance (R : Type u₁) [Ring R] :
    ReflectsIsomorphisms (forget₂ (ModuleCat.{v} R) AddCommGroupCat) :=
  ⟨fun {A B} f hf => by
    let F := forget₂ (ModuleCat.{v} R) AddCommGroupCat
    let g := inv (F.map f)
    have hf' : Function.Bijective f :=
      (AddCommGroupCat.isIso_iff_bijective (F.map f)).1 inferInstance
    have h₁ : ∀ (b : B), f (g b) = b := fun b => by
      change (g ≫ F.map f) b = b
      simp only [IsIso.inv_hom_id, forget₂_obj, AddCommGroupCat.coe_id, id_eq]
    refine' ⟨⟨⟨g, g.map_add⟩ , _⟩, _, _⟩
    · intro r b
      apply hf'.injective
      change f (g (r • b)) = f (r • _)
      rw [h₁, map_smul, h₁]
    · exact F.map_injective (IsIso.hom_inv_id (F.map f))
    · exact F.map_injective (IsIso.inv_hom_id (F.map f))⟩

lemma isIso_iff_bijective {R : Type u} [Ring R] {M N : ModuleCat R} (f : M ⟶ N) :
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

lemma hasLimitsOfShape (J : Type u₂) [SmallCategory J] (R : Type u₁) [Ring R] :
    HasLimitsOfShape J (ModuleCatMax.{u₂, v} R) := by
  -- TODO: make explicit parameters for `ModuleCat.hasLimitsOfSize.{u₂, v}`
  have : HasLimitsOfSize.{u₂, u₂} (ModuleCatMax.{u₂, v} R) := hasLimitsOfSize.{u₂, v}
  apply HasLimitsOfSize.has_limits_of_shape

noncomputable def forget₂PreservesLimitsOfShape (J : Type u₂) [SmallCategory J] (R : Type u₁) [Ring R] :
    PreservesLimitsOfShape J (forget₂ (ModuleCat.{max u₂ v} R) AddCommGroupCat) := by
  have : PreservesLimitsOfSize.{u₂, u₂} (forget₂ (ModuleCat.{max u₂ v} R) AddCommGroupCat) :=
  -- TODO: make explicit parameters for `ModuleCat.forget₂AddCommGroupPreservesLimitsOfSize`
    forget₂AddCommGroupPreservesLimitsOfSize.{u₂, v}
  infer_instance

noncomputable def forget₂ReflectsLimitsOfShape (J : Type u₂) [SmallCategory J] (R : Type u₁) [Ring R] :
    ReflectsLimitsOfShape J (forget₂ (ModuleCat.{max u₂ v} R) AddCommGroupCat) := by
  have := hasLimitsOfShape.{v} J R
  have := forget₂PreservesLimitsOfShape.{v} J R
  exact reflectsLimitsOfShapeOfReflectsIsomorphisms

noncomputable def restrictScalarsPreservesLimitsOfShape (J : Type u₂) [SmallCategory J] {R : Type u₁} {S : Type u₃}
    [Ring R] [Ring S] (f : R →+* S) :
    PreservesLimitsOfShape J (restrictScalars.{max u₂ v} f) where
  preservesLimit {K} := ⟨fun {c} hc => by
    have := forget₂ReflectsLimitsOfShape.{v} J R
    have := forget₂PreservesLimitsOfShape.{v} J S
    refine' @isLimitOfReflects _ _ _ _ _ _ _ (forget₂ (ModuleCat.{max u₂ v} R) AddCommGroupCat) ((restrictScalars f).mapCone c) _ _
    exact isLimitOfPreserves (forget₂ (ModuleCat.{max u₂ v} S) AddCommGroupCat) hc⟩

end ModuleCat

namespace PresheafOfModules

open CategoryTheory Category Limits

noncomputable example (R : Type u) [Ring R] :
  PreservesLimits (forget₂ (ModuleCat.{v} R) AddCommGroupCat.{v}) :=
    @ModuleCat.forget₂AddCommGroupPreservesLimits R _

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {J : Type u₂} [SmallCategory J] (F : J ⥤ PresheafOfModules.{max u₂ v} R)

def evaluationJointlyReflectsLimits (c : Cone F)
    (hc : ∀ (X : Cᵒᵖ), IsLimit ((evaluation R X).mapCone c)) : IsLimit c := by
  letI : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y),
    PreservesLimitsOfShape J (ModuleCat.restrictScalars (R.map f)) := fun f =>
      ModuleCat.restrictScalarsPreservesLimitsOfShape.{v} _ _
  exact
  { lift := fun s => Hom.mk'' (fun X => (hc X).lift ((evaluation R X).mapCone s)) (fun X Y f => by
      apply (isLimitOfPreserves (ModuleCat.restrictScalars (R.map f)) (hc Y)).hom_ext
      intro j
      simp only [Functor.mapCone_π_app, Category.assoc, ← Functor.map_comp]
      erw [IsLimit.fac, ← NatTrans.naturality, ← NatTrans.naturality, IsLimit.fac_assoc]
      rfl)
    fac := fun s j => by
      ext1 X
      exact (hc X).fac ((evaluation R X).mapCone s) j
    uniq := fun s m hm => by
      ext1 X
      exact (hc X).uniq ((evaluation R X).mapCone s) ((evaluation R X).map m) (fun j => by
        dsimp
        rw [← hm]
        rfl) }

@[simps]
noncomputable def limitBundledMkStruct : BundledMkStruct R := by
  letI : ∀ (X : Cᵒᵖ), HasLimitsOfShape J (ModuleCat.{max u₂ v} (R.obj X)) :=
    fun _ => ModuleCat.hasLimitsOfShape.{v} _ _
  letI : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y),
      PreservesLimitsOfShape J (ModuleCat.restrictScalars (R.map f)) :=
    fun f => ModuleCat.restrictScalarsPreservesLimitsOfShape.{v} _ _
  exact
  { obj := fun X => limit (F ⋙ evaluation R X)
    map := fun {X Y} f => limMap (whiskerLeft F (restriction R f)) ≫ (preservesLimitIso ((ModuleCat.restrictScalars (R.map f))) (F ⋙ evaluation R Y)).inv
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
    map_comp := fun {X Y Z} f g => by
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
      rfl }

noncomputable def limitCone : Cone F := by
  letI : ∀ (X : Cᵒᵖ), HasLimitsOfShape J (ModuleCat.{max u₂ v} (R.obj X)) :=
    fun _ => ModuleCat.hasLimitsOfShape.{v} _ _
  letI : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y),
      PreservesLimitsOfShape J (ModuleCat.restrictScalars (R.map f)) :=
    fun f => ModuleCat.restrictScalarsPreservesLimitsOfShape.{v} _ _
  exact
  { pt := mk'' (limitBundledMkStruct.{v} F)
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
          exact (limit.w (F ⋙ evaluation R X) φ).symm } }

noncomputable def isLimitLimitCone : IsLimit (limitCone.{v} F) := by
  letI : ∀ (X : Cᵒᵖ), HasLimitsOfShape J (ModuleCat.{max u₂ v} (R.obj X)) :=
    fun _ => ModuleCat.hasLimitsOfShape.{v} _ _
  exact evaluationJointlyReflectsLimits.{v} _ _ (fun _ => limit.isLimit _)

variable (R J)

lemma hasLimitsOfShape : HasLimitsOfShape J (PresheafOfModules.{max u₂ v} R) where
  has_limit F := ⟨_, isLimitLimitCone.{v} F⟩

attribute [instance] hasLimitsOfShape

noncomputable def evaluationPreservesLimitsOfShape (X : Cᵒᵖ) :
    PreservesLimitsOfShape J (evaluation R X : PresheafOfModules.{max u₂ v} R ⥤ _) where
  preservesLimit := fun {K} => by
    letI : HasLimitsOfShape J (ModuleCat.ModuleCatMax.{u₂, v} (R.obj X)) :=
      ModuleCat.hasLimitsOfShape _ _
    exact preservesLimitOfPreservesLimitCone (isLimitLimitCone.{v} K) (limit.isLimit _)

instance : HasFiniteLimits (PresheafOfModules.{v} R) :=
  ⟨fun _ => inferInstance⟩

noncomputable instance (X : Cᵒᵖ) : PreservesFiniteLimits (evaluation.{v} R X) :=
  ⟨fun _ _ _ => evaluationPreservesLimitsOfShape.{v} _ _ _⟩

instance (J : Type v) [SmallCategory J] : HasLimitsOfShape J (PresheafOfModules.{v} R) := by
  apply hasLimitsOfShape.{v}

noncomputable instance (J : Type v) [SmallCategory J] (X : Cᵒᵖ) :
    PreservesLimitsOfShape J (evaluation.{v} R X) :=
  evaluationPreservesLimitsOfShape.{v, v} _ _ _

end PresheafOfModules
