import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Limits

universe v₂ v₁ v u₃ u₂ u₁ u

namespace PresheafOfModules

open CategoryTheory Limits

-- let us not care too much about universes so far...

instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
  PreservesLimitsOfSize (ModuleCat.restrictScalars f) := sorry

instance {R : Type u₁} [Ring R] : HasLimitsOfSize (ModuleCat.{v} R) := sorry

section

variable {R : Type u₁} {S : Type u₃} [Ring R] [Ring S] (f : R →+* S)
  {J : Type u₂} [Category.{v₂} J] (F : J ⥤ ModuleCat.{v} S)

-- all of this should be generalized...
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


@[simps]
def semilinearMapEquiv {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    (M : ModuleCat.{v} R) (N : ModuleCat.{v} S) :
    (M →ₛₗ[f] N) ≃ (M ⟶ (ModuleCat.restrictScalars f).obj N) where
  toFun g :=
    { toFun := g
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp }
  invFun g :=
    { toFun := g
      map_add' := fun x y => by simp
      map_smul' := fun r x => g.map_smul r x }
  left_inv f := rfl
  right_inv f := rfl

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

variable [∀ X, HasLimit (F ⋙ evaluation R X)]

noncomputable def limitMkStruct : MkStruct R where
  obj X := (limit (F ⋙ evaluation R X)).carrier
  map {X Y} f :=
    (semilinearMapEquiv (R.map f) _ _).symm (limMap (whiskerLeft F (restriction R f)) ≫ (restrictScalarsLimitIso (R.map f) (F ⋙ evaluation R Y)).inv)
  map_id := sorry
  map_comp := sorry

@[simp]
lemma restriction_app_mk'_limitMkStruct_restriction {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (restriction R f).app (mk' (limitMkStruct F)) =
      (limMap (whiskerLeft F (restriction R f)) ≫ (restrictScalarsLimitIso (R.map f) (F ⋙ evaluation R Y)).inv) := by
  rfl

noncomputable def limitCone : Cone F where
  pt := mk' (limitMkStruct F)
  π :=
    { app := fun j => Hom.mk'' (fun X => (limit.π _ j : (limit (F ⋙ evaluation R X)) ⟶ _)) (by
        intro X Y f
        dsimp
        simp only [Category.assoc, restrictScalarsLimitIso_inv_map_π]
        exact limMap_π (whiskerLeft F (restriction R f) ≫ (Functor.associator _ _ _).inv) j)
      naturality := sorry }

noncomputable def isLimitLimitCone : IsLimit (limitCone F) :=
  evaluationJointlyReflectsLimits _ _ (fun _ => limit.isLimit _)

instance : HasLimitsOfShape J (PresheafOfModules.{v} R) where
  has_limit F := ⟨_, isLimitLimitCone F⟩

end

end PresheafOfModules
