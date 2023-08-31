import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Limits

universe v₃ v₂ v₁ v u₃ u₂ u₁ u

namespace CategoryTheory

-- to be moved...
namespace Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : Type u₃} [Category.{v₃} J] {K : J ⥤ C}

namespace IsLimit

@[nolint unusedArguments]
def comparison {c : Cone K} (_ : IsLimit c) (F : C ⥤ D)
  {c' : Cone (K ⋙ F)} (hc' : IsLimit c') : F.obj c.pt ⟶ c'.pt :=
  hc'.lift (F.mapCone c)

variable {c : Cone K} (hc : IsLimit c) (F : C ⥤ D) {c' : Cone (K ⋙ F)} (hc' : IsLimit c')

@[reassoc (attr := simp)]
lemma comparison_π (j : J) :
    comparison hc F hc' ≫ c'.π.app j = F.map (c.π.app j) :=
  hc'.fac _ _

variable [PreservesLimit K F]

def comparisonIso : F.obj c.pt ≅ c'.pt :=
  IsLimit.conePointUniqueUpToIso (isLimitOfPreserves F hc) hc'

@[simp]
lemma comparisonIso_hom :
    (comparisonIso hc F hc').hom = comparison hc F hc' := rfl

@[reassoc (attr := simp)]
lemma comparisonIso_hom_inv_id :
    comparison hc F hc' ≫ (comparisonIso hc F hc').inv = 𝟙 _ :=
  (comparisonIso hc F hc').hom_inv_id

@[reassoc (attr := simp)]
lemma comparisonIso_inv_hom_id :
     (comparisonIso hc F hc').inv ≫ comparison hc F hc' = 𝟙 _ :=
  (comparisonIso hc F hc').inv_hom_id

@[reassoc (attr := simp)]
lemma comparisonInv_inv_map_π (j : J) :
    (comparisonIso hc F hc').inv ≫ F.map (c.π.app j) = c'.π.app j :=
  (isLimitOfPreserves F hc).fac _ _

end IsLimit

variable (K) (F : C ⥤ D) [HasLimit K] [HasLimit (K ⋙ F)]

namespace limit

noncomputable def comparison : F.obj (limit K) ⟶ limit (K ⋙ F) :=
  IsLimit.comparison (limit.isLimit K) F (limit.isLimit (K ⋙ F))

@[reassoc (attr := simp)]
lemma comparison_π (j : J) :
    comparison K F ≫ limit.π (K ⋙ F) j = F.map (limit.π K j) :=
  IsLimit.comparison_π _ _ _ _

variable [PreservesLimit K F]

instance : IsIso (comparison K F) :=
  IsIso.of_iso (IsLimit.comparisonIso (limit.isLimit K) F (limit.isLimit (K ⋙ F)))

@[reassoc (attr := simp)]
lemma inv_comparisonInv_map_π (j : J) :
    inv (comparison K F) ≫ F.map (limit.π K j) = limit.π (K ⋙ F) j := by
  simp only [← cancel_epi (comparison K F), IsIso.hom_inv_id_assoc, comparison_π]

@[simps!]
noncomputable def comparisonIso : F.obj (limit K) ≅ limit (K ⋙ F) := asIso (comparison K F)

end limit

end Limits

end CategoryTheory

namespace PresheafOfModules

open CategoryTheory Category Limits

-- let us not care too much about universes for now...

instance {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S) :
  PreservesLimitsOfSize (ModuleCat.restrictScalars f) := sorry

instance {R : Type u₁} [Ring R] : HasLimitsOfSize (ModuleCat.{v} R) := sorry

section

variable {R : Type u₁} {S : Type u₃} [Ring R] [Ring S] (f : R →+* S)
  {J : Type u₂} [Category.{v₂} J] (F : J ⥤ ModuleCat.{v} S)

/-noncomputable def restrictScalarsLimitIso :
    (ModuleCat.restrictScalars.{v} f).obj (limit F) ≅ limit (F ⋙ ModuleCat.restrictScalars.{v} f) :=
  limit.comparisonIso F (ModuleCat.restrictScalars.{v} f)

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
  dsimp only [restrictScalarsLimitIso]
  simp-/

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
  map {X Y} f := limMap (whiskerLeft F (restriction R f)) ≫ (limit.comparisonIso (F ⋙ evaluation R Y) ((ModuleCat.restrictScalars (R.map f)))).inv
  map_id := fun X => by
    dsimp
    simp only [← cancel_mono (limit.comparisonIso (F ⋙ evaluation R X) ((ModuleCat.restrictScalars (R.map (𝟙 X))))).hom,
      assoc, Iso.inv_hom_id, comp_id]
    apply limit.hom_ext
    intro j
    simp only [assoc, limit.comparisonIso_hom, limit.comparison_π, limit.inv_comparisonInv_map_π]
    erw [limMap_π]
    simp only [← cancel_mono ((ModuleCat.restrictScalarsId' (R.map (𝟙 X)) (R.map_id X)).hom.app ((F.obj j).obj X)),
      Functor.comp_obj, evaluation_obj, whiskerLeft_app, restriction_app_id,
      Functor.id_obj, assoc, Iso.inv_hom_id_app, comp_id, CategoryTheory.Functor.map_id, NatTrans.naturality,
      Functor.id_map, Iso.inv_hom_id_app_assoc]
  map_comp {X Y Z} f g := by
    dsimp
    rw [← cancel_mono (limit.comparison (F ⋙ evaluation R Z) (ModuleCat.restrictScalars (R.map (f ≫ g))))]
    simp only [assoc, IsIso.inv_hom_id, comp_id, Functor.map_comp]
    apply limit.hom_ext
    intro j
    simp only [limMap_π, Functor.map_comp, assoc]
    erw [limit.comparison_π, restriction_app_comp]
    simp only [evaluation_obj, Functor.comp_obj, Functor.map_comp, ← NatTrans.naturality]
    dsimp
    simp only [← Functor.map_comp_assoc, limit.inv_comparisonInv_map_π]
    erw [limMap_π, Functor.map_comp_assoc, limit.inv_comparisonInv_map_π_assoc,
      limMap_π_assoc]
    rfl

noncomputable def limitCone : Cone F where
  pt := mk'' (limitBundledMkStruct F)
  π :=
    { app := fun j => Hom.mk'' (fun X => limit.π (F ⋙ evaluation R X) j) (fun X Y f => by
        dsimp
        simp only [assoc, limit.inv_comparisonInv_map_π]
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
