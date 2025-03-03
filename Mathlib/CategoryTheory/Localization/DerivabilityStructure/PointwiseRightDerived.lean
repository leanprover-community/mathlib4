/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Limits.Final

/-!
# Existence of pointwise right derived functors via derivability structures



## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

lemma Limits.hasColimit_iff_of_iso {J C : Type*} [Category J] [Category C]
    {F G : J ⥤ C} (e : F ≅ G) : HasColimit F ↔ HasColimit G := by
  constructor
  · intro
    exact hasColimitOfIso e.symm
  · intro
    exact hasColimitOfIso e

open Limits Category

variable {C₁ : Type u₁} {C₂ : Type u₂} {H : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} H]
  {D₁ : Type u₄} {D₂ : Type u₅}
  [Category.{v₄} D₁] [Category.{v₅} D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂) (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  (F : C₂ ⥤ H) (F₁ : D₁ ⥤ H) (α₁ : Φ.functor ⋙ F ⟶ L₁ ⋙ F₁)
  (F₂ : D₂ ⥤ H) (α₂ : F ⟶ L₂ ⋙ F₂)
  [F₁.IsRightDerivedFunctor α₁ W₁]

noncomputable def rightDerivedFunctorComparison :
    F₁ ⟶ Φ.localizedFunctor L₁ L₂ ⋙ F₂ :=
  F₁.rightDerivedDesc α₁ W₁ (Φ.localizedFunctor L₁ L₂ ⋙ F₂)
    (whiskerLeft _ α₂ ≫ (Functor.associator _ _ _).inv ≫
      whiskerRight ((Φ.catCommSq L₁ L₂).iso).hom F₂ ≫ (Functor.associator _ _ _).hom)

lemma rightDerivedFunctorComparison_fac :
    α₁ ≫ whiskerLeft _ (Φ.rightDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂) =
      whiskerLeft Φ.functor α₂ ≫ ((Functor.associator _ _ _).inv ≫
      whiskerRight ((Φ.catCommSq L₁ L₂).iso).hom F₂ ≫ (Functor.associator _ _ _).hom) := by
  dsimp only [rightDerivedFunctorComparison]
  rw [Functor.rightDerived_fac]

@[reassoc (attr := simp)]
lemma rightDerivedFunctorComparison_fac_app (X : C₁) :
    α₁.app X ≫ (Φ.rightDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂).app (L₁.obj X) =
      α₂.app (Φ.functor.obj X) ≫ F₂.map (((Φ.catCommSq L₁ L₂).iso).hom.app X) := by
  simpa using congr_app (Φ.rightDerivedFunctorComparison_fac L₁ L₂ F F₁ α₁ F₂ α₂) X

variable [Φ.IsRightDerivabilityStructure]

-- similar to Kahn-Maltsiniotis Lemme 5.5
lemma hasPointwiseRightDerivedFunctorAt_iff_of_isRightDerivabilityStructure (X : C₁) :
    (Φ.functor ⋙ F).HasPointwiseRightDerivedFunctorAt W₁ X ↔
      F.HasPointwiseRightDerivedFunctorAt W₂ (Φ.functor.obj X) := by
  let e : W₂.Q.obj _ ≅ (Φ.localizedFunctor W₁.Q W₂.Q).obj _  := ((Φ.catCommSq W₁.Q W₂.Q).iso).app X
  rw [F.hasPointwiseRightDerivedFunctorAt_iff W₂.Q W₂ (Φ.functor.obj X),
    (Φ.functor ⋙ F).hasPointwiseRightDerivedFunctorAt_iff W₁.Q W₁ X]
  rw [Functor.hasPointwiseLeftKanExtensionAt_iff_of_iso W₂.Q F e]
  dsimp [Functor.HasPointwiseLeftKanExtensionAt]
  let w : TwoSquare _ _ _ _ := ((Φ.catCommSq W₁.Q W₂.Q).iso).hom
  rw [← Functor.Final.hasColimit_comp_iff (w.costructuredArrowRightwards (W₁.Q.obj X))]
  apply hasColimit_iff_of_iso
  apply Iso.refl

lemma hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure :
    F.HasPointwiseRightDerivedFunctor W₂ ↔
      ((Φ.functor ⋙ F).HasPointwiseRightDerivedFunctor W₁) := by
  constructor
  · intro hF X₁
    rw [hasPointwiseRightDerivedFunctorAt_iff_of_isRightDerivabilityStructure]
    apply hF
  · intro hF X₂
    have R : Φ.RightResolution X₂ := Classical.arbitrary _
    simpa only [hasPointwiseRightDerivedFunctorAt_iff_of_isRightDerivabilityStructure,
      ← F.hasPointwiseRightDerivedFunctorAt_iff_of_mem W₂ R.w R.hw ] using hF R.X₁

variable [F₂.IsRightDerivedFunctor α₂ W₂]

instance [(Φ.functor ⋙ F).HasPointwiseRightDerivedFunctor W₁] :
    IsIso (Φ.rightDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂) := by
  suffices ∀ Y, IsIso ((rightDerivedFunctorComparison Φ L₁ L₂ F F₁ α₁ F₂ α₂).app Y) from
    NatIso.isIso_of_isIso_app _
  intro Y
  have : (F.HasPointwiseRightDerivedFunctor W₂) := by
    rw [Φ.hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure]
    infer_instance
  let w : TwoSquare _ _ _ _ := ((Φ.catCommSq L₁ L₂).iso).hom
  have : w.GuitartExact := Φ.guitartExact_of_isRightDerivabilityStructure L₁ L₂
  have hF₁ := (F₁.isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor α₁ W₁) Y
  have hF₂ := (F₂.isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor α₂ W₂)
      ((Φ.localizedFunctor L₁ L₂).obj Y)
  have hF₂' := (Functor.Final.isColimitWhiskerEquiv (w.costructuredArrowRightwards Y) _).symm hF₂
  have : (Φ.rightDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂).app Y =
      (IsColimit.coconePointUniqueUpToIso hF₁ hF₂').hom := hF₁.hom_ext (fun φ => by
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    dsimp
    simp only [w, assoc, NatTrans.naturality, Functor.comp_obj, Functor.comp_map,
      rightDerivedFunctorComparison_fac_app_assoc, Functor.map_comp])
  rw [this]
  infer_instance

lemma isIso_α_iff_of_isRightDerivabilityStructure
    [(Φ.functor ⋙ F).HasPointwiseRightDerivedFunctor W₁] (X : C₁) :
    IsIso (α₁.app X) ↔ IsIso (α₂.app (Φ.functor.obj X)) := by
  rw [← isIso_comp_right_iff (α₁.app X)
    ((Φ.rightDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂).app (L₁.obj X)),
    rightDerivedFunctorComparison_fac_app, isIso_comp_right_iff]
/-
#check hasPointwiseRightDerivedFunctorAt_iff_of_isRightDerivabilityStructure
CategoryTheory.LocalizerMorphism.hasPointwiseRightDerivedFunctorAt_iff_of_isRightDerivabilityStructure.{v₁, v₂, v₃, u₁,
    u₂, u₃}
  {C₁ : Type u₁} {C₂ : Type u₂} {H : Type u₃} [Category.{v₁, u₁} C₁] [Category.{v₂, u₂} C₂] [Category.{v₃, u₃} H]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂} (Φ : LocalizerMorphism W₁ W₂) (F : C₂ ⥤ H)
  [Φ.IsRightDerivabilityStructure] (X : C₁) :
  (Φ.functor ⋙ F).HasPointwiseRightDerivedFunctorAt W₁ X ↔ F.HasPointwiseRightDerivedFunctorAt W₂ (Φ.functor.obj X)
  -/
end LocalizerMorphism

end CategoryTheory
