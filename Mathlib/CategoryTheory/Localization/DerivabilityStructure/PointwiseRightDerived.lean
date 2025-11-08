/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.GuitartExact.KanExtension
import Mathlib.CategoryTheory.Limits.Final

/-!
# Existence of pointwise right derived functors via derivability structures

In this file, we show how a right derivability structure can be used in
order to construct (pointwise) right derived functors.
Let `Φ` be a right derivability structure from `W₁ : MorphismProperty C₁`
to `W₂ : MorphismProperty C₂`. Let `F : C₂ ⥤ H` be a functor.
Then, the lemma `hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure`
says that `F` has a pointwise right derived functor with respect to `W₂`
if and only if `Φ.functor ⋙ F` has a pointwise right derived functor
with respect to `W₁`. This is essentially the Proposition 5.5 from the article
*Structures de dérivabilité* by Bruno Kahn and Georges Maltsiniotis (there,
it was stated in terms of absolute derived functors).

In particular, if `Φ.functor ⋙ F` inverts `W₁`, it follows that the
right derived functor of `F` with respect to `W₂` exists.

## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

open Limits Category Functor

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

/-- If `Φ` is a localizer morphism from `W₁ : MorphismProperty C₁` to
`W₂ : MorphismProperty C₂`, if `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` are
localization functors for `W₁` and `W₂`, if `F : C₂ ⥤ H` is a functor,
if `F₁ : D₁ ⥤ H` is a right derived functor of `Φ.functor ⋙ F`,
and if `F₂ : D₂ ⥤ H` is a functor equipped with a
natural transformation `α₂ : F ⟶ L₂ ⋙ F₂`, this is the canonical
morphism `F₁ ⟶ Φ.localizedFunctor L₁ L₂ ⋙ F₂`. -/
noncomputable def rightDerivedFunctorComparison :
    F₁ ⟶ Φ.localizedFunctor L₁ L₂ ⋙ F₂ :=
  F₁.rightDerivedDesc α₁ W₁ (Φ.localizedFunctor L₁ L₂ ⋙ F₂)
    (whiskerLeft _ α₂ ≫ (Functor.associator _ _ _).inv ≫
      whiskerRight ((Φ.catCommSq L₁ L₂).iso).hom F₂ ≫ (Functor.associator _ _ _).hom)

@[reassoc]
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

lemma hasPointwiseRightDerivedFunctorAt_iff_of_isRightDerivabilityStructure (X : C₁) :
    (Φ.functor ⋙ F).HasPointwiseRightDerivedFunctorAt W₁ X ↔
      F.HasPointwiseRightDerivedFunctorAt W₂ (Φ.functor.obj X) := by
  let e : W₂.Q.obj _ ≅ (Φ.localizedFunctor W₁.Q W₂.Q).obj _  := ((Φ.catCommSq W₁.Q W₂.Q).iso).app X
  rw [F.hasPointwiseRightDerivedFunctorAt_iff W₂.Q W₂ (Φ.functor.obj X),
    (Φ.functor ⋙ F).hasPointwiseRightDerivedFunctorAt_iff W₁.Q W₁ X,
    TwoSquare.hasPointwiseLeftKanExtensionAt_iff ((Φ.catCommSq W₁.Q W₂.Q).iso).hom,
    Functor.hasPointwiseLeftKanExtensionAt_iff_of_iso W₂.Q F e]

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
      ← F.hasPointwiseRightDerivedFunctorAt_iff_of_mem W₂ R.w R.hw] using hF R.X₁

section

variable [(Φ.functor ⋙ F).HasPointwiseRightDerivedFunctor W₁]
  [F₂.IsRightDerivedFunctor α₂ W₂]

instance : IsIso (Φ.rightDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂) := by
  have : F.HasPointwiseRightDerivedFunctor W₂ := by
    rw [Φ.hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure]
    infer_instance
  dsimp only [rightDerivedFunctorComparison]
  rw [← isRightDerivedFunctor_iff_isIso_rightDerivedDesc,
    isRightDerivedFunctor_iff_isLeftKanExtension]
  exact ((F₂.isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor α₂ W₂).compTwoSquare
    ((Φ.catCommSq L₁ L₂).iso).hom).isLeftKanExtension

lemma isIso_α_iff_of_isRightDerivabilityStructure (X : C₁) :
    IsIso (α₁.app X) ↔ IsIso (α₂.app (Φ.functor.obj X)) := by
  rw [← isIso_comp_right_iff (α₁.app X)
    ((Φ.rightDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂).app (L₁.obj X)),
    rightDerivedFunctorComparison_fac_app, isIso_comp_right_iff]

end

end LocalizerMorphism

end CategoryTheory
