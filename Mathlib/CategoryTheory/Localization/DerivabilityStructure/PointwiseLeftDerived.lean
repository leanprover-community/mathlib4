/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Existence of pointwise left derived functors via derivability structures

In this file, we show how a left derivability structure can be used in
order to construct (pointwise) left derived functors.
Let `Φ` be a left derivability structure from `W₁ : MorphismProperty C₁`
to `W₂ : MorphismProperty C₂`. Let `F : C₂ ⥤ H` be a functor.
Then, the lemma `hasPointwiseLeftDerivedFunctor_iff_of_isLeftDerivabilityStructure`
says that `F` has a pointwise left derived functor with respect to `W₂`
if and only if `Φ.functor ⋙ F` has a pointwise left derived functor
with respect to `W₁`. This is essentially the Proposition 5.5 from the article
*Structures de dérivabilité* by Bruno Kahn and Georges Maltsiniotis (there,
it was stated in terms of absolute derived functors).

In particular, if `Φ.functor ⋙ F` inverts `W₁`, it follows that the
left derived functor of `F` with respect to `W₂` exists.

This file contains the dual results to those obtained in the file
`Mathlib/CategoryTheory/Localization/DerivabilityStructure/PointwiseRightDerived.lean`.

## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

variable {C₁ C₂ H D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* H]
  [Category* D₁] [Category* D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂) (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  (F : C₂ ⥤ H) (F₁ : D₁ ⥤ H) (α₁ : L₁ ⋙ F₁ ⟶ Φ.functor ⋙ F)
  (F₂ : D₂ ⥤ H) (α₂ : L₂ ⋙ F₂ ⟶ F)
  [F₁.IsLeftDerivedFunctor α₁ W₁]

/-- If `Φ` is a localizer morphism from `W₁ : MorphismProperty C₁` to
`W₂ : MorphismProperty C₂`, if `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` are
localization functors for `W₁` and `W₂`, if `F : C₂ ⥤ H` is a functor,
if `F₁ : D₁ ⥤ H` is a left derived functor of `Φ.functor ⋙ F`,
and if `F₂ : D₂ ⥤ H` is a functor equipped with a
natural transformation `α₂ : L₂ ⋙ F₂ ⟶ F`, this is the canonical
morphism `Φ.localizedFunctor L₁ L₂ ⋙ F₂ ⟶ F₁`. -/
noncomputable def leftDerivedFunctorComparison :
    Φ.localizedFunctor L₁ L₂ ⋙ F₂ ⟶ F₁ :=
  F₁.leftDerivedLift α₁ W₁ (Φ.localizedFunctor L₁ L₂ ⋙ F₂)
    ((associator _ _ _).inv ≫ whiskerRight ((Φ.catCommSq L₁ L₂).iso).inv F₂ ≫
      (associator _ _ _).hom ≫ whiskerLeft Φ.functor α₂)

@[reassoc]
lemma leftDerivedFunctorComparison_fac :
    whiskerLeft _ (Φ.leftDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂) ≫ α₁ =
      (associator _ _ _).inv ≫ whiskerRight ((Φ.catCommSq L₁ L₂).iso).inv F₂ ≫
        (associator _ _ _).hom ≫ whiskerLeft Φ.functor α₂ := by
  dsimp only [leftDerivedFunctorComparison]
  rw [Functor.leftDerived_fac]

@[reassoc (attr := simp)]
lemma leftDerivedFunctorComparison_fac_app (X : C₁) :
    (Φ.leftDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂).app (L₁.obj X) ≫ α₁.app X =
      F₂.map (((Φ.catCommSq L₁ L₂).iso).inv.app X) ≫ α₂.app (Φ.functor.obj X) := by
  simpa using congr_app (Φ.leftDerivedFunctorComparison_fac L₁ L₂ F F₁ α₁ F₂ α₂) X

variable [Φ.IsLeftDerivabilityStructure]

set_option backward.isDefEq.respectTransparency.types false in
lemma hasPointwiseLeftDerivedFunctorAt_iff_of_isLeftDerivabilityStructure (X : C₁) :
    (Φ.functor ⋙ F).HasPointwiseLeftDerivedFunctorAt W₁ X ↔
      F.HasPointwiseLeftDerivedFunctorAt W₂ (Φ.functor.obj X) := by
  let e : W₂.Q.obj _ ≅ (Φ.localizedFunctor W₁.Q W₂.Q).obj _ := ((Φ.catCommSq W₁.Q W₂.Q).iso).app X
  rw [F.hasPointwiseLeftDerivedFunctorAt_iff W₂.Q W₂ (Φ.functor.obj X),
    (Φ.functor ⋙ F).hasPointwiseLeftDerivedFunctorAt_iff W₁.Q W₁ X,
    TwoSquare.hasPointwiseRightKanExtensionAt_iff ((Φ.catCommSq W₁.Q W₂.Q).iso).inv,
    Functor.hasPointwiseRightKanExtensionAt_iff_of_iso W₂.Q F e]

lemma hasPointwiseLeftDerivedFunctor_iff_of_isLeftDerivabilityStructure :
    F.HasPointwiseLeftDerivedFunctor W₂ ↔
      ((Φ.functor ⋙ F).HasPointwiseLeftDerivedFunctor W₁) := by
  constructor
  · intro hF X₁
    rw [hasPointwiseLeftDerivedFunctorAt_iff_of_isLeftDerivabilityStructure]
    apply hF
  · intro hF X₂
    have R : Φ.LeftResolution X₂ := Classical.arbitrary _
    simpa only [hasPointwiseLeftDerivedFunctorAt_iff_of_isLeftDerivabilityStructure,
      ← F.hasPointwiseLeftDerivedFunctorAt_iff_of_mem W₂ R.w R.hw] using hF R.X₁

section

variable [(Φ.functor ⋙ F).HasPointwiseLeftDerivedFunctor W₁]
  [F₂.IsLeftDerivedFunctor α₂ W₂]

instance : IsIso (Φ.leftDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂) := by
  have : F.HasPointwiseLeftDerivedFunctor W₂ := by
    rw [Φ.hasPointwiseLeftDerivedFunctor_iff_of_isLeftDerivabilityStructure]
    infer_instance
  dsimp only [leftDerivedFunctorComparison]
  rw [← isLeftDerivedFunctor_iff_isIso_leftDerivedLift,
    isLeftDerivedFunctor_iff_isRightKanExtension]
  exact ((F₂.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor α₂ W₂).compTwoSquare
    ((Φ.catCommSq L₁ L₂).iso).inv).isRightKanExtension

lemma isIso_iff_of_isLeftDerivabilityStructure (X : C₁) :
    IsIso (α₁.app X) ↔ IsIso (α₂.app (Φ.functor.obj X)) := by
  rw [← isIso_comp_left_iff
    ((Φ.leftDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂).app (L₁.obj X)),
    leftDerivedFunctorComparison_fac_app, isIso_comp_left_iff]

end

end LocalizerMorphism

end CategoryTheory
