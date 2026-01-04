/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.PointwiseRightDerived

/-!
# Deriving functors using a derivability structure

Let `Φ : LocalizerMorphism W₁ W₂` be a localizer morphism between classes
of morphisms on categories `C₁` and `C₂`. Let `F : C₂ ⥤ H`.
When `Φ` is a left or right derivability structure, it allows to derive
the functor `F` (with respect to `W₂`) when `Φ.functor ⋙ F : C₁ ⥤ H`
inverts `W₁` (this is the most favorable case when we can apply the lemma
`hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure`).
We define `Φ.Derives F` as an abbreviation for `W₁.IsInvertedBy (Φ.functor ⋙ F)`.

When `h : Φ.Derives F` holds and `Φ` is a right derivability structure,
we show that `F` has a right derived functor with respect to `W₂`.
Under this assumption, if `L₂ : C₂ ⥤ D₂` is a localization functor
for `W₂`, then a functor `RF : D₂ ⥤ H` equipped with a natural
transformation `α : F ⟶ L₂ ⋙ RF` is the right derived functor of `F` iff
for any `X₁ : C₁`, the map `α.app (Φ.functor.obj X₁)` is an isomorphism.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Limits Category

variable {C₁ : Type u₁} {C₂ : Type u₂} {H : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} H]
  {D₂ : Type u₄} [Category.{v₄} D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂) (F : C₂ ⥤ H)

/-- Given a localizer morphism `Φ : LocalizerMorphism W₁ W₂` between
morphism properties on `C₁` and `C₂`, and a functor `C₂ ⥤ H`, this
is the property that `W₁` is inverted by `Φ.functor ⋙ F`.
In case `Φ` is a (left/right) derivability structure, this allows
the construction of a derived functor for `F` relatively to `W₂`. -/
abbrev Derives : Prop := W₁.IsInvertedBy (Φ.functor ⋙ F)

namespace Derives

variable {Φ F} (h : Φ.Derives F) [Φ.IsRightDerivabilityStructure]

include h

lemma hasPointwiseRightDerivedFunctor : F.HasPointwiseRightDerivedFunctor W₂ := by
  rw [hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure Φ F]
  exact Functor.hasPointwiseRightDerivedFunctor_of_inverts _ h

section

variable {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂] {RF : D₂ ⥤ H} (α : F ⟶ L₂ ⋙ RF)

lemma isIso (X₁ : C₁) [RF.IsRightDerivedFunctor α W₂] :
    IsIso (α.app (Φ.functor.obj X₁)) := by
  let G : W₁.Localization ⥤ H := Localization.lift (Φ.functor ⋙ F) h W₁.Q
  let eG := Localization.Lifting.iso W₁.Q W₁ (Φ.functor ⋙ F) G
  have := Functor.isRightDerivedFunctor_of_inverts W₁ G eG
  have := (Φ.functor ⋙ F).hasPointwiseRightDerivedFunctor_of_inverts h
  rw [← Φ.isIso_iff_of_isRightDerivabilityStructure W₁.Q L₂ F G eG.inv RF α]
  infer_instance

lemma isRightDerivedFunctor_of_isIso (hα : ∀ (X₁ : C₁), IsIso (α.app (Φ.functor.obj X₁))) :
    RF.IsRightDerivedFunctor α W₂ := by
  have := h.hasPointwiseRightDerivedFunctor
  have := h.isIso (F.totalRightDerivedUnit L₂ W₂)
  have := Φ.essSurj_of_hasRightResolutions L₂
  let φ := (F.totalRightDerived L₂ W₂).rightDerivedDesc (F.totalRightDerivedUnit L₂ W₂) W₂ RF α
  have hφ : F.totalRightDerivedUnit L₂ W₂ ≫ Functor.whiskerLeft L₂ φ = α :=
    (F.totalRightDerived L₂ W₂).rightDerived_fac (F.totalRightDerivedUnit L₂ W₂) W₂ RF α
  have : IsIso φ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Y₂
    rw [NatTrans.isIso_app_iff_of_iso φ ((Φ.functor ⋙ L₂).objObjPreimageIso Y₂).symm]
    dsimp
    simp only [← hφ, NatTrans.comp_app, Functor.whiskerLeft_app, isIso_comp_left_iff] at hα
    infer_instance
  rw [← Functor.isRightDerivedFunctor_iff_of_iso (F.totalRightDerivedUnit L₂ W₂) α W₂
    (asIso φ) (by cat_disch)]
  infer_instance

lemma isRightDerivedFunctor_iff_isIso :
    RF.IsRightDerivedFunctor α W₂ ↔ ∀ (X₁ : C₁), IsIso (α.app (Φ.functor.obj X₁)) :=
  ⟨fun _ _ ↦ h.isIso α _, h.isRightDerivedFunctor_of_isIso α⟩

end

end Derives

end LocalizerMorphism

end CategoryTheory
