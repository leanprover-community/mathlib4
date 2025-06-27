/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.PointwiseRightDerived
import Mathlib.CategoryTheory.Functor.Derived.Opposite

/-!
# Deriving functors using a derivability structure

Let `Φ : LocalizerMorphism W₁ W₂` be a localizer morphism between classes
of morphisms on categories `C₁` and `C₂`. Let `F : C₂ ⥤ H`.
When `Φ` is a left or right derivability structure, it allows to derive
the functor `F` (with respect to `W₂`) when `Φ.functor ⋙ F : C₁ ⥤ H`
inverts `W₁` (this is the most favorable case when we can apply the lemma
`hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure`).
We derive `Φ.Derives F` as an abbreviation for `W₁.IsInvertedBy (Φ.functor ⋙ F)`.

When `h : Φ.Derives F` holds and `Φ` is a right derivability structure,
we show that `F` has a right derived functor with respect to `W₂` and
then when `L₂ : C₂ ⥤ D₂` is a localization functor for `W₂`, then
a functor `RF : D₂ ⥤ H` equipped with a natural transformation
`α : F ⟶ L₂ ⋙ RF` is the right derived functor iff for any `X₁ : C₁`,
the map `α.app (Φ.functor.obj X₁)` is an isomorphism.

-/

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

variable {Φ F} (h : Φ.Derives F)

include h in
protected lemma op : Φ.op.Derives F.op := fun _ _ f hf ↦ by
  have := h f.unop hf
  dsimp at this ⊢
  infer_instance

include h in
lemma hasPointwiseRightDerivedFunctor [Φ.IsRightDerivabilityStructure] :
    F.HasPointwiseRightDerivedFunctor W₂ := by
  rw [hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure Φ F]
  exact Functor.hasPointwiseRightDerivedFunctor_of_inverts _ h

include h in
lemma hasLeftDerivedFunctor [Φ.IsLeftDerivabilityStructure] :
    F.HasLeftDerivedFunctor W₂ := by
  rw [Functor.hasLeftDerivedFunctor_iff_op]
  have := h.op.hasPointwiseRightDerivedFunctor
  infer_instance

section

variable {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂] {RF : D₂ ⥤ H} (α : F ⟶ L₂ ⋙ RF)

include h in
lemma isIso_of_isRightDerivabilityStructure
    [Φ.IsRightDerivabilityStructure] (X₁ : C₁) [RF.IsRightDerivedFunctor α W₂] :
    IsIso (α.app (Φ.functor.obj X₁)) := by
  let G : W₁.Localization ⥤ H := Localization.lift (Φ.functor ⋙ F) h W₁.Q
  let eG := Localization.Lifting.iso W₁.Q W₁ (Φ.functor ⋙ F) G
  have := Functor.isRightDerivedFunctor_of_inverts W₁ G eG
  have := (Φ.functor ⋙ F).hasPointwiseRightDerivedFunctor_of_inverts h
  rw [← Φ.isIso_α_iff_of_isRightDerivabilityStructure W₁.Q L₂ F G eG.inv RF α]
  infer_instance

lemma of_isIso_app_functor_obj (hα : ∀ (X₁ : C₁), IsIso (α.app (Φ.functor.obj X₁))) :
    Φ.Derives F := by
  intro X₁ X₂ f hf
  have := Localization.inverts L₂ W₂ _ (Φ.map f hf)
  rw [Functor.comp_map, ← isIso_comp_right_iff _ (α.app _), α.naturality (Φ.functor.map f),
    isIso_comp_left_iff, Functor.comp_map]
  infer_instance

end

section

variable {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂] {LF : D₂ ⥤ H} (α : L₂ ⋙ LF ⟶ F)

include h in
lemma isIso_of_isLeftDerivabilityStructure
    [Φ.IsLeftDerivabilityStructure] (X₁ : C₁) [LF.IsLeftDerivedFunctor α W₂] :
    IsIso (α.app (Φ.functor.obj X₁)) := by
  have := h.op.isIso_of_isRightDerivabilityStructure (RF := LF.op) (F := F.op)
    (L₂ := L₂.op) (NatTrans.op α) (Opposite.op X₁)
  rwa [← isIso_unop_iff] at this

lemma of_isIso_app_functor_obj' (hα : ∀ (X₁ : C₁), IsIso (α.app (Φ.functor.obj X₁))) :
    Φ.Derives F := by
  intro X₁ X₂ f hf
  have := Localization.inverts L₂ W₂ _ (Φ.map f hf)
  rw [Functor.comp_map, ← isIso_comp_left_iff (α.app _),
    ← α.naturality (Φ.functor.map f), isIso_comp_right_iff, Functor.comp_map]
  infer_instance

end

end Derives

lemma isRightDerivedFunctor_of_isRightDerivabilityStructure
    [Φ.IsRightDerivabilityStructure]
    {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂] {RF : D₂ ⥤ H}
    (α : F ⟶ L₂ ⋙ RF) (hα : ∀ (X₁ : C₁), IsIso (α.app (Φ.functor.obj X₁))) :
    RF.IsRightDerivedFunctor α W₂ := by
  have h := Derives.of_isIso_app_functor_obj α hα
  have := h.hasPointwiseRightDerivedFunctor
  have := h.isIso_of_isRightDerivabilityStructure (F.totalRightDerivedUnit L₂ W₂)
  have := Φ.essSurj_of_hasRightResolutions L₂
  let φ := (F.totalRightDerived L₂ W₂).rightDerivedDesc (F.totalRightDerivedUnit L₂ W₂) W₂ RF α
  have hφ : F.totalRightDerivedUnit L₂ W₂ ≫ whiskerLeft L₂ φ = α :=
    (F.totalRightDerived L₂ W₂).rightDerived_fac (F.totalRightDerivedUnit L₂ W₂) W₂ RF α
  have : IsIso φ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Y₂
    rw [NatTrans.isIso_app_iff_of_iso φ ((Φ.functor ⋙ L₂).objObjPreimageIso Y₂).symm]
    dsimp
    simp only [← hφ, NatTrans.comp_app, whiskerLeft_app, isIso_comp_left_iff] at hα
    infer_instance
  rw [← Functor.isRightDerivedFunctor_iff_of_iso (F.totalRightDerivedUnit L₂ W₂) α W₂
    (asIso φ) (by aesop)]
  infer_instance

variable {F} in
lemma isLeftDerivedFunctor_of_isLeftDerivabilityStructure
    [Φ.IsLeftDerivabilityStructure]
    {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂] {LF : D₂ ⥤ H}
    (α : L₂ ⋙ LF ⟶ F) (hα : ∀ (X₁ : C₁), IsIso (α.app (Φ.functor.obj X₁))) :
    LF.IsLeftDerivedFunctor α W₂ := by
  rw [Functor.isLeftDerivedFunctor_iff_op]
  exact Φ.op.isRightDerivedFunctor_of_isRightDerivabilityStructure
    (F := F.op) (RF := LF.op) (L₂ := L₂.op)
    (α := NatTrans.op α) (fun X₁ ↦ by dsimp; infer_instance)

end LocalizerMorphism

end CategoryTheory
