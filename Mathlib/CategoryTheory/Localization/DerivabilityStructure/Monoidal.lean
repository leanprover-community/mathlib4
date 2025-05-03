/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
import Mathlib.CategoryTheory.Monoidal.Derived

/-!
# Deriving a monoidal structure using a left derivability structure

-/

namespace CategoryTheory

namespace NatTrans

lemma isIso_app_app_iff_of_iso
    {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D] {F G : C₁ ⥤ C₂ ⥤ D}
    (τ : F ⟶ G) {X₁ Y₁ : C₁} (e₁ : X₁ ≅ Y₁) {X₂ Y₂ : C₂} (e₂ : X₂ ≅ Y₂) :
    IsIso ((τ.app X₁).app X₂) ↔ IsIso ((τ.app Y₁).app Y₂) := by
  apply (MorphismProperty.isomorphisms D).arrow_mk_iso_iff
  refine Arrow.isoMk ((F.mapIso e₁).app X₂ ≪≫ (F.obj Y₁).mapIso e₂)
    ((G.mapIso e₁).app X₂ ≪≫ (G.obj Y₁).mapIso e₂) ?_
  dsimp
  rw [Category.assoc, naturality, ← NatTrans.comp_app_assoc, naturality,
    NatTrans.comp_app_assoc]

end NatTrans

open MonoidalCategory

namespace LocalizerMorphism

variable {C₀ C D : Type*} [Category C₀] [Category C] [Category D]
  [MonoidalCategory C₀] [MonoidalCategory C]
  {W₀ : MorphismProperty C₀} {W : MorphismProperty C} (Φ : LocalizerMorphism W₀ W)
  [W₀.ContainsIdentities] [W.ContainsIdentities]
  [Φ.IsLeftDerivabilityStructure] [Φ.functor.Monoidal] (L : C ⥤ D)

abbrev DerivesMonoidalStructure [L.IsLocalization W] : Prop :=
  Derives₂ Φ Φ ((Functor.postcompose₂.obj L).obj (curriedTensor C))

namespace DerivesMonoidalStructure

variable [L.IsLocalization W] (h : Φ.DerivesMonoidalStructure L)

/-open DerivedMonoidal in
include h in
lemma HasDerivedMonoidalCategory : L.HasDerivedMonoidalCategory W := by
  have : (curriedTensor C ⋙ (whiskeringRight C C (DerivedMonoidal L W)).obj
    (toDerivedMonoidal L W)).HasLeftDerivedFunctor₂ W W := h.hasLeftDerivedFunctor₂
  have : (bifunctor L W).IsLeftDerivedFunctor₂ (counit L W) W W := inferInstance
  have h (X₁ X₂ : C) {X₁₀ X₂₀ : C₀} (e₁ : X₁ ≅ Φ.functor.obj X₁₀)
    (e₂ : X₂ ≅ Φ.functor.obj X₂₀) :
      IsIso (((counit L W).app X₁).app X₂) := by
    rw [NatTrans.isIso_app_app_iff_of_iso (counit L W) e₁ e₂]
    apply h.isIso_of_isLeftDerivabilityStructure (counit L W)
  exact {
    curriedTensor_hasLeftDerivedFunctor₂ := by infer_instance
    bifunctorFlipObjUnit_isLeftDerivedFunctor := by
      apply Φ.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
      intro X₀
      exact h _ _ (Iso.refl _) (Functor.Monoidal.εIso Φ.functor)
    bifunctorObjUnit_isLeftDerivedFunctor := by
      apply Φ.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
      intro X₀
      exact h _ _ (Functor.Monoidal.εIso Φ.functor) (Iso.refl _)
    trifunctor₁₂_isLeftDerivedFunctor₃ := sorry
    trifunctor₂₃_isLeftDerivedFunctor₃ := sorry
    quadrifunctorRight_isLeftDerivedFunctor₄ := sorry
  }-/

end DerivesMonoidalStructure

end LocalizerMorphism

end CategoryTheory
