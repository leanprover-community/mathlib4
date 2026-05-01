/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Product
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTwo

/-!
# Deriving bifunctors using a derivability structure


-/

@[expose] public section

universe v₁₀ v₂₀ v₁ v₂ v₃ u₁₀ u₂₀ u₁ u₂ u₃

namespace CategoryTheory

open Limits Category Functor

-- to be moved
namespace MorphismProperty

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]

lemma prod_isInvertedBy_iff (W₁ : MorphismProperty C₁)
    (W₂ : MorphismProperty C₂) [W₁.ContainsIdentities] [W₂.ContainsIdentities]
    (F : C₁ × C₂ ⥤ D) :
    (W₁.prod W₂).IsInvertedBy F ↔
      (∀ (X₂ : C₂), W₁.IsInvertedBy (Functor.prod' (𝟭 _) ((Functor.const _).obj X₂) ⋙ F)) ∧
      (∀ (X₁ : C₁), W₂.IsInvertedBy (Functor.prod' ((Functor.const _).obj X₁) (𝟭 _) ⋙ F)) :=
  ⟨fun hF ↦ ⟨fun X₂ _ _ _ hf ↦ hF _ ⟨hf, by simpa using W₂.id_mem _⟩,
      fun X₁ _ _ _ hf ↦ hF _ ⟨by simpa using W₁.id_mem _, hf⟩⟩,
    fun ⟨hF₁, hF₂⟩ ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩ ↦ by
      let α : (X₁, X₂) ⟶ (Y₁, X₂) := (f₁, 𝟙 X₂)
      let β : (Y₁, X₂) ⟶ (Y₁, Y₂) := (𝟙 Y₁, f₂)
      have : IsIso (F.map α) := hF₁ X₂ _ hf₁
      have : IsIso (F.map β) := hF₂ Y₁ _ hf₂
      simpa only [← F.map_comp, prod_comp, comp_id, id_comp, α, β] using
        (inferInstance : IsIso (F.map α ≫ F.map β))⟩

end MorphismProperty

variable {C₁₀ : Type u₁₀} {C₂₀ : Type u₂₀}
  {C₁ : Type u₁} {C₂ : Type u₂} {H : Type u₃} {D₁ D₂ : Type*}
  [Category.{v₁₀} C₁₀] [Category.{v₂₀} C₂₀]
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} H]
  [Category D₁] [Category D₂]
  {W₁₀ : MorphismProperty C₁₀} {W₂₀ : MorphismProperty C₂₀}
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ₁ : LocalizerMorphism W₁₀ W₁) (Φ₂ : LocalizerMorphism W₂₀ W₂)
  (F : C₁ ⥤ C₂ ⥤ H)

abbrev Derives₂ : Prop :=
  (Φ₁.prod Φ₂).Derives (uncurry.obj F)

variable [W₁₀.ContainsIdentities] [W₂₀.ContainsIdentities]

lemma derives₂_iff :
    Derives₂ Φ₁ Φ₂ F ↔
      (∀ (X₂₀ : C₂₀), W₁₀.IsInvertedBy (Φ₁.functor ⋙ F.flip.obj (Φ₂.functor.obj X₂₀))) ∧
      (∀ (X₁₀ : C₁₀), W₂₀.IsInvertedBy (Φ₂.functor ⋙ F.obj (Φ₁.functor.obj X₁₀))) := by
  change (W₁₀.prod W₂₀).IsInvertedBy (Φ₁.functor.prod Φ₂.functor ⋙ uncurry.obj F) ↔ _
  simp only [MorphismProperty.prod_isInvertedBy_iff]
  apply and_congr <;> apply forall_congr' <;> intro <;>
    simp [MorphismProperty.IsInvertedBy]

namespace Derives₂

variable {Φ₁ Φ₂ F} (h : Derives₂ Φ₁ Φ₂ F)

lemma isInvertedBy₁ (h : Derives₂ Φ₁ Φ₂ F) (X₂₀ : C₂₀) :
    W₁₀.IsInvertedBy (Φ₁.functor ⋙ F.flip.obj (Φ₂.functor.obj X₂₀)) :=
  ((derives₂_iff _ _ _).1 h).1 _

lemma isInvertedBy₂ (h : Derives₂ Φ₁ Φ₂ F) (X₁₀ : C₁₀) :
    W₂₀.IsInvertedBy (Φ₂.functor ⋙ F.obj (Φ₁.functor.obj X₁₀)) :=
  ((derives₂_iff _ _ _).1 h).2 _

variable [Φ₁.IsLeftDerivabilityStructure] [Φ₂.IsLeftDerivabilityStructure]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities]

include h in
lemma hasLeftDerivedFunctor₂ : F.HasLeftDerivedFunctor₂ W₁ W₂ :=
  Derives.hasLeftDerivedFunctor h

include h in
lemma isIso_of_isLeftDerivabilityStructure
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} [L₁.IsLocalization W₁]
    [L₂.IsLocalization W₂] {LF : D₁ ⥤ D₂ ⥤ H}
    (α : (((whiskeringLeft₂ H).obj L₁).obj L₂).obj LF ⟶ F)
    (X₁ : C₁₀) (X₂ : C₂₀) [LF.IsLeftDerivedFunctor₂ α W₁ W₂] :
    IsIso ((α.app (Φ₁.functor.obj X₁)).app (Φ₂.functor.obj X₂)) :=
  h.isIso_of_isLeftDerivedFunctor (Functor.whiskeringLeft₂Equiv α) ⟨X₁, X₂⟩

end Derives₂

variable {F} in
lemma isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    [W₁.ContainsIdentities] [W₂.ContainsIdentities]
    [Φ₁.IsLeftDerivabilityStructure] [Φ₂.IsLeftDerivabilityStructure]
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} [L₁.IsLocalization W₁]
    [L₂.IsLocalization W₂] {LF : D₁ ⥤ D₂ ⥤ H}
    (α : (((whiskeringLeft₂ H).obj L₁).obj L₂).obj LF ⟶ F)
    (hα : ∀ (X₁₀ : C₁₀) (X₂₀ : C₂₀),
      IsIso ((α.app (Φ₁.functor.obj X₁₀)).app (Φ₂.functor.obj X₂₀))) :
    LF.IsLeftDerivedFunctor₂ α W₁ W₂ := by
  apply (Φ₁.prod Φ₂).isLeftDerivedFunctor_of_isLeftDerivabilityStructure
  rintro ⟨X₁, X₂⟩
  apply hα

end LocalizerMorphism

end CategoryTheory
