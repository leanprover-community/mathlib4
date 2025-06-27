/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.DerivesThree
import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedFour

/-!
# Deriving quadrifunctors using a derivability structure


-/

namespace CategoryTheory

open Limits Category

variable {C₁₀ C₂₀ C₃₀ C₄₀ C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ H : Type*}
  [Category C₁₀] [Category C₂₀] [Category C₃₀] [Category C₄₀]
  [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  [Category D₁] [Category D₂] [Category D₃] [Category D₄] [Category H]
  {W₁₀ : MorphismProperty C₁₀} {W₂₀ : MorphismProperty C₂₀} {W₃₀ : MorphismProperty C₃₀}
  {W₄₀ : MorphismProperty C₄₀} {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {W₃ : MorphismProperty C₃} {W₄ : MorphismProperty C₄}

namespace LocalizerMorphism

variable (Φ₁ : LocalizerMorphism W₁₀ W₁) (Φ₂ : LocalizerMorphism W₂₀ W₂)
  (Φ₃ : LocalizerMorphism W₃₀ W₃) (Φ₄ : LocalizerMorphism W₄₀ W₄)
  (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ H)

abbrev Derives₄ : Prop :=
  (Φ₁.prod (Φ₂.prod (Φ₃.prod Φ₄))).Derives (uncurry₄.obj F)

variable [W₁₀.ContainsIdentities] [W₂₀.ContainsIdentities] [W₃₀.ContainsIdentities]
  [W₄₀.ContainsIdentities]

namespace Derives₄

variable {Φ₁ Φ₂ Φ₃ Φ₄ F} (h : Derives₄ Φ₁ Φ₂ Φ₃ Φ₄ F)
  [Φ₁.IsLeftDerivabilityStructure] [Φ₂.IsLeftDerivabilityStructure]
  [Φ₃.IsLeftDerivabilityStructure] [Φ₄.IsLeftDerivabilityStructure]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities]
  [W₃.ContainsIdentities] [W₄.ContainsIdentities]

include h in
lemma hasLeftDerivedFunctor₄ : F.HasLeftDerivedFunctor₄ W₁ W₂ W₃ W₄ :=
  Derives.hasLeftDerivedFunctor h

include h in
lemma isIso_of_isLeftDerivabilityStructure
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃} {L₄ : C₄ ⥤ D₄} [L₁.IsLocalization W₁]
    [L₂.IsLocalization W₂] [L₃.IsLocalization W₃] [L₄.IsLocalization W₄]
    {LF : D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ H}
    (α : (((((whiskeringLeft₄ H).obj L₁).obj L₂).obj L₃).obj L₄).obj LF ⟶ F)
    (X₁ : C₁₀) (X₂ : C₂₀) (X₃ : C₃₀) (X₄ : C₄₀) [LF.IsLeftDerivedFunctor₄ α W₁ W₂ W₃ W₄] :
    IsIso ((((α.app (Φ₁.functor.obj X₁)).app (Φ₂.functor.obj X₂)).app
      (Φ₃.functor.obj X₃)).app (Φ₄.functor.obj X₄)) :=
  Derives.isIso_of_isLeftDerivabilityStructure h (Functor.whiskeringLeft₄Equiv α) ⟨X₁, X₂, X₃, X₄⟩

end Derives₄

variable {F} in
lemma isLeftDerivedFunctor₄_of_isLeftDerivabilityStructure
    [W₁.ContainsIdentities] [W₂.ContainsIdentities] [W₃.ContainsIdentities] [W₄.ContainsIdentities]
    [Φ₁.IsLeftDerivabilityStructure] [Φ₂.IsLeftDerivabilityStructure]
    [Φ₃.IsLeftDerivabilityStructure] [Φ₄.IsLeftDerivabilityStructure]
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃} {L₄ : C₄ ⥤ D₄} [L₁.IsLocalization W₁]
    [L₂.IsLocalization W₂] [L₃.IsLocalization W₃] [L₄.IsLocalization W₄]
    {LF : D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ H}
    (α : (((((whiskeringLeft₄ H).obj L₁).obj L₂).obj L₃).obj L₄).obj LF ⟶ F)
    (hα : ∀ (X₁₀ : C₁₀) (X₂₀ : C₂₀) (X₃₀ : C₃₀) (X₄₀ : C₄₀),
      IsIso ((((α.app (Φ₁.functor.obj X₁₀)).app (Φ₂.functor.obj X₂₀)).app
        (Φ₃.functor.obj X₃₀)).app (Φ₄.functor.obj X₄₀))) :
    LF.IsLeftDerivedFunctor₄ α W₁ W₂ W₃ W₄ := by
  apply (Φ₁.prod (Φ₂.prod (Φ₃.prod Φ₄))).isLeftDerivedFunctor_of_isLeftDerivabilityStructure
  rintro ⟨X₁, X₂, X₃, X₄⟩
  apply hα

end LocalizerMorphism

end CategoryTheory
