/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedThree

/-!
# Deriving trifunctors using a derivability structure


-/

namespace CategoryTheory

open Limits Category

variable {C₁₀ C₂₀ C₃₀ C₁ C₂ C₃ D₁ D₂ D₃ H : Type*}
  [Category C₁₀] [Category C₂₀] [Category C₃₀]
  [Category C₁] [Category C₂] [Category C₃]
  [Category D₁] [Category D₂] [Category D₃] [Category H]
  {W₁₀ : MorphismProperty C₁₀} {W₂₀ : MorphismProperty C₂₀} {W₃₀ : MorphismProperty C₃₀}
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂} {W₃ : MorphismProperty C₃}

namespace LocalizerMorphism

variable (Φ₁ : LocalizerMorphism W₁₀ W₁) (Φ₂ : LocalizerMorphism W₂₀ W₂)
  (Φ₃ : LocalizerMorphism W₃₀ W₃) (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ H)

abbrev Derives₃ : Prop :=
  (Φ₁.prod (Φ₂.prod Φ₃)).Derives (uncurry₃.obj F)

variable [W₁₀.ContainsIdentities] [W₂₀.ContainsIdentities] [W₃₀.ContainsIdentities]

namespace Derives₃

variable {Φ₁ Φ₂ Φ₃ F} (h : Derives₃ Φ₁ Φ₂ Φ₃ F)
  [Φ₁.IsLeftDerivabilityStructure] [Φ₂.IsLeftDerivabilityStructure]
  [Φ₃.IsLeftDerivabilityStructure] [W₁.ContainsIdentities] [W₂.ContainsIdentities]
  [W₃.ContainsIdentities]

include h in
lemma hasLeftDerivedFunctor₃ : F.HasLeftDerivedFunctor₃ W₁ W₂ W₃ :=
  Derives.hasLeftDerivedFunctor h

include h in
lemma isIso_of_isLeftDerivabilityStructure
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃} [L₁.IsLocalization W₁]
    [L₂.IsLocalization W₂] [L₃.IsLocalization W₃] {LF : D₁ ⥤ D₂ ⥤ D₃ ⥤ H}
    (α : ((((whiskeringLeft₃ H).obj L₁).obj L₂).obj L₃).obj LF ⟶ F)
    (X₁ : C₁₀) (X₂ : C₂₀) (X₃ : C₃₀) [LF.IsLeftDerivedFunctor₃ α W₁ W₂ W₃] :
    IsIso (((α.app (Φ₁.functor.obj X₁)).app (Φ₂.functor.obj X₂)).app (Φ₃.functor.obj X₃)) :=
  Derives.isIso_of_isLeftDerivabilityStructure h (Functor.whiskeringLeft₃Equiv α) ⟨X₁, X₂, X₃⟩

end Derives₃

variable {F} in
lemma isLeftDerivedFunctor₃_of_isLeftDerivabilityStructure
    [W₁.ContainsIdentities] [W₂.ContainsIdentities] [W₃.ContainsIdentities]
    [Φ₁.IsLeftDerivabilityStructure] [Φ₂.IsLeftDerivabilityStructure]
    [Φ₃.IsLeftDerivabilityStructure]
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃} [L₁.IsLocalization W₁]
    [L₂.IsLocalization W₂] [L₃.IsLocalization W₃] {LF : D₁ ⥤ D₂ ⥤ D₃ ⥤ H}
    (α : ((((whiskeringLeft₃ H).obj L₁).obj L₂).obj L₃).obj LF ⟶ F)
    (hα : ∀ (X₁₀ : C₁₀) (X₂₀ : C₂₀) (X₃₀ : C₃₀),
      IsIso (((α.app (Φ₁.functor.obj X₁₀)).app (Φ₂.functor.obj X₂₀)).app (Φ₃.functor.obj X₃₀))) :
    LF.IsLeftDerivedFunctor₃ α W₁ W₂ W₃ := by
  apply (Φ₁.prod (Φ₂.prod Φ₃)).isLeftDerivedFunctor_of_isLeftDerivabilityStructure
  rintro ⟨X₁, X₂, X₃⟩
  apply hα

end LocalizerMorphism

end CategoryTheory
