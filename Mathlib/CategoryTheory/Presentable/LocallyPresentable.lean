/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Presentable.CardinalFilteredPresentation

/-!
# Locally presentable and accessible categories

-/

universe w v u

namespace CategoryTheory

open Limits

variable (C : Type u) [Category.{v} C]

section

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]

class HasCardinalFilteredGenerators : Prop extends LocallySmall.{w} C where
  exists_generators' : ∃ (ι : Type w) (G : ι → C),
    AreCardinalFilteredGenerators G κ

namespace HasCardinalFilteredGenerators

lemma exists_generators [HasCardinalFilteredGenerators.{w} C κ] :
    ∃ (ι : Type w) (G : ι → C), AreCardinalFilteredGenerators G κ :=
  HasCardinalFilteredGenerators.exists_generators'

end HasCardinalFilteredGenerators

class IsCardinalLocallyPresentable : Prop
  extends HasCardinalFilteredGenerators C κ, HasColimitsOfSize.{w, w} C where

class IsCardinalAccessibleCategory : Prop
  extends HasCardinalFilteredGenerators C κ, HasCardinalFilteredColimits.{w} C κ where

instance [IsCardinalLocallyPresentable C κ] : IsCardinalAccessibleCategory C κ where

end

section

class IsLocallyPresentable : Prop where
  exists_cardinal' : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
    IsCardinalLocallyPresentable C κ

lemma IsLocallyPresentable.exists_cardinal [IsLocallyPresentable.{w} C] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalLocallyPresentable C κ :=
  exists_cardinal'

class IsAccessibleCategory : Prop where
  exists_cardinal' : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
    IsCardinalAccessibleCategory C κ

lemma IsAccessibleCategory.exists_cardinal [IsAccessibleCategory.{w} C] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory C κ :=
  exists_cardinal'

instance [h : IsLocallyPresentable.{w} C] : IsAccessibleCategory.{w} C where
  exists_cardinal' := by
    obtain ⟨κ, hκ, h'⟩ := h.exists_cardinal
    exact ⟨κ, hκ, inferInstance⟩

instance [IsAccessibleCategory.{w} C] (X : C) : IsPresentable.{w} X := by
  obtain ⟨κ, _, _⟩ := IsAccessibleCategory.exists_cardinal C
  obtain ⟨ι, G, h⟩ := HasCardinalFilteredGenerators.exists_generators C κ
  apply h.presentable

end

end CategoryTheory
