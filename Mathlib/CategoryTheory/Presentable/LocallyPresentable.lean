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

section

class HasCardinalFilteredGenerators (C : Type u) [hC : Category.{v} C]
    (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] :
    Prop extends LocallySmall.{w} C where
  exists_generators (C κ) [hC] [hκ] : ∃ (ι : Type w) (G : ι → C),
    AreCardinalFilteredGenerators G κ

variable (C : Type u) [Category.{v} C] (κ : Cardinal.{w}) [Fact κ.IsRegular]

class IsCardinalLocallyPresentable : Prop
  extends HasCardinalFilteredGenerators C κ, HasColimitsOfSize.{w, w} C where

class IsCardinalAccessibleCategory : Prop
  extends HasCardinalFilteredGenerators C κ, HasCardinalFilteredColimits.{w} C κ where

instance [IsCardinalLocallyPresentable C κ] : IsCardinalAccessibleCategory C κ where

end

section

class IsLocallyPresentable (C : Type u) [hC : Category.{v} C] : Prop where
  exists_cardinal (C) [hC] : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
    IsCardinalLocallyPresentable C κ

class IsAccessibleCategory (C : Type u) [hC : Category.{v} C] : Prop where
  exists_cardinal (C) [hC] : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
    IsCardinalAccessibleCategory C κ

variable (C : Type u) [hC : Category.{v} C]

instance [IsLocallyPresentable.{w} C] : IsAccessibleCategory.{w} C where
  exists_cardinal := by
    obtain ⟨κ, hκ, h'⟩ := IsLocallyPresentable.exists_cardinal C
    exact ⟨κ, hκ, inferInstance⟩

instance [IsAccessibleCategory.{w} C] (X : C) : IsPresentable.{w} X := by
  obtain ⟨κ, _, _⟩ := IsAccessibleCategory.exists_cardinal C
  obtain ⟨ι, G, h⟩ := HasCardinalFilteredGenerators.exists_generators C κ
  apply h.presentable

end

end CategoryTheory
