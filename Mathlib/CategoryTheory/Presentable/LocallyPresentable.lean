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

class HasCardinalFilteredGenerators extends LocallySmall.{w} C : Prop where
  exists_generators : ∃ (ι : Type w) (G : ι → C),
    AreCardinalFilteredGenerators G κ

class IsCardinalLocallyPresentable
  extends HasCardinalFilteredGenerators C κ, HasColimitsOfSize.{w, w} C : Prop where

class HasCardinalFilteredColimits : Prop where
  hasColimitsOfShape (J : Type w) [Category.{w} J] [IsCardinalFiltered J κ] :
    HasColimitsOfShape J C := by intros; infer_instance

attribute [instance] HasCardinalFilteredColimits.hasColimitsOfShape

instance [HasColimitsOfSize.{w, w} C] : HasCardinalFilteredColimits.{w} C κ where

class IsCardinalAccessibleCategory
  extends HasCardinalFilteredGenerators C κ, HasCardinalFilteredColimits.{w} C κ : Prop where

instance [IsCardinalLocallyPresentable C κ] : IsCardinalAccessibleCategory C κ where

end

section

class IsLocallyPresentable : Prop where
  exists_cardinal : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
    IsCardinalLocallyPresentable C κ

class IsAccessibleCategory : Prop where
  exists_cardinal : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
    IsCardinalAccessibleCategory C κ

instance [h : IsLocallyPresentable.{w} C] : IsAccessibleCategory.{w} C where
  exists_cardinal := by
    obtain ⟨κ, hκ, h'⟩ := h.exists_cardinal
    exact ⟨κ, hκ, inferInstance⟩

end

end CategoryTheory
