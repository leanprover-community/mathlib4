/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Presentable.CardinalDirectedPoset

/-!
# Sharply smaller regular cardinals
-/

universe w v u

open CategoryTheory

namespace Cardinal

variable {κ₁ κ₂ : Cardinal.{w}} [Fact κ₁.IsRegular] [Fact κ₂.IsRegular]

variable (κ₁ κ₂) in
structure SharplyLT : Prop where
  lt : κ₁ < κ₂
  isCardinalAccessible_cardinalDirectedPoset :
    IsCardinalAccessibleCategory (CardinalFilteredPoset κ₁) κ₂

namespace SharplyLT

variable (h : SharplyLT κ₁ κ₂)

include h
lemma le : κ₁ ≤ κ₂ := h.lt.le

lemma isCardinalAccessible
    (C : Type u) [Category.{v} C] [IsCardinalAccessibleCategory C κ₁] :
    IsCardinalAccessibleCategory C κ₂ where
  toHasCardinalFilteredColimits := HasCardinalFilteredColimits.of_le C h.le
  exists_generator := sorry

end SharplyLT

end Cardinal
