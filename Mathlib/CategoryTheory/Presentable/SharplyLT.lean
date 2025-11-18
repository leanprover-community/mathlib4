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

variable {κ₁ κ₂ : Cardinal.{w}}

structure SharplyLT [Fact κ₁.IsRegular] [Fact κ₂.IsRegular] : Prop where
  lt : κ₁ < κ₂
  isCardinalAccessible_cardinalDirectedPoset :
    IsCardinalAccessibleCategory (CardinalFilteredPoset κ₁) κ₂

end Cardinal
