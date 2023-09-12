/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.RelSeries

/-!
This file discuss generalisation of relation series.

-/

universe u v

variable {α : Type u} (r : Rel α α)

/-- Relation series with ordinal indexing-/
structure RelSeries' where
/-- shut up linter-/
length : Ordinal.{v}
/-- shut up linter-/
toFun : Set.Iic length → α
/-- shut up linter-/
step : ∀ (i : Set.Iio length),
  r (toFun ⟨i, show i ≤ length from le_of_lt i.2⟩)
    (toFun ⟨i.1 + 1, show i.1 + 1 ≤ length from
      (Order.succ_le_iff_of_not_isMax $ not_isMax i.1).mpr i.2⟩)

example (o : Ordinal.{v}) : RelSeries' (α := Ordinal.{v}) (r := (. < .)) where
  length := o
  toFun := Subtype.val
  step := λ i ↦ by norm_num

/-- relation series with cardinal indexing-/
structure RelSeries'' where
/-- shut up linter-/
length : Cardinal.{v}
/-- shut up linter-/
toFun : Set.Iic length → α
/-- shut up linter-/
step : ∀ (i : Set.Iio length),
  r (toFun ⟨i, show i ≤ length from le_of_lt i.2⟩)
    (toFun ⟨Order.succ i.1, show Order.succ i.1 ≤ length from
      (Order.succ_le_iff_of_not_isMax $ not_isMax i.1).mpr i.2⟩)

example (o : Cardinal.{v}) : RelSeries'' (α := Cardinal.{v}) (r := (. < .)) where
  length := o
  toFun := Subtype.val
  step := λ i ↦ by norm_num
