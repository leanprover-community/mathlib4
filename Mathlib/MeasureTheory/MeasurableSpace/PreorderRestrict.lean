/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Order.Restriction
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Measurability of the restriction function for functions indexed by a preorder

We prove that the map which restricts a function `f : (i : α) → X i` to elements `≤ a` is
measurable.
-/

open MeasureTheory

namespace Preorder

variable {α : Type*} [Preorder α] {X : α → Type*} [∀ a, MeasurableSpace (X a)]

@[measurability, fun_prop]
theorem measurable_restrict (a : α) : Measurable (restrict (β := X) a) :=
    Set.measurable_restrict _

@[measurability, fun_prop]
theorem measurable_restrict₂ {a b : α} (hab : a ≤ b) : Measurable (restrict₂ (β := X) hab) :=
  Set.measurable_restrict₂ _

variable [LocallyFiniteOrderBot α]

@[measurability, fun_prop]
theorem measurable_frestrict (a : α) : Measurable (frestrict (β := X) a) :=
  Finset.measurable_restrict _

@[measurability, fun_prop]
theorem measurable_frestrict₂ {a b : α} (hab : a ≤ b) : Measurable (frestrict₂ (β := X) hab) :=
  Finset.measurable_restrict₂ _

end Preorder
