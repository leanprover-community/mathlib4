/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Restriction

/-!
# Measurability of the restriction function for functions indexed by a preorder

We prove that the map which restricts a function `f : (i : α) → X i` to elements `≤ a` is
measurable.
-/

open MeasureTheory

namespace Preorder

variable {α : Type*} [Preorder α] {X : α → Type*} [∀ a, MeasurableSpace (X a)]

@[measurability, fun_prop]
theorem measurable_restrictLe (a : α) : Measurable (restrictLe (π := X) a) :=
    Set.measurable_restrict _

@[measurability, fun_prop]
theorem measurable_restrictLe₂ {a b : α} (hab : a ≤ b) : Measurable (restrictLe₂ (π := X) hab) :=
  Set.measurable_restrict₂ _

variable [LocallyFiniteOrderBot α]

@[measurability, fun_prop]
theorem measurable_frestrictLe (a : α) : Measurable (frestrictLe (π := X) a) :=
  Finset.measurable_restrict _

@[measurability, fun_prop]
theorem measurable_frestrictLe₂ {a b : α} (hab : a ≤ b) : Measurable (frestrictLe₂ (π := X) hab) :=
  Finset.measurable_restrict₂ _

end Preorder
