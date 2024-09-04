/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Order.Restriction
import Mathlib.Topology.Constructions

/-!
# Measurability of the restriction function for functions indexed by `ℕ`

We prove that the map which restricts a function `f : (i : α) → X i` to elements `≤ a` is
measurable.
-/

namespace Preorder

variable {α : Type*} [Preorder α] {X : α  → Type*} [∀ i, TopologicalSpace (X i)]

@[continuity, fun_prop]
theorem continuous_restrict (a : α) : Continuous (restrict (β := X) a) :=
  Pi.continuous_restrict _

@[continuity, fun_prop]
theorem continuous_restrict₂ {a b : α} (hab : a ≤ b) : Continuous (restrict₂ (β := X) hab) :=
  Pi.continuous_restrict₂ _

variable [LocallyFiniteOrderBot α]

@[continuity, fun_prop]
theorem continuous_frestrict (a : α) : Continuous (frestrict (β := X) a) :=
  Finset.continuous_restrict _

@[continuity, fun_prop]
theorem continuous_nat_frestrict₂ {a b : α} (hab : a ≤ b) : Continuous (frestrict₂ (β := X) hab) :=
  Finset.continuous_restrict₂ _

end Preorder
