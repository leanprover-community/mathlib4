/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Order.Restriction
import Mathlib.Topology.Constructions

/-!
# Continuity of the restriction function for functions indexed by a preorder

We prove that the map which restricts a function `f : (i : α) → X i` to elements `≤ a` is
continuous.
-/

namespace Preorder

variable {α : Type*} [Preorder α] {X : α → Type*} [∀ i, TopologicalSpace (X i)]

@[continuity, fun_prop]
theorem continuous_restrictLe (a : α) : Continuous (restrictLe (π := X) a) :=
  Pi.continuous_restrict _

@[continuity, fun_prop]
theorem continuous_restrictLe₂ {a b : α} (hab : a ≤ b) : Continuous (restrictLe₂ (π := X) hab) :=
  Pi.continuous_restrict₂ _

variable [LocallyFiniteOrderBot α]

@[continuity, fun_prop]
theorem continuous_frestrictLe (a : α) : Continuous (frestrictLe (π := X) a) :=
  Finset.continuous_restrict _

@[continuity, fun_prop]
theorem continuous_frestrictLe₂ {a b : α} (hab : a ≤ b) :
    Continuous (frestrictLe₂ (π := X) hab) :=
  Finset.continuous_restrict₂ _

end Preorder
