/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Data.Nat.Restriction
import Mathlib.Topology.Constructions

/-!
# Measurability of the restriction function for functions indexed by `ℕ`

We prove that the map which restricts a function `f : (n : ℕ) → X n` to integers `≤ n` is
measurable.
-/

open Nat

variable {X : ℕ → Type*} [∀ n, TopologicalSpace (X n)]

@[continuity, fun_prop]
theorem continuous_nat_restrict (n : ℕ) : Continuous (n.restrict (α := X)) :=
  continuous_set_restrict _

@[continuity, fun_prop]
theorem continuous_nat_restrict₂ {m n : ℕ} (hmn : m ≤ n) : Continuous (restrict₂ (α := X) hmn) :=
  continuous_set_restrict₂ _

@[continuity, fun_prop]
theorem continuous_nat_frestrict (n : ℕ) : Continuous (n.frestrict (α := X)) :=
  continuous_finset_restrict _

@[continuity, fun_prop]
theorem continuous_nat_frestrict₂ {m n : ℕ} (hmn : m ≤ n) : Continuous (frestrict₂ (α := X) hmn) :=
  continuous_finset_restrict₂ _
