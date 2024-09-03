/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Data.Nat.Restriction
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Measurability of the restriction function for functions indexed by `ℕ`

We prove that the map which restricts a function `f : (n : ℕ) → X n` to integers `≤ n` is
measurable.
-/

open MeasureTheory Nat

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

@[measurability, fun_prop]
theorem measurable_nat_restrict (n : ℕ) : Measurable (n.restrict (α := X)) :=
    measurable_set_restrict _

@[measurability, fun_prop]
theorem measurable_nat_restrict₂ {m n : ℕ} (hmn : m ≤ n) : Measurable (restrict₂ (α := X) hmn) :=
  measurable_set_restrict₂ _

@[measurability, fun_prop]
theorem measurable_nat_frestrict (n : ℕ) : Measurable (n.frestrict (α := X)) :=
  measurable_finset_restrict _

@[measurability, fun_prop]
theorem measurable_nat_frestrict₂ {m n : ℕ} (hmn : m ≤ n) : Measurable (frestrict₂ (α := X) hmn) :=
  measurable_finset_restrict₂ _
