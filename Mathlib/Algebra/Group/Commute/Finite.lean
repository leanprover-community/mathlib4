/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Data.Fintype.EquivFin

/-!
# Commuting elements and (in)finiteness.

This file contains lemma on the combination of `Commute` and `Finite`, `Fintype` and `Infinite`.
-/

variable {α : Type*}

instance instInfiniteProdSubtypeCommute [Mul α] [Infinite α] :
    Infinite { p : α × α // Commute p.1 p.2 } :=
  Infinite.of_injective (fun a => ⟨⟨a, a⟩, rfl⟩) (by intro; simp)
