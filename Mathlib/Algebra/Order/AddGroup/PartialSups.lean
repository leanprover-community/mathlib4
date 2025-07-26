/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Lua Viana Reis
-/
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Order.PartialSups

/-!
# `PartialSups` of functions taking values in an `AddGroup`
-/

variable {α ι : Type*}

lemma partialSups_const_add [Preorder ι] [LocallyFiniteOrderBot ι] [Lattice α] [AddGroup α]
    [CovariantClass α α (· + ·) (· ≤ ·)] (f : ι → α) (c : α) (i : ι) :
    partialSups (c + f ·) i = c + partialSups f i := by
  change (partialSups (OrderIso.addLeft c ∘ f)) i = _
  rw [comp_partialSups f (OrderIso.addLeft c)]
  rfl
