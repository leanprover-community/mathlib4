/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Regular.Basic

/-!
# Results about `IsRegular` and pi types
-/

variable {ι : Type*} {R : ι → Type*} [∀ i, Mul (R i)]

@[to_additive (attr := simp)]
theorem Pi.isLeftRegular_iff {a : ∀ i, R i} : IsLeftRegular a ↔ ∀ i, IsLeftRegular (a i) :=
  have (i) : Nonempty (R i) := ⟨a i⟩; Pi.map_injective

@[to_additive (attr := simp)]
theorem Pi.isRightRegular_iff {a : ∀ i, R i} : IsRightRegular a ↔ ∀ i, IsRightRegular (a i) :=
  have (i) : Nonempty (R i) := ⟨a i⟩; Iff.symm <| Pi.map_injective.symm

@[to_additive (attr := simp)]
theorem Pi.isRegular_iff {a : ∀ i, R i} : IsRegular a ↔ ∀ i, IsRegular (a i) := by
  simp [_root_.isRegular_iff, forall_and]
