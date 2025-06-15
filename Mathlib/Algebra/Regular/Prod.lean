/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Regular.Basic

/-!
# Results about `IsRegular` and `Prod`
-/

variable {R S : Type*} [Mul R] [Mul S]

@[to_additive (attr := simp)]
theorem isLeftRegular_mk {a : R} {b : S} :
    IsLeftRegular (a, b) ↔ IsLeftRegular a ∧ IsLeftRegular b :=
  have : Nonempty R := ⟨a⟩; have : Nonempty S := ⟨b⟩; Prod.map_injective

@[to_additive (attr := simp)]
theorem isRightRegular_mk {a : R} {b : S} :
    IsRightRegular (a, b) ↔ IsRightRegular a ∧ IsRightRegular b :=
  have : Nonempty R := ⟨a⟩; have : Nonempty S := ⟨b⟩; Iff.symm <| Prod.map_injective |>.symm

@[to_additive (attr := simp)]
theorem isRegular_mk {a : R} {b : S} : IsRegular (a, b) ↔ IsRegular a ∧ IsRegular b := by
  simp [isRegular_iff, and_and_and_comm]

@[to_additive]
theorem IsLeftRegular.prodMk {a : R} {b : S} (ha : IsLeftRegular a) (hb : IsLeftRegular b) :
    IsLeftRegular (a, b) := isLeftRegular_mk.2 ⟨ha, hb⟩

@[to_additive]
theorem IsRightRegular.prodMk {a : R} {b : S} (ha : IsRightRegular a) (hb : IsRightRegular b) :
    IsRightRegular (a, b) := isRightRegular_mk.2 ⟨ha, hb⟩

@[to_additive]
theorem IsRegular.prodMk {a : R} {b : S} (ha : IsRegular a) (hb : IsRegular b) :
    IsRegular (a, b) := isRegular_mk.2 ⟨ha, hb⟩
