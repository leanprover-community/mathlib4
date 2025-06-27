/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Regular.Basic
import Mathlib.Algebra.Regular.SMul

/-!
# Results about `IsRegular` and `Prod`
-/

variable {α R S : Type*}

section
variable [Mul R] [Mul S]

@[to_additive (attr := simp)]
theorem Prod.isLeftRegular_mk {a : R} {b : S} :
    IsLeftRegular (a, b) ↔ IsLeftRegular a ∧ IsLeftRegular b :=
  have : Nonempty R := ⟨a⟩; have : Nonempty S := ⟨b⟩; Prod.map_injective

@[to_additive (attr := simp)]
theorem Prod.isRightRegular_mk {a : R} {b : S} :
    IsRightRegular (a, b) ↔ IsRightRegular a ∧ IsRightRegular b :=
  have : Nonempty R := ⟨a⟩; have : Nonempty S := ⟨b⟩; Iff.symm <| Prod.map_injective |>.symm

@[to_additive (attr := simp)]
theorem Prod.isRegular_mk {a : R} {b : S} : IsRegular (a, b) ↔ IsRegular a ∧ IsRegular b := by
  simp [isRegular_iff, and_and_and_comm]

@[to_additive]
theorem IsLeftRegular.prodMk {a : R} {b : S} (ha : IsLeftRegular a) (hb : IsLeftRegular b) :
    IsLeftRegular (a, b) := Prod.isLeftRegular_mk.2 ⟨ha, hb⟩

@[to_additive]
theorem IsRightRegular.prodMk {a : R} {b : S} (ha : IsRightRegular a) (hb : IsRightRegular b) :
    IsRightRegular (a, b) := Prod.isRightRegular_mk.2 ⟨ha, hb⟩

@[to_additive]
theorem IsRegular.prodMk {a : R} {b : S} (ha : IsRegular a) (hb : IsRegular b) :
    IsRegular (a, b) := Prod.isRegular_mk.2 ⟨ha, hb⟩

end

@[simp]
theorem Prod.isSMulRegular_iff [SMul α R] [SMul α S] {r : α} [Nonempty R] [Nonempty S] :
    IsSMulRegular (R × S) r ↔ IsSMulRegular R r ∧ IsSMulRegular S r :=
  Prod.map_injective
