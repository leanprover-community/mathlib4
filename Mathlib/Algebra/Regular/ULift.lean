/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Regular.SMul

/-!
# Results about `IsRegular` and `ULift`
-/

universe u v

variable {α} {R : Type v}

namespace ULift

section
variable [Mul R]

@[to_additive (attr := simp)]
theorem isLeftRegular_up {a : R} : IsLeftRegular (ULift.up.{u} a) ↔ IsLeftRegular a :=
  Equiv.ulift.symm.comp_injective _ |>.trans <| Equiv.ulift.symm.injective_comp _ |>.symm

@[to_additive (attr := simp)]
theorem isRightRegular_up {a : R} : IsRightRegular (ULift.up.{u} a) ↔ IsRightRegular a :=
  Equiv.ulift.symm.comp_injective _ |>.trans <| Equiv.ulift.symm.injective_comp _ |>.symm

@[to_additive (attr := simp)]
theorem isRegular_up {a : R} : IsRegular (ULift.up.{u} a) ↔ IsRegular a := by
  simp [isRegular_iff]

@[to_additive (attr := simp)]
theorem isLeftRegular_down {a : ULift.{u} R} : IsLeftRegular a.down ↔ IsLeftRegular a :=
  isLeftRegular_up.symm

@[to_additive (attr := simp)]
theorem isRightRegular_down {a : ULift.{u} R} : IsRightRegular a.down ↔ IsRightRegular a :=
  isRightRegular_up.symm

@[to_additive (attr := simp)]
theorem isRegular_down {a : ULift.{u} R} : IsRegular a.down ↔ IsRegular a :=
  isRegular_up.symm

end

@[simp]
theorem isSMulRegular_iff [SMul α R] {r : α} :
    IsSMulRegular (ULift R) r ↔ IsSMulRegular R r :=
  Equiv.ulift.symm.comp_injective _ |>.trans <| Equiv.ulift.symm.injective_comp _ |>.symm

end ULift
