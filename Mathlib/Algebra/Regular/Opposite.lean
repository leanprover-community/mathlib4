/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Regular.Basic

/-!
# Results about `IsRegular` and `MulOpposite`
-/

variable {R} [Mul R]

@[to_additive (attr := simp)]
theorem isLeftRegular_op {a : R} :
    IsLeftRegular (MulOpposite.op a) ↔ IsRightRegular a :=
  MulOpposite.opEquiv.comp_injective _ |>.trans <| MulOpposite.opEquiv.injective_comp _ |>.symm

@[to_additive (attr := simp)]
theorem isRightRegular_op {a : R} :
    IsRightRegular (MulOpposite.op a) ↔ IsLeftRegular a :=
  MulOpposite.opEquiv.comp_injective _ |>.trans <| MulOpposite.opEquiv.injective_comp _ |>.symm

@[to_additive (attr := simp)]
theorem isRegular_op {a : R} : IsRegular (MulOpposite.op a) ↔ IsRegular a := by
  simp [isRegular_iff, and_comm]

@[to_additive] alias ⟨_, IsLeftRegular.op⟩ := isLeftRegular_op
@[to_additive] alias ⟨_, IsRightRegular.op⟩ := isRightRegular_op
@[to_additive] alias ⟨_, IsRegular.op⟩ := isRegular_op

@[to_additive (attr := simp)]
theorem isLeftRegular_unop {a : Rᵐᵒᵖ} :
    IsLeftRegular (MulOpposite.unop a) ↔ IsRightRegular a :=
  isRightRegular_op.symm

@[to_additive (attr := simp)]
theorem isRightRegular_unop {a : Rᵐᵒᵖ} :
    IsRightRegular (MulOpposite.unop a) ↔ IsLeftRegular a :=
  isLeftRegular_op.symm

@[to_additive (attr := simp)]
theorem isRegular_unop {a : Rᵐᵒᵖ} : IsRegular (MulOpposite.unop a) ↔ IsRegular a :=
  isRegular_op.symm

@[to_additive] alias ⟨_, IsLeftRegular.unop⟩ := isLeftRegular_unop
@[to_additive] alias ⟨_, IsRightRegular.unop⟩ := isRightRegular_unop
@[to_additive] alias ⟨_, IsRegular.unop⟩ := isRegular_unop
