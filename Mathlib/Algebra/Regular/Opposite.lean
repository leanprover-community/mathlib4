/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Regular.Basic
import Mathlib.Algebra.Opposites

/-!
# Results about `IsRegular` and `MulOpposite`
-/

variable {R} [Mul R]
open MulOpposite

@[to_additive (attr := simp)]
theorem isLeftRegular_op {a : R} : IsLeftRegular (op a) ↔ IsRightRegular a :=
  opEquiv.comp_injective _ |>.trans <| opEquiv.injective_comp _ |>.symm

@[to_additive (attr := simp)]
theorem isRightRegular_op {a : R} : IsRightRegular (op a) ↔ IsLeftRegular a :=
  opEquiv.comp_injective _ |>.trans <| opEquiv.injective_comp _ |>.symm

@[to_additive (attr := simp)]
theorem isRegular_op {a : R} : IsRegular (op a) ↔ IsRegular a := by
  simp [isRegular_iff, and_comm]

@[to_additive] protected alias ⟨_, IsLeftRegular.op⟩ := isLeftRegular_op
@[to_additive] protected alias ⟨_, IsRightRegular.op⟩ := isRightRegular_op
@[to_additive] protected alias ⟨_, IsRegular.op⟩ := isRegular_op

@[to_additive (attr := simp)]
theorem isLeftRegular_unop {a : Rᵐᵒᵖ} : IsLeftRegular a.unop ↔ IsRightRegular a :=
  isRightRegular_op.symm

@[to_additive (attr := simp)]
theorem isRightRegular_unop {a : Rᵐᵒᵖ} : IsRightRegular a.unop ↔ IsLeftRegular a :=
  isLeftRegular_op.symm

@[to_additive (attr := simp)]
theorem isRegular_unop {a : Rᵐᵒᵖ} : IsRegular a.unop ↔ IsRegular a :=
  isRegular_op.symm

@[to_additive] protected alias ⟨_, IsLeftRegular.unop⟩ := isLeftRegular_unop
@[to_additive] protected alias ⟨_, IsRightRegular.unop⟩ := isRightRegular_unop
@[to_additive] protected alias ⟨_, IsRegular.unop⟩ := isRegular_unop
