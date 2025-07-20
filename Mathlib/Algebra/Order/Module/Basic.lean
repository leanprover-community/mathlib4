/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Module.Defs

/-!
# Further lemmas about monotonicity of scalar multiplication
-/

variable {α β : Type*}
variable [Ring α] [LinearOrder α] [IsOrderedRing α]
variable [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β]
variable [Module α β] [PosSMulMono α β]

@[simp]
theorem abs_smul (a : α) (b : β) : |a • b| = |a| • |b| := by
  obtain ha | ha := le_total a 0 <;> obtain hb | hb := le_total b 0 <;>
    simp [*, abs_of_nonneg, abs_of_nonpos, smul_nonneg, smul_nonpos_of_nonneg_of_nonpos,
      smul_nonpos_of_nonpos_of_nonneg, smul_nonneg_of_nonpos_of_nonpos]
