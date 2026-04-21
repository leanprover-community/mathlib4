/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Invertible
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Module.Defs

/-!
# Further lemmas about monotonicity of scalar multiplication
-/
set_option backward.defeqAttrib.useBackward true

public section

variable {𝕜 R M : Type*}

section Semiring
variable [Semiring R] [Invertible (2 : R)] [Lattice M] [AddCommGroup M] [Module R M]
  [IsOrderedAddMonoid M]

variable (R) in
lemma inf_eq_half_smul_add_sub_abs_sub (x y : M) : x ⊓ y = (⅟2 : R) • (x + y - |y - x|) := by
  rw [← two_nsmul_inf_eq_add_sub_abs_sub x y, two_smul, ← two_smul R,
    smul_smul, invOf_mul_self, one_smul]

variable (R) in
lemma sup_eq_half_smul_add_add_abs_sub (x y : M) : x ⊔ y = (⅟2 : R) • (x + y + |y - x|) := by
  rw [← two_nsmul_sup_eq_add_add_abs_sub x y, two_smul, ← two_smul R,
    smul_smul, invOf_mul_self, one_smul]

end Semiring

section Ring
variable [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [LinearOrder M]
  [IsOrderedAddMonoid M] [Module R M] [PosSMulMono R M]

@[simp]
theorem abs_smul (a : R) (b : M) : |a • b| = |a| • |b| := by
  obtain ha | ha := le_total a 0 <;> obtain hb | hb := le_total b 0 <;>
    simp [*, abs_of_nonneg, abs_of_nonpos, smul_nonneg, smul_nonpos_of_nonneg_of_nonpos,
      smul_nonpos_of_nonpos_of_nonneg, smul_nonneg_of_nonpos_of_nonpos]

end Ring

section DivisionSemiring
variable [DivisionSemiring 𝕜] [NeZero (2 : 𝕜)] [Lattice M] [AddCommGroup M] [Module 𝕜 M]
  [IsOrderedAddMonoid M]

variable (𝕜) in
lemma inf_eq_half_smul_add_sub_abs_sub' (x y : M) : x ⊓ y = (2⁻¹ : 𝕜) • (x + y - |y - x|) :=
  let := invertibleOfNonzero (two_ne_zero' 𝕜); inf_eq_half_smul_add_sub_abs_sub 𝕜 x y

variable (𝕜) in
lemma sup_eq_half_smul_add_add_abs_sub' (x y : M) : x ⊔ y = (2⁻¹ : 𝕜) • (x + y + |y - x|) :=
  let := invertibleOfNonzero (two_ne_zero' 𝕜); sup_eq_half_smul_add_add_abs_sub 𝕜 x y

end DivisionSemiring
