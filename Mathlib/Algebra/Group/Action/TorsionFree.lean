/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Regular.SMul
import Mathlib.Algebra.Regular.Opposite
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Ring.Int.Defs

/-!
# Torsion-free actions

This file defines torsion-free actions as thosefor which `r • · : M → M` is injective
for all non-zero natural number `n`.

-/

open Function

variable {R S M G : Type*}

variable (R M) in
/-- An action is torsion free if regular elements are also `•`-regular.

This can be used to state that a module is torsion-free. -/
@[mk_iff]
class IsSMulTorsionFree [Mul R] [SMul R M] where
  protected isSMulRegular_of_isRegular ⦃r : R⦄ (hr : IsRegular r) : IsSMulRegular M r

section Mul
variable [Mul R] [SMul R M] [IsSMulTorsionFree R M]

variable (M) in
theorem IsRegular.isSMulRegular {r : R} (hr : IsRegular r) : IsSMulRegular M r :=
  IsSMulTorsionFree.isSMulRegular_of_isRegular hr

instance Subsingleton.to_isSMulTorsionFree [Subsingleton M] :
    IsSMulTorsionFree R M where
  isSMulRegular_of_isRegular _ _ := injective_of_subsingleton _

instance isSMulTorsionFreeLeft : IsSMulTorsionFree R R where
  isSMulRegular_of_isRegular _ hr := hr.left

instance isSMulTorsionFreeRight : IsSMulTorsionFree Rᵐᵒᵖ R where
  isSMulRegular_of_isRegular _ hr := hr.unop.isSMulRegular R


variable (R S)
theorem IsSMulTorsionFree.restrictScalars
    [Monoid S] [SMul R S] [SMul S M] [IsScalarTower R S M] :
    IsSMulTorsionFree S M where
  isSMulRegular_of_isRegular r hr := by
    let := hr.isS

end Mul

instance IsAddTorsionFree.toIsSMulTorsionFreeNat [AddMonoid M] [IsAddTorsionFree M] :
    IsSMulTorsionFree ℕ M where
  isSMulRegular_of_isRegular _ hn := nsmul_right_injective <| IsRegular.ne_zero hn

instance IsAddTorsionFree.toIsSMulTorsionFreeInt [AddGroup M] [IsAddTorsionFree M] :
    IsSMulTorsionFree ℤ M where
  isSMulRegular_of_isRegular _ hn := zsmul_right_injective <| IsRegular.ne_zero hn

section SMulInjective

variable [Semiring R] [IsCancelMulZero R] [AddCommGroup M] [Module R M] [IsSMulTorsionFree R M]
variable (M) in
theorem smul_right_injective
    {c : R} (hc : c ≠ 0) :
    Function.Injective (c • · : M → M) :=
  IsRegular.isSMulRegular _ <| isRegular_of_ne_zero hc

theorem smul_right_inj {c : R} (hc : c ≠ 0) {x y : M} :
    c • x = c • y ↔ x = y :=
  (smul_right_injective M hc).eq_iff

end SMulInjective
