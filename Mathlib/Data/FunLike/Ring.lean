/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Data.FunLike.Group
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Ring.Pi
import Mathlib.Tactic.FastInstance

/-! # Ring instances for `FunLike` types
In this file we define various instances related to ring for `FunLike` types.
-/

@[expose] public section

variable {F α : Type*}

section MonoidWithZero

variable [FunLike F α α] [Zero F] [One F] [Mul F] [Zero α]
  [IsZeroApply F α α] [IsOneApplyEqId F α] [IsMulApplyEqComp F α]
  [ZeroHomClass F α α]

instance FunLike.instMonoidWithZero : MonoidWithZero F where
  mul_zero f := by apply DFunLike.ext; simp
  zero_mul _ := by apply DFunLike.ext; simp
  mul_one _ := by apply DFunLike.ext; simp
  one_mul _ := by apply DFunLike.ext; simp
  mul_assoc _ _ _ := by apply DFunLike.ext; simp

end MonoidWithZero

section Semiring

variable [FunLike F α α] [Zero F] [One F] [Mul F] [Add F] [AddCommMonoid α]
  [IsZeroApply F α α] [IsAddApply F α α] [IsOneApplyEqId F α] [IsMulApplyEqComp F α]
  [SMul ℕ F] [IsSMulApply ℕ F α α] [AddMonoidHomClass F α α]

instance FunLike.instSemiring : Semiring F where
  __ := FunLike.instMonoidWithZero
  __ := FunLike.instAddCommMonoid
  left_distrib f g h := by apply DFunLike.ext; simp
  right_distrib _ _ _ := by apply DFunLike.ext; simp
  natCast n := n • (1 : F)
  natCast_zero := by apply DFunLike.ext; simp
  natCast_succ n := by apply DFunLike.ext; simpa using (succ_nsmul · n)

@[norm_cast]
theorem coe_natCast (n : ℕ) : (n : F) = n • (1 : F) := rfl

@[simp, grind =]
theorem natCast_apply [SMul ℕ α] [IsSMulApply ℕ F α α] (n : ℕ) (x : α) :
    (↑n : F) x = n • x := by
  norm_cast
  rw [smul_apply, one_apply_eq_id]

end Semiring

section Ring

variable [FunLike F α α] [Zero F] [One F] [Mul F] [Add F] [Neg F] [Sub F]
  [AddCommGroup α]
  [IsZeroApply F α α] [IsAddApply F α α] [IsOneApplyEqId F α] [IsMulApplyEqComp F α]
  [IsNegApply F α α] [IsSubApply F α α]
  [SMul ℕ F] [IsSMulApply ℕ F α α]
  [SMul ℤ F] [IsSMulApply ℤ F α α] [AddMonoidHomClass F α α]

instance FunLike.instRing : Ring F where
  __ := FunLike.instSemiring
  __ := FunLike.instAddCommGroup
  intCast n := n • (1 : F)
  intCast_ofNat := natCast_zsmul _
  intCast_negSucc n := by apply negSucc_zsmul _

@[norm_cast]
theorem coe_intCast (n : ℤ) : (n : F) = n • (1 : F) := rfl

@[simp, grind =]
theorem intCast_apply [SMul ℤ α] [IsSMulApply ℤ F α α] (n : ℤ) (x : α) :
    (↑n : F) x = n • x := by
  norm_cast
  rw [smul_apply, one_apply_eq_id]

end Ring
