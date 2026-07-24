/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Data.FunLike.Group
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Ring.Pi

/-! # Ring instances for `FunLike` types
In this file we define various instances related to ring for `FunLike` types.

Note that currently, these are not registered as instances, but only `abbrev`s to avoid long
typeclass searches.
-/

@[expose] public section

variable {F α : Type*}

section MonoidWithZero

variable [FunLike F α α] [Zero F] [One F] [Mul F] [Zero α]
  [IsZeroApply F α α] [IsOneApplyEqSelf F α] [IsMulApplyEqComp F α]
  [ZeroHomClass F α α] [NPow F]
  (pow_zero : ∀ f : F, f ^ 0 = 1)
  (pow_succ : ∀ (n : ℕ) (f : F), f ^ (n + 1) = f ^ n * f)

/-- A `FunLike` type with `(f + g) x = f x + g x` and `(f * g) x = f (g x)` is a `MonoidWithZero`
if `α` is a `MonoidWithZero`. -/
protected abbrev FunLike.monoidWithZero : MonoidWithZero F where
  mul_zero f := by apply DFunLike.ext; simp
  zero_mul _ := by apply DFunLike.ext; simp
  mul_one _ := by apply DFunLike.ext; simp
  one_mul _ := by apply DFunLike.ext; simp
  mul_assoc _ _ _ := by apply DFunLike.ext; simp
  npow_zero := pow_zero
  npow_succ := pow_succ

end MonoidWithZero

section Semiring

variable [FunLike F α α] [Zero F] [One F] [Mul F] [Add F] [AddCommMonoid α]
  [IsZeroApply F α α] [IsAddApply F α α] [IsOneApplyEqSelf F α] [IsMulApplyEqComp F α]
  [SMul ℕ F] [IsSMulApply ℕ F α α] [AddMonoidHomClass F α α] [NatCast F] [IsNatCastApply F α]
  [NPow F] (pow_zero : ∀ f : F, f ^ 0 = 1) (pow_succ : ∀ (n : ℕ) (f : F), f ^ (n + 1) = f ^ n * f)

/-- A `FunLike` type with `(f + g) x = f x + g x` and `(f * g) x = f (g x)` is a `Semiring` if `α`
is a `AddCommMonoid`. -/
protected abbrev FunLike.semiring : Semiring F where
  __ := FunLike.monoidWithZero pow_zero pow_succ
  __ := FunLike.addCommMonoid
  left_distrib f g h := by apply DFunLike.ext; simp
  right_distrib _ _ _ := by apply DFunLike.ext; simp
  natCast_zero := by apply DFunLike.ext; simp
  natCast_succ n := by apply DFunLike.ext; simp [succ_nsmul]

end Semiring

section Ring

variable [FunLike F α α] [Zero F] [One F] [Mul F] [Add F] [Neg F] [Sub F]
  [AddCommGroup α]
  [IsZeroApply F α α] [IsAddApply F α α] [IsOneApplyEqSelf F α] [IsMulApplyEqComp F α]
  [IsNegApply F α α] [IsSubApply F α α]
  [SMul ℕ F] [IsSMulApply ℕ F α α]
  [SMul ℤ F] [IsSMulApply ℤ F α α] [AddMonoidHomClass F α α]
  [NatCast F] [IsNatCastApply F α] [IntCast F] [IsIntCastApply F α]
  [NPow F] (pow_zero : ∀ f : F, f ^ 0 = 1) (pow_succ : ∀ (n : ℕ) (f : F), f ^ (n + 1) = f ^ n * f)

/-- A `FunLike` type with `(f + g) x = f x + g x` and `(f * g) x = f (g x)` is a `Ring` if `α` is a
`AddCommGroup`. -/
protected abbrev FunLike.ring : Ring F where
  __ := FunLike.semiring pow_zero pow_succ
  __ := FunLike.addCommGroup
  intCast_ofNat _ := by apply DFunLike.ext; simp
  intCast_negSucc n := by apply DFunLike.ext; simp [succ_nsmul]

end Ring
