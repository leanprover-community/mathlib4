/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Group.FunLike
public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Algebra.GroupWithZero.Pi

/-! # Group with zero instances for `FunLike` types
In this file we define various instances related to `GroupWithZero` for `FunLike` types.
There are two different variants: either the multiplication is given by composition or it is
pointwise multiplication.

Note that currently, these are not registered as instances, but only `abbrev`s to avoid long
typeclass searches.
-/

@[expose] public section

namespace FunLike

variable {F α β : Type*}

section Comp

variable [FunLike F α α] [Zero F] [One F] [Mul F] [Zero α]
  [IsZeroApply F] [IsOneApplyEqSelf F] [IsMulApplyEqComp F]
  [ZeroHomClass F α α]

/-- A `FunLike` type with `(f * g) x = f (g x)` is a `MonoidWithZero` -/
protected abbrev compMonoidWithZero : MonoidWithZero F where
  mul_zero f := by apply DFunLike.ext; simp
  zero_mul _ := by apply DFunLike.ext; simp
  mul_one _ := by apply DFunLike.ext; simp
  one_mul _ := by apply DFunLike.ext; simp
  mul_assoc _ _ _ := by apply DFunLike.ext; simp

end Comp

section PointwiseMul

variable [FunLike F α β] [Zero F] [One F] [Mul F] [Pow F ℕ]

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `MulZeroClass` if `β` is a `MulZeroClass`. -/
protected abbrev mulZeroClass [MulZeroClass β] [IsZeroApply F] [IsMulApply F] :
    MulZeroClass F :=
  DFunLike.coe_injective.mulZeroClass _ coe_zero coe_mul

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `MulZeroOneClass` if `β` is a
`MulZeroOneClass`. -/
protected abbrev mulZeroOneClass [MulZeroOneClass β] [IsZeroApply F] [IsMulApply F]
    [IsOneApply F] :
    MulZeroOneClass F :=
  DFunLike.coe_injective.mulZeroOneClass _ coe_zero coe_one coe_mul

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `MonoidWithZero` if `β` is a
`MonoidWithZero`. -/
protected abbrev monoidWithZero [MonoidWithZero β] [IsZeroApply F] [IsMulApply F]
    [IsOneApply F] [IsPowApply ℕ F] :
    MonoidWithZero F :=
  DFunLike.coe_injective.monoidWithZero _ coe_zero coe_one coe_mul coe_pow

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `CommMonoidWithZero` if `β` is a
`CommMonoidWithZero`. -/
protected abbrev commMonoidWithZero [CommMonoidWithZero β] [IsZeroApply F] [IsMulApply F]
    [IsOneApply F] [IsPowApply ℕ F] :
    CommMonoidWithZero F :=
  DFunLike.coe_injective.commMonoidWithZero _ coe_zero coe_one coe_mul
    coe_pow

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `SemigroupWithZero` if `β` is a
`SemigroupWithZero`. -/
protected abbrev semigroupWithZero [SemigroupWithZero β] [IsZeroApply F] [IsMulApply F] :
    SemigroupWithZero F :=
  DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul

end PointwiseMul

end FunLike
