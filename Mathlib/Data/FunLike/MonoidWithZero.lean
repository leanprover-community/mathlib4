/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Data.FunLike.Group
public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Algebra.GroupWithZero.Pi
import Mathlib.Tactic.FastInstance

/-! # Monoid with zero instances for `FunLike` types
In this file we define various instances related to monoids with zero for `FunLike` types.
-/

public section

namespace FunLike

variable {F α β : Type*} [FunLike F α β]

variable [Zero F] [Mul F]

instance instMulZeroClass [MulZeroClass β] [IsZeroApply F α β] [IsMulApply F α β] :
    MulZeroClass F :=
  fast_instance% DFunLike.coe_injective.mulZeroClass (fun (f : F) ↦ (f : α → β)) coe_zero coe_mul

instance instSemigroupWithZero [SemigroupWithZero β] [IsZeroApply F α β] [IsMulApply F α β] :
    SemigroupWithZero F :=
  DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul

variable [One F]

instance instMulZeroOneClass [MulZeroOneClass β] [IsZeroApply F α β] [IsOneApply F α β]
    [IsMulApply F α β] : MulZeroOneClass F :=
  fast_instance% DFunLike.coe_injective.mulZeroOneClass (fun (f : F) ↦ (f : α → β)) coe_zero coe_one
    coe_mul

variable [Pow F ℕ]

instance instMonoidWithZero [MonoidWithZero β] [IsZeroApply F α β] [IsOneApply F α β]
    [IsMulApply F α β] [IsPowApply ℕ F α β] :
    MonoidWithZero F :=
  fast_instance% DFunLike.coe_injective.monoidWithZero (fun (f : F) ↦ (f : α → β)) coe_zero coe_one
    coe_mul coe_pow

instance instCommMonoidWithZero [CommMonoidWithZero β] [IsZeroApply F α β] [IsOneApply F α β]
    [IsMulApply F α β] [IsPowApply ℕ F α β] :
    CommMonoidWithZero F :=
  fast_instance% DFunLike.coe_injective.commMonoidWithZero (fun (f : F) ↦ (f : α → β)) coe_zero
    coe_one coe_mul coe_pow

end FunLike
