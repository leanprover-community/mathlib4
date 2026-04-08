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

/-! # Group with zero structure for `FunLike` -/

@[expose] public section

namespace FunLike

variable {F α β : Type*} [FunLike F α β]

variable [Zero F] [Mul F]

instance instMulZeroClass [MulZeroClass β] [FunLikeZero F α β] [FunLikeMul F α β] :
    MulZeroClass F :=
  fast_instance% DFunLike.coe_injective.mulZeroClass (fun (f : F) ↦ (f : α → β)) coe_zero coe_mul

instance instSemigroupWithZero [SemigroupWithZero β] [FunLikeZero F α β] [FunLikeMul F α β] :
    SemigroupWithZero F :=
  DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul

variable [One F]

instance instMulZeroOneClass [MulZeroOneClass β] [FunLikeZero F α β] [FunLikeOne F α β]
    [FunLikeMul F α β] : MulZeroOneClass F :=
  fast_instance% DFunLike.coe_injective.mulZeroOneClass (fun (f : F) ↦ (f : α → β)) coe_zero coe_one
    coe_mul

variable [Pow F ℕ]

instance instMonoidWithZero [MonoidWithZero β] [FunLikeZero F α β] [FunLikeOne F α β]
    [FunLikeMul F α β] [FunLikePow ℕ F α β] :
    MonoidWithZero F :=
  fast_instance% DFunLike.coe_injective.monoidWithZero (fun (f : F) ↦ (f : α → β)) coe_zero coe_one
    coe_mul coe_pow

instance instCommMonoidWithZero [CommMonoidWithZero β] [FunLikeZero F α β] [FunLikeOne F α β]
    [FunLikeMul F α β] [FunLikePow ℕ F α β] :
    CommMonoidWithZero F :=
  fast_instance% DFunLike.coe_injective.commMonoidWithZero (fun (f : F) ↦ (f : α → β)) coe_zero
    coe_one coe_mul coe_pow

end FunLike
