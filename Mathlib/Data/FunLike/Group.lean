/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Data.FunLike.Hom
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Tactic.FastInstance

/-! # Group structure for `FunLike` -/

@[expose] public section

namespace FunLike

variable {F α β : Type*} [FunLike F α β]

section CoercionHom

variable [MulOne F] [MulOneClass β] [FunLikeOne F α β] [FunLikeMul F α β]

variable (F α β) in
/-- Coercion as a multiplicative homomorphism. -/
@[to_additive
/-- Coercion as an additive homomorphism. -/]
def coeMulHom : F →* α → β where
  toFun f := f
  map_one' := coe_one
  map_mul' := coe_mul

@[to_additive]
theorem coe_coeMulHom : (coeMulHom F α β : F → α → β) = DFunLike.coe := rfl

@[to_additive]
theorem coeMulHom_injective : Function.Injective (coeMulHom F α β) := by
  rw [coe_coeMulHom]
  exact DFunLike.coe_injective

end CoercionHom

section GroupInstances

variable [Mul F]

@[to_additive]
instance instSemigroup [Semigroup β] [FunLikeMul F α β] : Semigroup F :=
  fast_instance% DFunLike.coe_injective.semigroup (fun (f : F) ↦ (f : α → β)) coe_mul

@[to_additive]
instance instCommSemigroup [CommSemigroup β] [FunLikeMul F α β] :
    CommSemigroup F :=
  fast_instance% DFunLike.coe_injective.commSemigroup (fun (f : F) ↦ (f : α → β)) coe_mul

@[to_additive]
instance instIsLeftCancelMul [Mul β] [IsLeftCancelMul β] [FunLikeMul F α β] :
    IsLeftCancelMul F :=
  DFunLike.coe_injective.isLeftCancelMul (fun (f : F) ↦ (f : α → β)) coe_mul

@[to_additive]
instance instIsRightCancelMul [Mul β] [IsRightCancelMul β] [FunLikeMul F α β] :
    IsRightCancelMul F :=
  DFunLike.coe_injective.isRightCancelMul (fun (f : F) ↦ (f : α → β)) coe_mul

@[to_additive]
instance instIsCancelMul [Mul β] [IsCancelMul β] [FunLikeMul F α β] :
    IsCancelMul F :=
  DFunLike.coe_injective.isCancelMul (fun (f : F) ↦ (f : α → β)) coe_mul

@[to_additive]
instance instLeftCancelSemigroup [LeftCancelSemigroup β] [FunLikeMul F α β] :
    LeftCancelSemigroup F :=
  DFunLike.coe_injective.leftCancelSemigroup (fun (f : F) ↦ (f : α → β)) coe_mul

@[to_additive]
instance instRightCancelSemigroup [RightCancelSemigroup β] [FunLikeMul F α β] :
    RightCancelSemigroup F :=
  DFunLike.coe_injective.rightCancelSemigroup (fun (f : F) ↦ (f : α → β)) coe_mul

variable [One F]

@[to_additive]
instance instMulOne [MulOneClass β] [FunLikeOne F α β] [FunLikeMul F α β] :
    MulOneClass F :=
  fast_instance% DFunLike.coe_injective.mulOneClass (fun (f : F) ↦ (f : α → β)) coe_one coe_mul

variable [Pow F ℕ]

@[to_additive]
instance instMonoid [Monoid β] [FunLikeOne F α β] [FunLikeMul F α β] [FunLikePow ℕ F α β] :
    Monoid F :=
  fast_instance% DFunLike.coe_injective.monoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_pow

@[to_additive]
instance instLeftCancelMonoid [LeftCancelMonoid β] [FunLikeOne F α β] [FunLikeMul F α β]
    [FunLikePow ℕ F α β] :
    LeftCancelMonoid F :=
  fast_instance%
    DFunLike.coe_injective.leftCancelMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_pow

@[to_additive]
instance instRightCancelMonoid [RightCancelMonoid β] [FunLikeOne F α β] [FunLikeMul F α β]
    [FunLikePow ℕ F α β] :
    RightCancelMonoid F :=
  fast_instance%
    DFunLike.coe_injective.rightCancelMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_pow

@[to_additive]
instance instCancelMonoid [CancelMonoid β] [FunLikeOne F α β] [FunLikeMul F α β]
    [FunLikePow ℕ F α β] :
    CancelMonoid F :=
  fast_instance%
    DFunLike.coe_injective.cancelMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_pow

@[to_additive]
instance instCommMonoid [CommMonoid β] [FunLikeOne F α β] [FunLikeMul F α β]
    [FunLikePow ℕ F α β] :
    CommMonoid F :=
  fast_instance%
    DFunLike.coe_injective.commMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_pow

@[to_additive]
instance instCancelCommMonoid [CancelCommMonoid β] [FunLikeOne F α β] [FunLikeMul F α β]
    [FunLikePow ℕ F α β] :
    CancelCommMonoid F :=
  fast_instance%
    DFunLike.coe_injective.cancelCommMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_pow

variable [Inv F]

@[to_additive]
instance instInvolutiveInv [InvolutiveInv β] [FunLikeInv F α β] : InvolutiveInv F :=
  fast_instance% DFunLike.coe_injective.involutiveInv (fun (f : F) ↦ (f : α → β)) coe_inv

@[to_additive]
instance instInvOneClass [InvOneClass β] [FunLikeOne F α β] [FunLikeInv F α β] : InvOneClass F :=
  fast_instance% DFunLike.coe_injective.invOneClass (fun (f : F) ↦ (f : α → β)) coe_one coe_inv

variable [Div F] [Pow F ℤ]

@[to_additive instSubNegMonoid]
instance instDivInvMonoid [DivInvMonoid β] [FunLikeOne F α β] [FunLikeMul F α β] [FunLikeInv F α β]
    [FunLikeDiv F α β] [FunLikePow ℕ F α β] [FunLikePow ℤ F α β] : DivInvMonoid F :=
  fast_instance% DFunLike.coe_injective.divInvMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul
    coe_inv coe_div coe_pow coe_pow

@[to_additive]
instance instDivInvOneMonoid [DivInvOneMonoid β] [FunLikeOne F α β] [FunLikeMul F α β]
    [FunLikeInv F α β] [FunLikeDiv F α β] [FunLikePow ℕ F α β] [FunLikePow ℤ F α β] :
    DivInvOneMonoid F :=
  fast_instance% DFunLike.coe_injective.divInvOneMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul
    coe_inv coe_div coe_pow coe_pow

@[to_additive]
instance instDivisionMonoid [DivisionMonoid β] [FunLikeOne F α β] [FunLikeMul F α β]
    [FunLikeInv F α β] [FunLikeDiv F α β] [FunLikePow ℕ F α β] [FunLikePow ℤ F α β] :
    DivisionMonoid F :=
  fast_instance% DFunLike.coe_injective.divisionMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul
    coe_inv coe_div coe_pow coe_pow

@[to_additive instSubtractionCommMonoid]
instance instDivisionCommMonoid [DivisionCommMonoid β] [FunLikeOne F α β] [FunLikeMul F α β]
    [FunLikeInv F α β] [FunLikeDiv F α β] [FunLikePow ℕ F α β] [FunLikePow ℤ F α β] :
    DivisionCommMonoid F :=
  fast_instance% DFunLike.coe_injective.divisionCommMonoid (fun (f : F) ↦ (f : α → β)) coe_one
    coe_mul coe_inv coe_div coe_pow coe_pow

@[to_additive]
instance instGroup [Group β] [FunLikeOne F α β] [FunLikeMul F α β] [FunLikeInv F α β]
    [FunLikeDiv F α β] [FunLikePow ℕ F α β] [FunLikePow ℤ F α β] :
    Group F :=
  fast_instance% DFunLike.coe_injective.group (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_inv
    coe_div coe_pow coe_pow

@[to_additive]
instance instCommGroup [CommGroup β] [FunLikeOne F α β] [FunLikeMul F α β] [FunLikeInv F α β]
    [FunLikeDiv F α β] [FunLikePow ℕ F α β] [FunLikePow ℤ F α β] :
    CommGroup F :=
  fast_instance% DFunLike.coe_injective.commGroup (fun (f : F) ↦ (f : α → β)) coe_one coe_mul
    coe_inv coe_div coe_pow coe_pow

end GroupInstances

end FunLike
