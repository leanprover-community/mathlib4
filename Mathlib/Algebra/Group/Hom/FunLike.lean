/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Tactic.FastInstance

/-! # Group structure for `FunLike` -/

@[expose] public section

section Def

section Zero

/-- `FunLikeZero F α β` states for all `x : α`, `(0 : F) x = 0`. -/
class FunLikeZero (F : Type*) (α β : outParam Type*) [FunLike F α β] [Zero β] [Zero F] where
  zero_apply (x : α) : (0 : F) x = 0

attribute [simp] FunLikeZero.zero_apply

/-- `FunLikeOne F α β` states for all `x : α`, `(1 : F) x = 1`. -/
@[to_additive]
class FunLikeOne (F : Type*) (α β : outParam Type*) [FunLike F α β] [One β] [One F] where
  one_apply (x : α) : (1 : F) x = 1

attribute [simp] FunLikeOne.one_apply

end Zero

section Add

/-- `FunLikeAdd F α β` states for all `f g : F` and `x : α`, `(f + g) x = f x + g x`. -/
class FunLikeAdd (F : Type*) (α β : outParam Type*) [FunLike F α β] [Add β] [Add F] where
  add_apply (f g : F) (x : α) : (f + g) x = f x + g x

attribute [simp] FunLikeAdd.add_apply

/-- `FunLikeMul F α β` states for all `f g : F` and `x : α`, `(f * g) x = f x * g x`. -/
@[to_additive]
class FunLikeMul (F : Type*) (α β : outParam Type*) [FunLike F α β] [Mul β] [Mul F] where
  mul_apply (f g : F) (x : α) : (f * g) x = f x * g x

attribute [simp] FunLikeMul.mul_apply

end Add

section Sub

/-- `FunLikeSub F α β` states for all `f g : F` and `x : α`, `(f - g) x = f x - g x`. -/
class FunLikeSub (F : Type*) (α β : outParam Type*) [FunLike F α β] [Sub β] [Sub F] where
  sub_apply (f g : F) (x : α) : (f - g) x = f x - g x

attribute [simp] FunLikeSub.sub_apply

/-- `FunLikeDiv F α β` states for all `f g : F` and `x : α`, `(f / g) x = f x / g x`. -/
@[to_additive]
class FunLikeDiv (F : Type*) (α β : outParam Type*) [FunLike F α β] [Div β] [Div F] where
  div_apply (f g : F) (x : α) : (f / g) x = f x / g x

attribute [simp] FunLikeDiv.div_apply

end Sub

section Neg

/-- `FunLikeNeg F α β` states for all `f : F` and `x : α`, `(-f) x = -f x`. -/
class FunLikeNeg (F : Type*) (α β : outParam Type*) [FunLike F α β] [Neg β] [Neg F] where
  neg_apply (f : F) (x : α) : (-f) x = -f x

attribute [simp] FunLikeNeg.neg_apply

/-- `FunLikeInv F α β` states for all `f : F` and `x : α`, `f⁻¹ x = (f x)⁻¹`. -/
@[to_additive]
class FunLikeInv (F : Type*) (α β : outParam Type*) [FunLike F α β] [Inv β] [Inv F] where
  inv_apply (f : F) (x : α) : f⁻¹ x = (f x)⁻¹

attribute [simp] FunLikeInv.inv_apply

end Neg

section SMul

/-- `FunLikeVAdd M F α β` states for all `f : F`, `n : M` and `x : α`, `(n +ᵥ f) x = n +ᵥ f x`. -/
class FunLikeVAdd (M F : Type*) (α β : outParam Type*) [FunLike F α β] [VAdd M β] [VAdd M F] where
  vadd_apply (f : F) (n : M) (x : α) : (n +ᵥ f) x = n +ᵥ f x

attribute [simp] FunLikeVAdd.vadd_apply

/-- `FunLikeSMul M F α β` states for all `f : F`, `n : M` and `x : α`, `(n • f) x = n • f x`. -/
@[to_additive]
class FunLikeSMul (M F : Type*) (α β : outParam Type*) [FunLike F α β] [SMul M β] [SMul M F] where
  smul_apply (f : F) (n : M) (x : α) : (n • f) x = n • f x

attribute [simp] FunLikeSMul.smul_apply

/-- `FunLikePow M F α β` states for all `f : F`, `n : M` and `x : α`, `(f ^ n) x = (f x) ^ n`. -/
@[to_additive FunLikeSMul]
class FunLikePow (M F : Type*) (α β : outParam Type*) [FunLike F α β] [Pow β M] [Pow F M] where
  pow_apply (f : F) (n : M) (x : α) : (f ^ n) x = (f x) ^ n

attribute [simp] FunLikePow.pow_apply

end SMul

end Def

namespace FunLike

variable {M M' F α β : Type*} [FunLike F α β]

section Coercion

@[to_additive (attr := norm_cast)]
theorem coe_one [One F] [One β] [FunLikeOne F α β] : ↑(1 : F) = (1 : α → β) := by ext; simp

@[to_additive (attr := norm_cast)]
theorem coe_mul [Mul F] [Mul β] [FunLikeMul F α β] (f g : F) : ↑(f * g) = (f : α → β) * g := by
  ext; simp

@[to_additive (attr := norm_cast)]
theorem coe_div [Div F] [Div β] [FunLikeDiv F α β] (f g : F) : ↑(f / g) = (f : α → β) / g := by
  ext; simp

@[to_additive (attr := norm_cast)]
theorem coe_inv [Inv F] [Inv β] [FunLikeInv F α β] (f : F) : ↑(f⁻¹) = (f : α → β)⁻¹ := by
  ext; simp

@[to_additive (attr := norm_cast)]
theorem coe_smul [SMul M F] [SMul M β] [FunLikeSMul M F α β] (n : M) (f : F) :
    ↑(n • f) = n • (f : α → β) := by
  ext; simp

@[to_additive (attr := norm_cast) coe_smul']
theorem coe_pow [Pow F M] [Pow β M] [FunLikePow M F α β] (f : F) (n : M) :
    ↑(f ^ n) = (f : α → β) ^ n := by
  ext; simp

end Coercion

section CoercionHom

variable [MulOne F] [Monoid β] [FunLikeOne F α β] [FunLikeMul F α β]

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
