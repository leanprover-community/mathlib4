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

/-! # Ring structure for `FunLike` -/

@[expose] public section

namespace FunLike

variable {F α β : Type*} [FunLike F α β]

section Cast

/-- `FunLikeNatCast F α β` states for all `n : ℕ` and `x : α`, `(n : F) x = n`. -/
class FunLikeNatCast (F : Type*) (α β : outParam Type*) [FunLike F α β] [AddMonoidWithOne β]
    [NatCast F] where
  natCast_apply (n : ℕ) (x : α) : (n : F) x = n

@[simp]
alias _root_.natCast_apply := FunLikeNatCast.natCast_apply

theorem coe_natCast [AddMonoidWithOne β] [NatCast F] [FunLikeNatCast F α β] (n : ℕ) :
  ↑(n : F) = (n : α → β) := by ext; simp only [natCast_apply]; rfl

/-- `FunLikeIntCast F α β` states for all `n : ℤ` and `x : α`, `(n : F) x = n`. -/
class FunLikeIntCast (F : Type*) (α β : outParam Type*) [FunLike F α β] [AddGroupWithOne β]
    [IntCast F] where
  intCast_apply (n : ℤ) (x : α) : (n : F) x = n

@[simp]
alias _root_.intCast_apply := FunLikeIntCast.intCast_apply

theorem coe_intCast [AddGroupWithOne β] [IntCast F] [FunLikeIntCast F α β] (n : ℤ) :
  ↑(n : F) = (n : α → β) := by ext; simp only [intCast_apply]; rfl

end Cast

variable [Mul F]

instance instDistrib [Add F] [Distrib β] [FunLikeMul F α β] [FunLikeAdd F α β] : Distrib F :=
  fast_instance% DFunLike.coe_injective.distrib (fun (f : F) ↦ (f : α → β)) coe_add coe_mul

instance instHasDistribNeg [Neg F] [Mul β] [Add β] [HasDistribNeg β] [FunLikeNeg F α β]
    [FunLikeMul F α β] : HasDistribNeg F :=
  fast_instance% DFunLike.coe_injective.hasDistribNeg (fun (f : F) ↦ (f : α → β)) coe_neg coe_mul

variable [Add F] [Zero F] [One F] [SMul ℕ F]

instance [NonUnitalNonAssocSemiring β] [FunLikeZero F α β] [FunLikeAdd F α β] [FunLikeMul F α β]
    [FunLikeSMul ℕ F α β] : NonUnitalNonAssocSemiring F :=
  fast_instance% DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul
    coe_smul

instance [NonUnitalSemiring β] [FunLikeZero F α β] [FunLikeAdd F α β] [FunLikeMul F α β]
    [FunLikeSMul ℕ F α β] : NonUnitalSemiring F :=
  fast_instance% DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul coe_smul

instance [NonUnitalCommSemiring β] [FunLikeZero F α β] [FunLikeAdd F α β] [FunLikeMul F α β]
    [FunLikeSMul ℕ F α β] : NonUnitalCommSemiring F :=
  fast_instance% DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul coe_smul

section NegSub

variable [Neg F] [Sub F] [SMul ℤ F]

instance [NonUnitalNonAssocRing β] [FunLikeZero F α β] [FunLikeAdd F α β] [FunLikeMul F α β]
    [FunLikeSMul ℕ F α β] [FunLikeSMul ℤ F α β] [FunLikeNeg F α β] [FunLikeSub F α β] :
    NonUnitalNonAssocRing F :=
  fast_instance% DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg
    coe_sub coe_smul coe_smul

instance [NonUnitalRing β] [FunLikeZero F α β] [FunLikeAdd F α β] [FunLikeMul F α β]
    [FunLikeSMul ℕ F α β] [FunLikeSMul ℤ F α β] [FunLikeNeg F α β] [FunLikeSub F α β] :
    NonUnitalRing F :=
  fast_instance% DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    coe_smul coe_smul

instance [NonUnitalCommRing β] [FunLikeZero F α β] [FunLikeAdd F α β] [FunLikeMul F α β]
    [FunLikeSMul ℕ F α β] [FunLikeSMul ℤ F α β] [FunLikeNeg F α β] [FunLikeSub F α β] :
    NonUnitalCommRing F :=
  fast_instance% DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    coe_smul coe_smul

end NegSub

variable [Pow F ℕ] [NatCast F]

instance [Semiring β] [FunLikeZero F α β] [FunLikeOne F α β] [FunLikeAdd F α β] [FunLikeMul F α β]
    [FunLikeSMul ℕ F α β] [FunLikeSMul ℕ F α β] [FunLikePow ℕ F α β] [FunLikeNatCast F α β] :
    Semiring F :=
  fast_instance% DFunLike.coe_injective.semiring _ coe_zero coe_one coe_add coe_mul
    coe_smul coe_pow coe_natCast

variable [IntCast F] [Neg F] [Sub F] [SMul ℤ F]

instance [Ring β] [FunLikeZero F α β] [FunLikeOne F α β] [FunLikeAdd F α β] [FunLikeMul F α β]
    [FunLikeNeg F α β] [FunLikeSub F α β] [FunLikeSMul ℕ F α β] [FunLikeSMul ℤ F α β]
    [FunLikePow ℕ F α β] [FunLikeNatCast F α β] [FunLikeIntCast F α β] :
    Ring F :=
  fast_instance% DFunLike.coe_injective.ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub
    coe_smul coe_smul coe_pow coe_natCast coe_intCast

instance [CommRing β] [FunLikeZero F α β] [FunLikeOne F α β] [FunLikeAdd F α β] [FunLikeMul F α β]
    [FunLikeNeg F α β] [FunLikeSub F α β] [FunLikeSMul ℕ F α β] [FunLikeSMul ℤ F α β]
    [FunLikePow ℕ F α β] [FunLikeNatCast F α β] [FunLikeIntCast F α β] :
    CommRing F :=
  fast_instance% DFunLike.coe_injective.commRing _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub
    coe_smul coe_smul coe_pow coe_natCast coe_intCast

end FunLike
