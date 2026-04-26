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

public section

namespace FunLike

variable {F α β : Type*} [FunLike F α β]

section Cast

/-- `IsNatCastApply F α β` states for all `n : ℕ` and `x : α`, `(n : F) x = n`. -/
class IsNatCastApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [AddMonoidWithOne β]
    [NatCast F] where
  natCast_apply (n : ℕ) (x : α) : (n : F) x = n

@[simp]
alias _root_.natCast_apply := IsNatCastApply.natCast_apply

theorem coe_natCast [AddMonoidWithOne β] [NatCast F] [IsNatCastApply F α β] (n : ℕ) :
  ↑(n : F) = (n : α → β) := by ext; simp only [natCast_apply]; rfl

/-- `IsIntCastApply F α β` states for all `n : ℤ` and `x : α`, `(n : F) x = n`. -/
class IsIntCastApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [AddGroupWithOne β]
    [IntCast F] where
  intCast_apply (n : ℤ) (x : α) : (n : F) x = n

@[simp]
alias _root_.intCast_apply := IsIntCastApply.intCast_apply

theorem coe_intCast [AddGroupWithOne β] [IntCast F] [IsIntCastApply F α β] (n : ℤ) :
  ↑(n : F) = (n : α → β) := by ext; simp only [intCast_apply]; rfl

end Cast

variable [Mul F]

instance instDistrib [Add F] [Distrib β] [IsMulApply F α β] [IsAddApply F α β] : Distrib F :=
  fast_instance% DFunLike.coe_injective.distrib (fun (f : F) ↦ (f : α → β)) coe_add coe_mul

instance instHasDistribNeg [Neg F] [Mul β] [HasDistribNeg β] [IsNegApply F α β]
    [IsMulApply F α β] : HasDistribNeg F :=
  fast_instance% DFunLike.coe_injective.hasDistribNeg (fun (f : F) ↦ (f : α → β)) coe_neg coe_mul

variable [Add F] [Zero F] [One F] [SMul ℕ F]

instance [NonUnitalNonAssocSemiring β] [IsZeroApply F α β] [IsAddApply F α β] [IsMulApply F α β]
    [IsSMulApply ℕ F α β] : NonUnitalNonAssocSemiring F :=
  fast_instance% DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul
    coe_smul

instance [NonUnitalSemiring β] [IsZeroApply F α β] [IsAddApply F α β] [IsMulApply F α β]
    [IsSMulApply ℕ F α β] : NonUnitalSemiring F :=
  fast_instance% DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul coe_smul

instance [NonUnitalCommSemiring β] [IsZeroApply F α β] [IsAddApply F α β] [IsMulApply F α β]
    [IsSMulApply ℕ F α β] : NonUnitalCommSemiring F :=
  fast_instance% DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul coe_smul

section NegSub

variable [Neg F] [Sub F] [SMul ℤ F]

instance [NonUnitalNonAssocRing β] [IsZeroApply F α β] [IsAddApply F α β] [IsMulApply F α β]
    [IsSMulApply ℕ F α β] [IsSMulApply ℤ F α β] [IsNegApply F α β] [IsSubApply F α β] :
    NonUnitalNonAssocRing F :=
  fast_instance% DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg
    coe_sub coe_smul coe_smul

instance [NonUnitalRing β] [IsZeroApply F α β] [IsAddApply F α β] [IsMulApply F α β]
    [IsSMulApply ℕ F α β] [IsSMulApply ℤ F α β] [IsNegApply F α β] [IsSubApply F α β] :
    NonUnitalRing F :=
  fast_instance% DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    coe_smul coe_smul

instance [NonUnitalCommRing β] [IsZeroApply F α β] [IsAddApply F α β] [IsMulApply F α β]
    [IsSMulApply ℕ F α β] [IsSMulApply ℤ F α β] [IsNegApply F α β] [IsSubApply F α β] :
    NonUnitalCommRing F :=
  fast_instance% DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    coe_smul coe_smul

end NegSub

variable [Pow F ℕ] [NatCast F]

instance [Semiring β] [IsZeroApply F α β] [IsOneApply F α β] [IsAddApply F α β] [IsMulApply F α β]
    [IsSMulApply ℕ F α β] [IsPowApply ℕ F α β] [IsNatCastApply F α β] :
    Semiring F :=
  fast_instance% DFunLike.coe_injective.semiring _ coe_zero coe_one coe_add coe_mul
    coe_smul coe_pow coe_natCast

variable [IntCast F] [Neg F] [Sub F] [SMul ℤ F]

instance [Ring β] [IsZeroApply F α β] [IsOneApply F α β] [IsAddApply F α β] [IsMulApply F α β]
    [IsNegApply F α β] [IsSubApply F α β] [IsSMulApply ℕ F α β] [IsSMulApply ℤ F α β]
    [IsPowApply ℕ F α β] [IsNatCastApply F α β] [IsIntCastApply F α β] :
    Ring F :=
  fast_instance% DFunLike.coe_injective.ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub
    coe_smul coe_smul coe_pow coe_natCast coe_intCast

instance [CommRing β] [IsZeroApply F α β] [IsOneApply F α β] [IsAddApply F α β] [IsMulApply F α β]
    [IsNegApply F α β] [IsSubApply F α β] [IsSMulApply ℕ F α β] [IsSMulApply ℤ F α β]
    [IsPowApply ℕ F α β] [IsNatCastApply F α β] [IsIntCastApply F α β] :
    CommRing F :=
  fast_instance% DFunLike.coe_injective.commRing _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub
    coe_smul coe_smul coe_pow coe_natCast coe_intCast

end FunLike
