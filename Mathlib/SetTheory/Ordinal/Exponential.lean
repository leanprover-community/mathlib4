/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios

! This file was ported from Lean 3 source module set_theory.ordinal.exponential
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.SetTheory.Ordinal.Arithmetic

/-! # Ordinal exponential

In this file we define the power function and the logarithm function on ordinals,

-/


noncomputable section

open Function Cardinal Set Equiv Order

open Classical Cardinal Ordinal

universe u v w

namespace Ordinal

/-- The ordinal exponential, defined by transfinite recursion. -/
instance : Pow Ordinal Ordinal :=
  ⟨fun a b => if a = 0 then 1 - b else limitRecOn b 1 (fun _ IH => IH * a) fun b _ => bsup.{u, u} b⟩

-- mathport name: ordinal.pow
local infixr:0 "^" => @pow Ordinal Ordinal Ordinal.hasPow

/- warning: ordinal.opow_def -> Ordinal.opow_def is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{u1}) (b : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b) (ite.{succ (succ u1)} Ordinal.{u1} (Eq.{succ (succ u1)} Ordinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) (Quotient.decidableEq.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1} (fun (a : WellOrder.{u1}) (b : WellOrder.{u1}) => Classical.propDecidable (HasEquivₓ.Equiv.{succ (succ u1)} WellOrder.{u1} (setoidHasEquiv.{succ (succ u1)} WellOrder.{u1} Ordinal.isEquivalent.{u1}) a b)) a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) (HSub.hSub.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHSub.{succ u1} Ordinal.{u1} Ordinal.hasSub.{u1}) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) b) (Ordinal.limitRecOn.{u1, succ (succ u1)} (fun (_x : Ordinal.{u1}) => Ordinal.{u1}) b (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) (fun (_x : Ordinal.{u1}) (IH : Ordinal.{u1}) => HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) IH a) (fun (b : Ordinal.{u1}) (_x : Ordinal.IsLimit.{u1} b) => Ordinal.bsup.{u1, u1} b)))
but is expected to have type
  forall (a : Ordinal.{u1}) (b : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b) (ite.{succ (succ u1)} Ordinal.{u1} (Eq.{succ (succ u1)} Ordinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) (instDecidableEq.{succ u1} Ordinal.{u1} Ordinal.instLinearOrderOrdinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) (HSub.hSub.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHSub.{succ u1} Ordinal.{u1} Ordinal.instSubOrdinal.{u1}) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) b) (Ordinal.limitRecOn.{u1, succ (succ u1)} (fun (_x : Ordinal.{u1}) => Ordinal.{u1}) b (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) (fun (_x : Ordinal.{u1}) (IH : Ordinal.{u1}) => HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.instMonoidWithZeroOrdinal.{u1})))) IH a) (fun (b : Ordinal.{u1}) (_x : Ordinal.IsLimit.{u1} b) => Ordinal.bsup.{u1, u1} b)))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_def Ordinal.opow_defₓ'. -/
theorem opow_def (a b : Ordinal) :
    (a^b) = if a = 0 then 1 - b else limitRecOn b 1 (fun _ IH => IH * a) fun b _ => bsup.{u, u} b :=
  rfl
#align ordinal.opow_def Ordinal.opow_def

/- warning: ordinal.zero_opow' -> Ordinal.zero_opow' is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) a) (HSub.hSub.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHSub.{succ u1} Ordinal.{u1} Ordinal.hasSub.{u1}) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) a)
but is expected to have type
  forall (a : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1})) a) (HSub.hSub.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHSub.{succ u1} Ordinal.{u1} Ordinal.instSubOrdinal.{u1}) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) a)
Case conversion may be inaccurate. Consider using '#align ordinal.zero_opow' Ordinal.zero_opow'ₓ'. -/
theorem zero_opow' (a : Ordinal) : (0^a) = 1 - a := by simp only [opow_def, if_pos rfl]
#align ordinal.zero_opow' Ordinal.zero_opow'

/- warning: ordinal.zero_opow -> Ordinal.zero_opow is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) a) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))))
but is expected to have type
  forall {a : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) -> (Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1})) a) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1})))
Case conversion may be inaccurate. Consider using '#align ordinal.zero_opow Ordinal.zero_opowₓ'. -/
@[simp]
theorem zero_opow {a : Ordinal} (a0 : a ≠ 0) : (0^a) = 0 := by
  rwa [zero_opow', Ordinal.sub_eq_zero_iff_le, one_le_iff_ne_zero]
#align ordinal.zero_opow Ordinal.zero_opow

/- warning: ordinal.opow_zero -> Ordinal.opow_zero is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))
but is expected to have type
  forall (a : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_zero Ordinal.opow_zeroₓ'. -/
@[simp]
theorem opow_zero (a : Ordinal) : (a^0) = 1 := by
  by_cases a = 0 <;> [simp only [opow_def, if_pos h, sub_zero],
    simp only [opow_def, if_neg h, limit_rec_on_zero]]
#align ordinal.opow_zero Ordinal.opow_zero

/- warning: ordinal.opow_succ -> Ordinal.opow_succ is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{u1}) (b : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} b)) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b) a)
but is expected to have type
  forall (a : Ordinal.{u1}) (b : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1}) Ordinal.instSuccOrderOrdinalToPreorderInstPartialOrderOrdinal.{u1} b)) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.instMonoidWithZeroOrdinal.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b) a)
Case conversion may be inaccurate. Consider using '#align ordinal.opow_succ Ordinal.opow_succₓ'. -/
@[simp]
theorem opow_succ (a b : Ordinal) : (a^succ b) = (a^b) * a :=
  if h : a = 0 then by subst a <;> simp only [zero_opow (succ_ne_zero _), mul_zero]
  else by simp only [opow_def, limit_rec_on_succ, if_neg h]
#align ordinal.opow_succ Ordinal.opow_succ

/- warning: ordinal.opow_limit -> Ordinal.opow_limit is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (Ordinal.IsLimit.{u1} b) -> (Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b) (Ordinal.bsup.{u1, u1} b (fun (c : Ordinal.{u1}) (_x : LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) c b) => HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a c)))
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) -> (Ordinal.IsLimit.{u1} b) -> (Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b) (Ordinal.bsup.{u1, u1} b (fun (c : Ordinal.{u1}) (_x : LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) c b) => HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a c)))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_limit Ordinal.opow_limitₓ'. -/
theorem opow_limit {a b : Ordinal} (a0 : a ≠ 0) (h : IsLimit b) :
    (a^b) = bsup.{u, u} b fun c _ => a^c := by
  simp only [opow_def, if_neg a0] <;> rw [limit_rec_on_limit _ _ _ _ h] <;> rfl
#align ordinal.opow_limit Ordinal.opow_limit

/- warning: ordinal.opow_le_of_limit -> Ordinal.opow_le_of_limit is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}} {c : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (Ordinal.IsLimit.{u1} b) -> (Iff (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b) c) (forall (b' : Ordinal.{u1}), (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) b' b) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b') c)))
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}} {c : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) -> (Ordinal.IsLimit.{u1} b) -> (Iff (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b) c) (forall (b' : Ordinal.{u1}), (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) b' b) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b') c)))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_le_of_limit Ordinal.opow_le_of_limitₓ'. -/
theorem opow_le_of_limit {a b c : Ordinal} (a0 : a ≠ 0) (h : IsLimit b) :
    (a^b) ≤ c ↔ ∀ b' < b, (a^b') ≤ c := by rw [opow_limit a0 h, bsup_le_iff]
#align ordinal.opow_le_of_limit Ordinal.opow_le_of_limit

/- warning: ordinal.lt_opow_of_limit -> Ordinal.lt_opow_of_limit is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}} {c : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} b (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (Ordinal.IsLimit.{u1} c) -> (Iff (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) a (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b c)) (Exists.{succ (succ u1)} Ordinal.{u1} (fun (c' : Ordinal.{u1}) => Exists.{0} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) c' c) (fun (H : LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) c' c) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) a (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b c')))))
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}} {c : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} b (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) -> (Ordinal.IsLimit.{u1} c) -> (Iff (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) a (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b c)) (Exists.{succ (succ u1)} Ordinal.{u1} (fun (c' : Ordinal.{u1}) => And (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) c' c) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) a (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b c')))))
Case conversion may be inaccurate. Consider using '#align ordinal.lt_opow_of_limit Ordinal.lt_opow_of_limitₓ'. -/
theorem lt_opow_of_limit {a b c : Ordinal} (b0 : b ≠ 0) (h : IsLimit c) :
    a < (b^c) ↔ ∃ c' < c, a < (b^c') := by
  rw [← not_iff_not, not_exists] <;> simp only [not_lt, opow_le_of_limit b0 h, exists_prop, not_and]
#align ordinal.lt_opow_of_limit Ordinal.lt_opow_of_limit

/- warning: ordinal.opow_one -> Ordinal.opow_one is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))) a
but is expected to have type
  forall (a : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1}))) a
Case conversion may be inaccurate. Consider using '#align ordinal.opow_one Ordinal.opow_oneₓ'. -/
@[simp]
theorem opow_one (a : Ordinal) : (a^1) = a := by
  rw [← succ_zero, opow_succ] <;> simp only [opow_zero, one_mul]
#align ordinal.opow_one Ordinal.opow_one

/- warning: ordinal.one_opow -> Ordinal.one_opow is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) a) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))
but is expected to have type
  forall (a : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) a) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.one_opow Ordinal.one_opowₓ'. -/
@[simp]
theorem one_opow (a : Ordinal) : (1^a) = 1 :=
  by
  apply limit_rec_on a
  · simp only [opow_zero]
  · intro _ ih
    simp only [opow_succ, ih, mul_one]
  refine' fun b l IH => eq_of_forall_ge_iff fun c => _
  rw [opow_le_of_limit Ordinal.one_ne_zero l]
  exact ⟨fun H => by simpa only [opow_zero] using H 0 l.pos, fun H b' h => by rwa [IH _ h]⟩
#align ordinal.one_opow Ordinal.one_opow

/- warning: ordinal.opow_pos -> Ordinal.opow_pos is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} (b : Ordinal.{u1}), (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) a) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b))
but is expected to have type
  forall {a : Ordinal.{u1}} (b : Ordinal.{u1}), (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1})) a) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_pos Ordinal.opow_posₓ'. -/
theorem opow_pos {a : Ordinal} (b) (a0 : 0 < a) : 0 < (a^b) :=
  by
  have h0 : 0 < (a^0) := by simp only [opow_zero, zero_lt_one]
  apply limit_rec_on b
  · exact h0
  · intro b IH
    rw [opow_succ]
    exact mul_pos IH a0
  · exact fun b l _ => (lt_opow_of_limit (Ordinal.pos_iff_ne_zero.1 a0) l).2 ⟨0, l.Pos, h0⟩
#align ordinal.opow_pos Ordinal.opow_pos

/- warning: ordinal.opow_ne_zero -> Ordinal.opow_ne_zero is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} (b : Ordinal.{u1}), (Ne.{succ (succ u1)} Ordinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (Ne.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))))
but is expected to have type
  forall {a : Ordinal.{u1}} (b : Ordinal.{u1}), (Ne.{succ (succ u1)} Ordinal.{u1} a (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) -> (Ne.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1})))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_ne_zero Ordinal.opow_ne_zeroₓ'. -/
theorem opow_ne_zero {a : Ordinal} (b) (a0 : a ≠ 0) : (a^b) ≠ 0 :=
  Ordinal.pos_iff_ne_zero.1 <| opow_pos b <| Ordinal.pos_iff_ne_zero.2 a0
#align ordinal.opow_ne_zero Ordinal.opow_ne_zero

/- warning: ordinal.opow_is_normal -> Ordinal.opow_isNormal is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) a) -> (Ordinal.IsNormal.{u1, u1} (fun (_y : Ordinal.{u1}) => HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a _y))
but is expected to have type
  forall {a : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) a) -> (Ordinal.IsNormal.{u1, u1} ((fun (x._@.Mathlib.SetTheory.Ordinal.Arithmetic._hyg.30436 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Ordinal.Arithmetic._hyg.30438 : Ordinal.{u1}) => HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) x._@.Mathlib.SetTheory.Ordinal.Arithmetic._hyg.30436 x._@.Mathlib.SetTheory.Ordinal.Arithmetic._hyg.30438) a))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_is_normal Ordinal.opow_isNormalₓ'. -/
theorem opow_isNormal {a : Ordinal} (h : 1 < a) : IsNormal ((·^·) a) :=
  have a0 : 0 < a := zero_lt_one.trans h
  ⟨fun b => by simpa only [mul_one, opow_succ] using (mul_lt_mul_iff_left (opow_pos b a0)).2 h,
    fun b l c => opow_le_of_limit (ne_of_gt a0) l⟩
#align ordinal.opow_is_normal Ordinal.opow_isNormal

/- warning: ordinal.opow_lt_opow_iff_right -> Ordinal.opow_lt_opow_iff_right is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}} {c : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) a) -> (Iff (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a c)) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) b c))
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}} {c : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) a) -> (Iff (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a c)) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) b c))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_lt_opow_iff_right Ordinal.opow_lt_opow_iff_rightₓ'. -/
theorem opow_lt_opow_iff_right {a b c : Ordinal} (a1 : 1 < a) : (a^b) < (a^c) ↔ b < c :=
  (opow_isNormal a1).lt_iff
#align ordinal.opow_lt_opow_iff_right Ordinal.opow_lt_opow_iff_right

/- warning: ordinal.opow_le_opow_iff_right -> Ordinal.opow_le_opow_iff_right is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}} {c : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) a) -> (Iff (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a c)) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) b c))
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}} {c : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) a) -> (Iff (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a c)) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) b c))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_le_opow_iff_right Ordinal.opow_le_opow_iff_rightₓ'. -/
theorem opow_le_opow_iff_right {a b c : Ordinal} (a1 : 1 < a) : (a^b) ≤ (a^c) ↔ b ≤ c :=
  (opow_isNormal a1).le_iff
#align ordinal.opow_le_opow_iff_right Ordinal.opow_le_opow_iff_right

/- warning: ordinal.opow_right_inj -> Ordinal.opow_right_inj is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}} {c : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) a) -> (Iff (Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a c)) (Eq.{succ (succ u1)} Ordinal.{u1} b c))
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}} {c : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) a) -> (Iff (Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a c)) (Eq.{succ (succ u1)} Ordinal.{u1} b c))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_right_inj Ordinal.opow_right_injₓ'. -/
theorem opow_right_inj {a b c : Ordinal} (a1 : 1 < a) : (a^b) = (a^c) ↔ b = c :=
  (opow_isNormal a1).inj
#align ordinal.opow_right_inj Ordinal.opow_right_inj

/- warning: ordinal.opow_is_limit -> Ordinal.opow_isLimit is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) a) -> (Ordinal.IsLimit.{u1} b) -> (Ordinal.IsLimit.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b))
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) a) -> (Ordinal.IsLimit.{u1} b) -> (Ordinal.IsLimit.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_is_limit Ordinal.opow_isLimitₓ'. -/
theorem opow_isLimit {a b : Ordinal} (a1 : 1 < a) : IsLimit b → IsLimit (a^b) :=
  (opow_isNormal a1).IsLimit
#align ordinal.opow_is_limit Ordinal.opow_isLimit

/- warning: ordinal.opow_is_limit_left -> Ordinal.opow_isLimit_left is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, (Ordinal.IsLimit.{u1} a) -> (Ne.{succ (succ u1)} Ordinal.{u1} b (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (Ordinal.IsLimit.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b))
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}}, (Ordinal.IsLimit.{u1} a) -> (Ne.{succ (succ u1)} Ordinal.{u1} b (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) -> (Ordinal.IsLimit.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_is_limit_left Ordinal.opow_isLimit_leftₓ'. -/
theorem opow_isLimit_left {a b : Ordinal} (l : IsLimit a) (hb : b ≠ 0) : IsLimit (a^b) :=
  by
  rcases zero_or_succ_or_limit b with (e | ⟨b, rfl⟩ | l')
  · exact absurd e hb
  · rw [opow_succ]
    exact mul_is_limit (opow_pos _ l.pos) l
  · exact opow_is_limit l.one_lt l'
#align ordinal.opow_is_limit_left Ordinal.opow_isLimit_left

/- warning: ordinal.opow_le_opow_right -> Ordinal.opow_le_opow_right is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}} {c : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) a) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) b c) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a c))
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}} {c : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1})) a) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) b c) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a c))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_le_opow_right Ordinal.opow_le_opow_rightₓ'. -/
theorem opow_le_opow_right {a b c : Ordinal} (h₁ : 0 < a) (h₂ : b ≤ c) : (a^b) ≤ (a^c) :=
  by
  cases' lt_or_eq_of_le (one_le_iff_pos.2 h₁) with h₁ h₁
  · exact (opow_le_opow_iff_right h₁).2 h₂
  · subst a
    simp only [one_opow]
#align ordinal.opow_le_opow_right Ordinal.opow_le_opow_right

/- warning: ordinal.opow_le_opow_left -> Ordinal.opow_le_opow_left is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}} (c : Ordinal.{u1}), (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) a b) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a c) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b c))
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}} (c : Ordinal.{u1}), (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) a b) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a c) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b c))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_le_opow_left Ordinal.opow_le_opow_leftₓ'. -/
theorem opow_le_opow_left {a b : Ordinal} (c) (ab : a ≤ b) : (a^c) ≤ (b^c) :=
  by
  by_cases a0 : a = 0
  · subst a
    by_cases c0 : c = 0
    · subst c
      simp only [opow_zero]
    · simp only [zero_opow c0, Ordinal.zero_le]
  · apply limit_rec_on c
    · simp only [opow_zero]
    · intro c IH
      simpa only [opow_succ] using mul_le_mul' IH ab
    ·
      exact fun c l IH =>
        (opow_le_of_limit a0 l).2 fun b' h =>
          (IH _ h).trans (opow_le_opow_right ((Ordinal.pos_iff_ne_zero.2 a0).trans_le ab) h.le)
#align ordinal.opow_le_opow_left Ordinal.opow_le_opow_left

/- warning: ordinal.left_le_opow -> Ordinal.left_le_opow is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{u1}) {b : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) b) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) a (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b))
but is expected to have type
  forall (a : Ordinal.{u1}) {b : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1})) b) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) a (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b))
Case conversion may be inaccurate. Consider using '#align ordinal.left_le_opow Ordinal.left_le_opowₓ'. -/
theorem left_le_opow (a : Ordinal) {b : Ordinal} (b1 : 0 < b) : a ≤ (a^b) :=
  by
  nth_rw 1 [← opow_one a]
  cases' le_or_gt a 1 with a1 a1
  · cases' lt_or_eq_of_le a1 with a0 a1
    · rw [lt_one_iff_zero] at a0
      rw [a0, zero_opow Ordinal.one_ne_zero]
      exact Ordinal.zero_le _
    rw [a1, one_opow, one_opow]
  rwa [opow_le_opow_iff_right a1, one_le_iff_pos]
#align ordinal.left_le_opow Ordinal.left_le_opow

/- warning: ordinal.right_le_opow -> Ordinal.right_le_opow is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} (b : Ordinal.{u1}), (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) a) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) b (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b))
but is expected to have type
  forall {a : Ordinal.{u1}} (b : Ordinal.{u1}), (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) a) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) b (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b))
Case conversion may be inaccurate. Consider using '#align ordinal.right_le_opow Ordinal.right_le_opowₓ'. -/
theorem right_le_opow {a : Ordinal} (b) (a1 : 1 < a) : b ≤ (a^b) :=
  (opow_isNormal a1).self_le _
#align ordinal.right_le_opow Ordinal.right_le_opow

/- warning: ordinal.opow_lt_opow_left_of_succ -> Ordinal.opow_lt_opow_left_of_succ is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}} {c : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) a b) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} c)) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} c)))
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}} {c : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) a b) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1}) Ordinal.instSuccOrderOrdinalToPreorderInstPartialOrderOrdinal.{u1} c)) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1}) Ordinal.instSuccOrderOrdinalToPreorderInstPartialOrderOrdinal.{u1} c)))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_lt_opow_left_of_succ Ordinal.opow_lt_opow_left_of_succₓ'. -/
theorem opow_lt_opow_left_of_succ {a b c : Ordinal} (ab : a < b) : (a^succ c) < (b^succ c) :=
  by
  rw [opow_succ, opow_succ]
  exact
    (mul_le_mul_right' (opow_le_opow_left c ab.le) a).trans_lt
      (mul_lt_mul_of_pos_left ab (opow_pos c ((Ordinal.zero_le a).trans_lt ab)))
#align ordinal.opow_lt_opow_left_of_succ Ordinal.opow_lt_opow_left_of_succ

/- warning: ordinal.opow_add -> Ordinal.opow_add is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{u1}) (b : Ordinal.{u1}) (c : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) b c)) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a c))
but is expected to have type
  forall (a : Ordinal.{u1}) (b : Ordinal.{u1}) (c : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.instAddOrdinal.{u1}) b c)) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.instMonoidWithZeroOrdinal.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a c))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_add Ordinal.opow_addₓ'. -/
theorem opow_add (a b c : Ordinal) : (a^b + c) = (a^b) * (a^c) :=
  by
  rcases eq_or_ne a 0 with (rfl | a0)
  · rcases eq_or_ne c 0 with (rfl | c0)
    · simp
    have : b + c ≠ 0 := ((Ordinal.pos_iff_ne_zero.2 c0).trans_le (le_add_left _ _)).ne'
    simp only [zero_opow c0, zero_opow this, mul_zero]
  rcases eq_or_lt_of_le (one_le_iff_ne_zero.2 a0) with (rfl | a1)
  · simp only [one_opow, mul_one]
  apply limit_rec_on c
  · simp
  · intro c IH
    rw [add_succ, opow_succ, IH, opow_succ, mul_assoc]
  · intro c l IH
    refine'
      eq_of_forall_ge_iff fun d =>
        (((opow_is_normal a1).trans (add_is_normal b)).limit_le l).trans _
    dsimp only [Function.comp]
    simp (config := { contextual := true }) only [IH]
    exact
      (((mul_is_normal <| opow_pos b (Ordinal.pos_iff_ne_zero.2 a0)).trans
              (opow_is_normal a1)).limit_le
          l).symm
#align ordinal.opow_add Ordinal.opow_add

/- warning: ordinal.opow_one_add -> Ordinal.opow_one_add is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{u1}) (b : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) b)) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) a (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b))
but is expected to have type
  forall (a : Ordinal.{u1}) (b : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.instAddOrdinal.{u1}) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) b)) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.instMonoidWithZeroOrdinal.{u1})))) a (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_one_add Ordinal.opow_one_addₓ'. -/
theorem opow_one_add (a b : Ordinal) : (a^1 + b) = a * (a^b) := by rw [opow_add, opow_one]
#align ordinal.opow_one_add Ordinal.opow_one_add

/- warning: ordinal.opow_dvd_opow -> Ordinal.opow_dvd_opow is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{u1}) {b : Ordinal.{u1}} {c : Ordinal.{u1}}, (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) b c) -> (Dvd.Dvd.{succ u1} Ordinal.{u1} (semigroupDvd.{succ u1} Ordinal.{u1} (SemigroupWithZero.toSemigroup.{succ u1} Ordinal.{u1} (MonoidWithZero.toSemigroupWithZero.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1}))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a c))
but is expected to have type
  forall (a : Ordinal.{u1}) {b : Ordinal.{u1}} {c : Ordinal.{u1}}, (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) b c) -> (Dvd.dvd.{succ u1} Ordinal.{u1} (semigroupDvd.{succ u1} Ordinal.{u1} (SemigroupWithZero.toSemigroup.{succ u1} Ordinal.{u1} (MonoidWithZero.toSemigroupWithZero.{succ u1} Ordinal.{u1} Ordinal.instMonoidWithZeroOrdinal.{u1}))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a c))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_dvd_opow Ordinal.opow_dvd_opowₓ'. -/
theorem opow_dvd_opow (a) {b c : Ordinal} (h : b ≤ c) : (a^b) ∣ (a^c) :=
  by
  rw [← Ordinal.add_sub_cancel_of_le h, opow_add]
  apply dvd_mul_right
#align ordinal.opow_dvd_opow Ordinal.opow_dvd_opow

/- warning: ordinal.opow_dvd_opow_iff -> Ordinal.opow_dvd_opow_iff is a dubious translation:
lean 3 declaration is
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}} {c : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) a) -> (Iff (Dvd.Dvd.{succ u1} Ordinal.{u1} (semigroupDvd.{succ u1} Ordinal.{u1} (SemigroupWithZero.toSemigroup.{succ u1} Ordinal.{u1} (MonoidWithZero.toSemigroupWithZero.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1}))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a c)) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) b c))
but is expected to have type
  forall {a : Ordinal.{u1}} {b : Ordinal.{u1}} {c : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) a) -> (Iff (Dvd.dvd.{succ u1} Ordinal.{u1} (semigroupDvd.{succ u1} Ordinal.{u1} (SemigroupWithZero.toSemigroup.{succ u1} Ordinal.{u1} (MonoidWithZero.toSemigroupWithZero.{succ u1} Ordinal.{u1} Ordinal.instMonoidWithZeroOrdinal.{u1}))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a c)) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) b c))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_dvd_opow_iff Ordinal.opow_dvd_opow_iffₓ'. -/
theorem opow_dvd_opow_iff {a b c : Ordinal} (a1 : 1 < a) : (a^b) ∣ (a^c) ↔ b ≤ c :=
  ⟨fun h =>
    le_of_not_lt fun hn =>
      not_le_of_lt ((opow_lt_opow_iff_right a1).2 hn) <|
        le_of_dvd (opow_ne_zero _ <| one_le_iff_ne_zero.1 <| a1.le) h,
    opow_dvd_opow _⟩
#align ordinal.opow_dvd_opow_iff Ordinal.opow_dvd_opow_iff

/- warning: ordinal.opow_mul -> Ordinal.opow_mul is a dubious translation:
lean 3 declaration is
  forall (a : Ordinal.{u1}) (b : Ordinal.{u1}) (c : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) b c)) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) a b) c)
but is expected to have type
  forall (a : Ordinal.{u1}) (b : Ordinal.{u1}) (c : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.instMonoidWithZeroOrdinal.{u1})))) b c)) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) a b) c)
Case conversion may be inaccurate. Consider using '#align ordinal.opow_mul Ordinal.opow_mulₓ'. -/
theorem opow_mul (a b c : Ordinal) : (a^b * c) = ((a^b)^c) :=
  by
  by_cases b0 : b = 0; · simp only [b0, zero_mul, opow_zero, one_opow]
  by_cases a0 : a = 0
  · subst a
    by_cases c0 : c = 0
    · simp only [c0, mul_zero, opow_zero]
    simp only [zero_opow b0, zero_opow c0, zero_opow (mul_ne_zero b0 c0)]
  cases' eq_or_lt_of_le (one_le_iff_ne_zero.2 a0) with a1 a1
  · subst a1
    simp only [one_opow]
  apply limit_rec_on c
  · simp only [mul_zero, opow_zero]
  · intro c IH
    rw [mul_succ, opow_add, IH, opow_succ]
  · intro c l IH
    refine'
      eq_of_forall_ge_iff fun d =>
        (((opow_is_normal a1).trans (mul_is_normal (Ordinal.pos_iff_ne_zero.2 b0))).limit_le
              l).trans
          _
    dsimp only [Function.comp]
    simp (config := { contextual := true }) only [IH]
    exact (opow_le_of_limit (opow_ne_zero _ a0) l).symm
#align ordinal.opow_mul Ordinal.opow_mul

/-! ### Ordinal logarithm -/


#print Ordinal.log /-
/-- The ordinal logarithm is the solution `u` to the equation `x = b ^ u * v + w` where `v < b` and
    `w < b ^ u`. -/
@[pp_nodot]
def log (b : Ordinal) (x : Ordinal) : Ordinal :=
  if h : 1 < b then pred (infₛ { o | x < (b^o) }) else 0
#align ordinal.log Ordinal.log
-/

/- warning: ordinal.log_nonempty -> Ordinal.log_nonempty is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} {x : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) b) -> (Set.Nonempty.{succ u1} Ordinal.{u1} (setOf.{succ u1} Ordinal.{u1} (fun (o : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b o))))
but is expected to have type
  forall {b : Ordinal.{u1}} {x : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) b) -> (Set.Nonempty.{succ u1} Ordinal.{u1} (setOf.{succ u1} Ordinal.{u1} (fun (o : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) x (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b o))))
Case conversion may be inaccurate. Consider using '#align ordinal.log_nonempty Ordinal.log_nonemptyₓ'. -/
/-- The set in the definition of `log` is nonempty. -/
theorem log_nonempty {b x : Ordinal} (h : 1 < b) : { o | x < (b^o) }.Nonempty :=
  ⟨_, succ_le_iff.1 (right_le_opow _ h)⟩
#align ordinal.log_nonempty Ordinal.log_nonempty

/- warning: ordinal.log_def -> Ordinal.log_def is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) b) -> (forall (x : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.log.{u1} b x) (Ordinal.pred.{u1} (InfSet.infₛ.{succ u1} Ordinal.{u1} (ConditionallyCompleteLattice.toHasInf.{succ u1} Ordinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Ordinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Ordinal.{u1} Ordinal.conditionallyCompleteLinearOrderBot.{u1}))) (setOf.{succ u1} Ordinal.{u1} (fun (o : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b o))))))
but is expected to have type
  forall {b : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) b) -> (forall (x : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.log.{u1} b x) (Ordinal.pred.{u1} (InfSet.infₛ.{succ u1} Ordinal.{u1} (ConditionallyCompleteLattice.toInfSet.{succ u1} Ordinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Ordinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Ordinal.{u1} Ordinal.instConditionallyCompleteLinearOrderBotOrdinal.{u1}))) (setOf.{succ u1} Ordinal.{u1} (fun (o : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) x (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b o))))))
Case conversion may be inaccurate. Consider using '#align ordinal.log_def Ordinal.log_defₓ'. -/
theorem log_def {b : Ordinal} (h : 1 < b) (x : Ordinal) : log b x = pred (infₛ { o | x < (b^o) }) :=
  by simp only [log, dif_pos h]
#align ordinal.log_def Ordinal.log_def

/- warning: ordinal.log_of_not_one_lt_left -> Ordinal.log_of_not_one_lt_left is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}}, (Not (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) b)) -> (forall (x : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.log.{u1} b x) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))))
but is expected to have type
  forall {b : Ordinal.{u1}}, (Not (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) b)) -> (forall (x : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.log.{u1} b x) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1})))
Case conversion may be inaccurate. Consider using '#align ordinal.log_of_not_one_lt_left Ordinal.log_of_not_one_lt_leftₓ'. -/
theorem log_of_not_one_lt_left {b : Ordinal} (h : ¬1 < b) (x : Ordinal) : log b x = 0 := by
  simp only [log, dif_neg h]
#align ordinal.log_of_not_one_lt_left Ordinal.log_of_not_one_lt_left

/- warning: ordinal.log_of_left_le_one -> Ordinal.log_of_left_le_one is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}}, (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) b (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))) -> (forall (x : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.log.{u1} b x) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))))
but is expected to have type
  forall {b : Ordinal.{u1}}, (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) b (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1}))) -> (forall (x : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.log.{u1} b x) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1})))
Case conversion may be inaccurate. Consider using '#align ordinal.log_of_left_le_one Ordinal.log_of_left_le_oneₓ'. -/
theorem log_of_left_le_one {b : Ordinal} (h : b ≤ 1) : ∀ x, log b x = 0 :=
  log_of_not_one_lt_left h.not_lt
#align ordinal.log_of_left_le_one Ordinal.log_of_left_le_one

#print Ordinal.log_zero_left /-
@[simp]
theorem log_zero_left : ∀ b, log 0 b = 0 :=
  log_of_left_le_one zero_le_one
#align ordinal.log_zero_left Ordinal.log_zero_left
-/

#print Ordinal.log_zero_right /-
@[simp]
theorem log_zero_right (b : Ordinal) : log b 0 = 0 :=
  if b1 : 1 < b then by
    rw [log_def b1, ← Ordinal.le_zero, pred_le]
    apply cinfₛ_le'
    dsimp
    rw [succ_zero, opow_one]
    exact zero_lt_one.trans b1
  else by simp only [log_of_not_one_lt_left b1]
#align ordinal.log_zero_right Ordinal.log_zero_right
-/

/- warning: ordinal.log_one_left -> Ordinal.log_one_left is a dubious translation:
lean 3 declaration is
  forall (b : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.log.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) b) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))
but is expected to have type
  forall (b : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.log.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) b) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.log_one_left Ordinal.log_one_leftₓ'. -/
@[simp]
theorem log_one_left : ∀ b, log 1 b = 0 :=
  log_of_left_le_one le_rfl
#align ordinal.log_one_left Ordinal.log_one_left

/- warning: ordinal.succ_log_def -> Ordinal.succ_log_def is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} {x : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) b) -> (Ne.{succ (succ u1)} Ordinal.{u1} x (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (Eq.{succ (succ u1)} Ordinal.{u1} (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} (Ordinal.log.{u1} b x)) (InfSet.infₛ.{succ u1} Ordinal.{u1} (ConditionallyCompleteLattice.toHasInf.{succ u1} Ordinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Ordinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Ordinal.{u1} Ordinal.conditionallyCompleteLinearOrderBot.{u1}))) (setOf.{succ u1} Ordinal.{u1} (fun (o : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b o)))))
but is expected to have type
  forall {b : Ordinal.{u1}} {x : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) b) -> (Ne.{succ (succ u1)} Ordinal.{u1} x (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) -> (Eq.{succ (succ u1)} Ordinal.{u1} (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1}) Ordinal.instSuccOrderOrdinalToPreorderInstPartialOrderOrdinal.{u1} (Ordinal.log.{u1} b x)) (InfSet.infₛ.{succ u1} Ordinal.{u1} (ConditionallyCompleteLattice.toInfSet.{succ u1} Ordinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Ordinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Ordinal.{u1} Ordinal.instConditionallyCompleteLinearOrderBotOrdinal.{u1}))) (setOf.{succ u1} Ordinal.{u1} (fun (o : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) x (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b o)))))
Case conversion may be inaccurate. Consider using '#align ordinal.succ_log_def Ordinal.succ_log_defₓ'. -/
theorem succ_log_def {b x : Ordinal} (hb : 1 < b) (hx : x ≠ 0) :
    succ (log b x) = infₛ { o | x < (b^o) } :=
  by
  let t := Inf { o | x < (b^o) }
  have : x < (b^t) := cinfₛ_mem (log_nonempty hb)
  rcases zero_or_succ_or_limit t with (h | h | h)
  · refine' ((one_le_iff_ne_zero.2 hx).not_lt _).elim
    simpa only [h, opow_zero]
  · rw [show log b x = pred t from log_def hb x, succ_pred_iff_is_succ.2 h]
  · rcases(lt_opow_of_limit (zero_lt_one.trans hb).ne' h).1 this with ⟨a, h₁, h₂⟩
    exact h₁.not_le.elim ((le_cinfₛ_iff'' (log_nonempty hb)).1 le_rfl a h₂)
#align ordinal.succ_log_def Ordinal.succ_log_def

/- warning: ordinal.lt_opow_succ_log_self -> Ordinal.lt_opow_succ_log_self is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) b) -> (forall (x : Ordinal.{u1}), LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} (Ordinal.log.{u1} b x))))
but is expected to have type
  forall {b : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) b) -> (forall (x : Ordinal.{u1}), LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) x (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1}) Ordinal.instSuccOrderOrdinalToPreorderInstPartialOrderOrdinal.{u1} (Ordinal.log.{u1} b x))))
Case conversion may be inaccurate. Consider using '#align ordinal.lt_opow_succ_log_self Ordinal.lt_opow_succ_log_selfₓ'. -/
theorem lt_opow_succ_log_self {b : Ordinal} (hb : 1 < b) (x : Ordinal) : x < (b^succ (log b x)) :=
  by
  rcases eq_or_ne x 0 with (rfl | hx)
  · apply opow_pos _ (zero_lt_one.trans hb)
  · rw [succ_log_def hb hx]
    exact cinfₛ_mem (log_nonempty hb)
#align ordinal.lt_opow_succ_log_self Ordinal.lt_opow_succ_log_self

/- warning: ordinal.opow_log_le_self -> Ordinal.opow_log_le_self is a dubious translation:
lean 3 declaration is
  forall (b : Ordinal.{u1}) {x : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} x (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b (Ordinal.log.{u1} b x)) x)
but is expected to have type
  forall (b : Ordinal.{u1}) {x : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} x (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b (Ordinal.log.{u1} b x)) x)
Case conversion may be inaccurate. Consider using '#align ordinal.opow_log_le_self Ordinal.opow_log_le_selfₓ'. -/
theorem opow_log_le_self (b) {x : Ordinal} (hx : x ≠ 0) : (b^log b x) ≤ x :=
  by
  rcases eq_or_ne b 0 with (rfl | b0)
  · rw [zero_opow']
    refine' (sub_le_self _ _).trans (one_le_iff_ne_zero.2 hx)
  rcases lt_or_eq_of_le (one_le_iff_ne_zero.2 b0) with (hb | rfl)
  · refine' le_of_not_lt fun h => (lt_succ (log b x)).not_le _
    have := @cinfₛ_le' _ _ { o | x < (b^o) } _ h
    rwa [← succ_log_def hb hx] at this
  · rwa [one_opow, one_le_iff_ne_zero]
#align ordinal.opow_log_le_self Ordinal.opow_log_le_self

/- warning: ordinal.opow_le_iff_le_log -> Ordinal.opow_le_iff_le_log is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} {x : Ordinal.{u1}} {c : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) b) -> (Ne.{succ (succ u1)} Ordinal.{u1} x (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (Iff (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b c) x) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) c (Ordinal.log.{u1} b x)))
but is expected to have type
  forall {b : Ordinal.{u1}} {x : Ordinal.{u1}} {c : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) b) -> (Ne.{succ (succ u1)} Ordinal.{u1} x (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) -> (Iff (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b c) x) (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) c (Ordinal.log.{u1} b x)))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_le_iff_le_log Ordinal.opow_le_iff_le_logₓ'. -/
/-- `opow b` and `log b` (almost) form a Galois connection. -/
theorem opow_le_iff_le_log {b x c : Ordinal} (hb : 1 < b) (hx : x ≠ 0) : (b^c) ≤ x ↔ c ≤ log b x :=
  ⟨fun h =>
    le_of_not_lt fun hn =>
      (lt_opow_succ_log_self hb x).not_le <|
        ((opow_le_opow_iff_right hb).2 (succ_le_of_lt hn)).trans h,
    fun h => ((opow_le_opow_iff_right hb).2 h).trans (opow_log_le_self b hx)⟩
#align ordinal.opow_le_iff_le_log Ordinal.opow_le_iff_le_log

/- warning: ordinal.lt_opow_iff_log_lt -> Ordinal.lt_opow_iff_log_lt is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} {x : Ordinal.{u1}} {c : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) b) -> (Ne.{succ (succ u1)} Ordinal.{u1} x (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (Iff (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b c)) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (Ordinal.log.{u1} b x) c))
but is expected to have type
  forall {b : Ordinal.{u1}} {x : Ordinal.{u1}} {c : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) b) -> (Ne.{succ (succ u1)} Ordinal.{u1} x (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) -> (Iff (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) x (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b c)) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (Ordinal.log.{u1} b x) c))
Case conversion may be inaccurate. Consider using '#align ordinal.lt_opow_iff_log_lt Ordinal.lt_opow_iff_log_ltₓ'. -/
theorem lt_opow_iff_log_lt {b x c : Ordinal} (hb : 1 < b) (hx : x ≠ 0) : x < (b^c) ↔ log b x < c :=
  lt_iff_lt_of_le_iff_le (opow_le_iff_le_log hb hx)
#align ordinal.lt_opow_iff_log_lt Ordinal.lt_opow_iff_log_lt

/- warning: ordinal.log_pos -> Ordinal.log_pos is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) b) -> (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) b o) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (Ordinal.log.{u1} b o))
but is expected to have type
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) b) -> (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) b o) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1})) (Ordinal.log.{u1} b o))
Case conversion may be inaccurate. Consider using '#align ordinal.log_pos Ordinal.log_posₓ'. -/
theorem log_pos {b o : Ordinal} (hb : 1 < b) (ho : o ≠ 0) (hbo : b ≤ o) : 0 < log b o := by
  rwa [← succ_le_iff, succ_zero, ← opow_le_iff_le_log hb ho, opow_one]
#align ordinal.log_pos Ordinal.log_pos

/- warning: ordinal.log_eq_zero -> Ordinal.log_eq_zero is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o b) -> (Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.log.{u1} b o) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))))
but is expected to have type
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) o b) -> (Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.log.{u1} b o) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1})))
Case conversion may be inaccurate. Consider using '#align ordinal.log_eq_zero Ordinal.log_eq_zeroₓ'. -/
theorem log_eq_zero {b o : Ordinal} (hbo : o < b) : log b o = 0 :=
  by
  rcases eq_or_ne o 0 with (rfl | ho)
  · exact log_zero_right b
  cases' le_or_lt b 1 with hb hb
  · rcases le_one_iff.1 hb with (rfl | rfl)
    · exact log_zero_left o
    · exact log_one_left o
  · rwa [← Ordinal.le_zero, ← lt_succ_iff, succ_zero, ← lt_opow_iff_log_lt hb ho, opow_one]
#align ordinal.log_eq_zero Ordinal.log_eq_zero

/- warning: ordinal.log_mono_right -> Ordinal.log_mono_right is a dubious translation:
lean 3 declaration is
  forall (b : Ordinal.{u1}) {x : Ordinal.{u1}} {y : Ordinal.{u1}}, (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x y) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (Ordinal.log.{u1} b x) (Ordinal.log.{u1} b y))
but is expected to have type
  forall (b : Ordinal.{u1}) {x : Ordinal.{u1}} {y : Ordinal.{u1}}, (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) x y) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (Ordinal.log.{u1} b x) (Ordinal.log.{u1} b y))
Case conversion may be inaccurate. Consider using '#align ordinal.log_mono_right Ordinal.log_mono_rightₓ'. -/
@[mono]
theorem log_mono_right (b) {x y : Ordinal} (xy : x ≤ y) : log b x ≤ log b y :=
  if hx : x = 0 then by simp only [hx, log_zero_right, Ordinal.zero_le]
  else
    if hb : 1 < b then
      (opow_le_iff_le_log hb (lt_of_lt_of_le (Ordinal.pos_iff_ne_zero.2 hx) xy).ne').1 <|
        (opow_log_le_self _ hx).trans xy
    else by simp only [log_of_not_one_lt_left hb, Ordinal.zero_le]
#align ordinal.log_mono_right Ordinal.log_mono_right

/- warning: ordinal.log_le_self -> Ordinal.log_le_self is a dubious translation:
lean 3 declaration is
  forall (b : Ordinal.{u1}) (x : Ordinal.{u1}), LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (Ordinal.log.{u1} b x) x
but is expected to have type
  forall (b : Ordinal.{u1}) (x : Ordinal.{u1}), LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (Ordinal.log.{u1} b x) x
Case conversion may be inaccurate. Consider using '#align ordinal.log_le_self Ordinal.log_le_selfₓ'. -/
theorem log_le_self (b x : Ordinal) : log b x ≤ x :=
  if hx : x = 0 then by simp only [hx, log_zero_right, Ordinal.zero_le]
  else
    if hb : 1 < b then (right_le_opow _ hb).trans (opow_log_le_self b hx)
    else by simp only [log_of_not_one_lt_left hb, Ordinal.zero_le]
#align ordinal.log_le_self Ordinal.log_le_self

/- warning: ordinal.log_one_right -> Ordinal.log_one_right is a dubious translation:
lean 3 declaration is
  forall (b : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.log.{u1} b (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))
but is expected to have type
  forall (b : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.log.{u1} b (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1}))) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.log_one_right Ordinal.log_one_rightₓ'. -/
@[simp]
theorem log_one_right (b : Ordinal) : log b 1 = 0 :=
  if hb : 1 < b then log_eq_zero hb else log_of_not_one_lt_left hb 1
#align ordinal.log_one_right Ordinal.log_one_right

/- warning: ordinal.mod_opow_log_lt_self -> Ordinal.mod_opow_log_lt_self is a dubious translation:
lean 3 declaration is
  forall (b : Ordinal.{u1}) {o : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HMod.hMod.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMod.{succ u1} Ordinal.{u1} Ordinal.hasMod.{u1}) o (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b (Ordinal.log.{u1} b o))) o)
but is expected to have type
  forall (b : Ordinal.{u1}) {o : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (HMod.hMod.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMod.{succ u1} Ordinal.{u1} Ordinal.instModOrdinal.{u1}) o (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b (Ordinal.log.{u1} b o))) o)
Case conversion may be inaccurate. Consider using '#align ordinal.mod_opow_log_lt_self Ordinal.mod_opow_log_lt_selfₓ'. -/
theorem mod_opow_log_lt_self (b : Ordinal) {o : Ordinal} (ho : o ≠ 0) : o % (b^log b o) < o :=
  by
  rcases eq_or_ne b 0 with (rfl | hb)
  · simpa using Ordinal.pos_iff_ne_zero.2 ho
  · exact (mod_lt _ <| opow_ne_zero _ hb).trans_le (opow_log_le_self _ ho)
#align ordinal.mod_opow_log_lt_self Ordinal.mod_opow_log_lt_self

/- warning: ordinal.log_mod_opow_log_lt_log_self -> Ordinal.log_mod_opow_log_lt_log_self is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) b) -> (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) b o) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (Ordinal.log.{u1} b (HMod.hMod.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMod.{succ u1} Ordinal.{u1} Ordinal.hasMod.{u1}) o (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b (Ordinal.log.{u1} b o)))) (Ordinal.log.{u1} b o))
but is expected to have type
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) b) -> (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) b o) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (Ordinal.log.{u1} b (HMod.hMod.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMod.{succ u1} Ordinal.{u1} Ordinal.instModOrdinal.{u1}) o (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b (Ordinal.log.{u1} b o)))) (Ordinal.log.{u1} b o))
Case conversion may be inaccurate. Consider using '#align ordinal.log_mod_opow_log_lt_log_self Ordinal.log_mod_opow_log_lt_log_selfₓ'. -/
theorem log_mod_opow_log_lt_log_self {b o : Ordinal} (hb : 1 < b) (ho : o ≠ 0) (hbo : b ≤ o) :
    log b (o % (b^log b o)) < log b o :=
  by
  cases eq_or_ne (o % (b^log b o)) 0
  · rw [h, log_zero_right]
    apply log_pos hb ho hbo
  · rw [← succ_le_iff, succ_log_def hb h]
    apply cinfₛ_le'
    apply mod_lt
    rw [← Ordinal.pos_iff_ne_zero]
    exact opow_pos _ (zero_lt_one.trans hb)
#align ordinal.log_mod_opow_log_lt_log_self Ordinal.log_mod_opow_log_lt_log_self

/- warning: ordinal.opow_mul_add_pos -> Ordinal.opow_mul_add_pos is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} {v : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} b (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (forall (u : Ordinal.{u1}), (Ne.{succ (succ u1)} Ordinal.{u1} v (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (forall (w : Ordinal.{u1}), LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b u) v) w)))
but is expected to have type
  forall {b : Ordinal.{u1}} {v : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} b (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) -> (forall (u : Ordinal.{u1}), (Ne.{succ (succ u1)} Ordinal.{u1} v (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) -> (forall (w : Ordinal.{u1}), LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1})) (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.instAddOrdinal.{u1}) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.instMonoidWithZeroOrdinal.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b u) v) w)))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_mul_add_pos Ordinal.opow_mul_add_posₓ'. -/
theorem opow_mul_add_pos {b v : Ordinal} (hb : b ≠ 0) (u) (hv : v ≠ 0) (w) : 0 < (b^u) * v + w :=
  (opow_pos u <| Ordinal.pos_iff_ne_zero.2 hb).trans_le <|
    (le_mul_left _ <| Ordinal.pos_iff_ne_zero.2 hv).trans <| le_add_right _ _
#align ordinal.opow_mul_add_pos Ordinal.opow_mul_add_pos

/- warning: ordinal.opow_mul_add_lt_opow_mul_succ -> Ordinal.opow_mul_add_lt_opow_mul_succ is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} {u : Ordinal.{u1}} {w : Ordinal.{u1}} (v : Ordinal.{u1}), (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) w (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b u)) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b u) v) w) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b u) (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} v)))
but is expected to have type
  forall {b : Ordinal.{u1}} {u : Ordinal.{u1}} {w : Ordinal.{u1}} (v : Ordinal.{u1}), (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) w (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b u)) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.instAddOrdinal.{u1}) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.instMonoidWithZeroOrdinal.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b u) v) w) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.instMonoidWithZeroOrdinal.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b u) (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1}) Ordinal.instSuccOrderOrdinalToPreorderInstPartialOrderOrdinal.{u1} v)))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_mul_add_lt_opow_mul_succ Ordinal.opow_mul_add_lt_opow_mul_succₓ'. -/
theorem opow_mul_add_lt_opow_mul_succ {b u w : Ordinal} (v : Ordinal) (hw : w < (b^u)) :
    (b^u) * v + w < (b^u) * succ v := by rwa [mul_succ, add_lt_add_iff_left]
#align ordinal.opow_mul_add_lt_opow_mul_succ Ordinal.opow_mul_add_lt_opow_mul_succ

/- warning: ordinal.opow_mul_add_lt_opow_succ -> Ordinal.opow_mul_add_lt_opow_succ is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} {u : Ordinal.{u1}} {v : Ordinal.{u1}} {w : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) v b) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) w (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b u)) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b u) v) w) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} u)))
but is expected to have type
  forall {b : Ordinal.{u1}} {u : Ordinal.{u1}} {v : Ordinal.{u1}} {w : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) v b) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) w (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b u)) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.instAddOrdinal.{u1}) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.instMonoidWithZeroOrdinal.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b u) v) w) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1}) Ordinal.instSuccOrderOrdinalToPreorderInstPartialOrderOrdinal.{u1} u)))
Case conversion may be inaccurate. Consider using '#align ordinal.opow_mul_add_lt_opow_succ Ordinal.opow_mul_add_lt_opow_succₓ'. -/
theorem opow_mul_add_lt_opow_succ {b u v w : Ordinal} (hvb : v < b) (hw : w < (b^u)) :
    (b^u) * v + w < (b^succ u) :=
  by
  convert (opow_mul_add_lt_opow_mul_succ v hw).trans_le (mul_le_mul_left' (succ_le_of_lt hvb) _)
  exact opow_succ b u
#align ordinal.opow_mul_add_lt_opow_succ Ordinal.opow_mul_add_lt_opow_succ

/- warning: ordinal.log_opow_mul_add -> Ordinal.log_opow_mul_add is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} {u : Ordinal.{u1}} {v : Ordinal.{u1}} {w : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) b) -> (Ne.{succ (succ u1)} Ordinal.{u1} v (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) v b) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) w (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b u)) -> (Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.log.{u1} b (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b u) v) w)) u)
but is expected to have type
  forall {b : Ordinal.{u1}} {u : Ordinal.{u1}} {v : Ordinal.{u1}} {w : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) b) -> (Ne.{succ (succ u1)} Ordinal.{u1} v (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) v b) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) w (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b u)) -> (Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.log.{u1} b (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.instAddOrdinal.{u1}) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.instMonoidWithZeroOrdinal.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b u) v) w)) u)
Case conversion may be inaccurate. Consider using '#align ordinal.log_opow_mul_add Ordinal.log_opow_mul_addₓ'. -/
theorem log_opow_mul_add {b u v w : Ordinal} (hb : 1 < b) (hv : v ≠ 0) (hvb : v < b)
    (hw : w < (b^u)) : log b ((b^u) * v + w) = u :=
  by
  have hne' := (opow_mul_add_pos (zero_lt_one.trans hb).ne' u hv w).ne'
  by_contra' hne
  cases' lt_or_gt_of_ne hne with h h
  · rw [← lt_opow_iff_log_lt hb hne'] at h
    exact h.not_le ((le_mul_left _ (Ordinal.pos_iff_ne_zero.2 hv)).trans (le_add_right _ _))
  · change _ < _ at h
    rw [← succ_le_iff, ← opow_le_iff_le_log hb hne'] at h
    exact (not_lt_of_le h) (opow_mul_add_lt_opow_succ hvb hw)
#align ordinal.log_opow_mul_add Ordinal.log_opow_mul_add

/- warning: ordinal.log_opow -> Ordinal.log_opow is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) b) -> (forall (x : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.log.{u1} b (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b x)) x)
but is expected to have type
  forall {b : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) b) -> (forall (x : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.log.{u1} b (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b x)) x)
Case conversion may be inaccurate. Consider using '#align ordinal.log_opow Ordinal.log_opowₓ'. -/
theorem log_opow {b : Ordinal} (hb : 1 < b) (x : Ordinal) : log b (b^x) = x :=
  by
  convert log_opow_mul_add hb zero_ne_one.symm hb (opow_pos x (zero_lt_one.trans hb))
  rw [add_zero, mul_one]
#align ordinal.log_opow Ordinal.log_opow

/- warning: ordinal.div_opow_log_lt -> Ordinal.div_opow_log_lt is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} (o : Ordinal.{u1}), (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) b) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HDiv.hDiv.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHDiv.{succ u1} Ordinal.{u1} Ordinal.hasDiv.{u1}) o (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b (Ordinal.log.{u1} b o))) b)
but is expected to have type
  forall {b : Ordinal.{u1}} (o : Ordinal.{u1}), (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.instOneOrdinal.{u1})) b) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (HDiv.hDiv.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHDiv.{succ u1} Ordinal.{u1} Ordinal.instDivOrdinal.{u1}) o (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) b (Ordinal.log.{u1} b o))) b)
Case conversion may be inaccurate. Consider using '#align ordinal.div_opow_log_lt Ordinal.div_opow_log_ltₓ'. -/
theorem div_opow_log_lt {b : Ordinal} (o : Ordinal) (hb : 1 < b) : o / (b^log b o) < b :=
  by
  rw [div_lt (opow_pos _ (zero_lt_one.trans hb)).ne', ← opow_succ]
  exact lt_opow_succ_log_self hb o
#align ordinal.div_opow_log_lt Ordinal.div_opow_log_lt

/- warning: ordinal.add_log_le_log_mul -> Ordinal.add_log_le_log_mul is a dubious translation:
lean 3 declaration is
  forall {x : Ordinal.{u1}} {y : Ordinal.{u1}} (b : Ordinal.{u1}), (Ne.{succ (succ u1)} Ordinal.{u1} x (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (Ne.{succ (succ u1)} Ordinal.{u1} y (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) (Ordinal.log.{u1} b x) (Ordinal.log.{u1} b y)) (Ordinal.log.{u1} b (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) x y)))
but is expected to have type
  forall {x : Ordinal.{u1}} {y : Ordinal.{u1}} (b : Ordinal.{u1}), (Ne.{succ (succ u1)} Ordinal.{u1} x (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) -> (Ne.{succ (succ u1)} Ordinal.{u1} y (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1}))) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.instAddOrdinal.{u1}) (Ordinal.log.{u1} b x) (Ordinal.log.{u1} b y)) (Ordinal.log.{u1} b (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.instMonoidWithZeroOrdinal.{u1})))) x y)))
Case conversion may be inaccurate. Consider using '#align ordinal.add_log_le_log_mul Ordinal.add_log_le_log_mulₓ'. -/
theorem add_log_le_log_mul {x y : Ordinal} (b : Ordinal) (hx : x ≠ 0) (hy : y ≠ 0) :
    log b x + log b y ≤ log b (x * y) :=
  by
  by_cases hb : 1 < b
  · rw [← opow_le_iff_le_log hb (mul_ne_zero hx hy), opow_add]
    exact mul_le_mul' (opow_log_le_self b hx) (opow_log_le_self b hy)
  simp only [log_of_not_one_lt_left hb, zero_add]
#align ordinal.add_log_le_log_mul Ordinal.add_log_le_log_mul

/-! ### Interaction with `nat.cast` -/


/- warning: ordinal.nat_cast_opow -> Ordinal.nat_cast_opow is a dubious translation:
lean 3 declaration is
  forall (m : Nat) (n : Nat), Eq.{succ (succ u1)} Ordinal.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Ordinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Ordinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Ordinal.{u1} (Nat.castCoe.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1})))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) m n)) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Ordinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Ordinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Ordinal.{u1} (Nat.castCoe.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1})))) m) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Ordinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Ordinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Ordinal.{u1} (Nat.castCoe.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1})))) n))
but is expected to have type
  forall (m : Nat) (n : Nat), Eq.{succ (succ u1)} Ordinal.{u1} (Nat.cast.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.instAddMonoidWithOneOrdinal.{u1}) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) m n)) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) (Nat.cast.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.instAddMonoidWithOneOrdinal.{u1}) m) (Nat.cast.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.instAddMonoidWithOneOrdinal.{u1}) n))
Case conversion may be inaccurate. Consider using '#align ordinal.nat_cast_opow Ordinal.nat_cast_opowₓ'. -/
@[simp, norm_cast]
theorem nat_cast_opow (m : ℕ) : ∀ n : ℕ, ((pow m n : ℕ) : Ordinal) = (m^n)
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ', nat_cast_mul, nat_cast_opow, Nat.cast_succ, add_one_eq_succ, opow_succ]
#align ordinal.nat_cast_opow Ordinal.nat_cast_opow

-- mathport name: ordinal.pow
local infixr:0 "^" => @pow Ordinal Ordinal Ordinal.hasPow

/- warning: ordinal.sup_opow_nat -> Ordinal.sup_opow_nat is a dubious translation:
lean 3 declaration is
  forall {o : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) o) -> (Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.sup.{0, u1} Nat (fun (n : Nat) => HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) o ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Ordinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Ordinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Ordinal.{u1} (Nat.castCoe.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1})))) n))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) o Ordinal.omega.{u1}))
but is expected to have type
  forall {o : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.instPartialOrderOrdinal.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.instZeroOrdinal.{u1})) o) -> (Eq.{succ (succ u1)} Ordinal.{u1} (Ordinal.sup.{0, u1} Nat (fun (n : Nat) => HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) o (Nat.cast.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.instAddMonoidWithOneOrdinal.{u1}) n))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.instPowOrdinalOrdinal.{u1}) o Ordinal.omega.{u1}))
Case conversion may be inaccurate. Consider using '#align ordinal.sup_opow_nat Ordinal.sup_opow_natₓ'. -/
theorem sup_opow_nat {o : Ordinal} (ho : 0 < o) : (sup fun n : ℕ => o^n) = (o^ω) :=
  by
  rcases lt_or_eq_of_le (one_le_iff_pos.2 ho) with (ho₁ | rfl)
  · exact (opow_is_normal ho₁).apply_omega
  · rw [one_opow]
    refine' le_antisymm (sup_le fun n => by rw [one_opow]) _
    convert le_sup _ 0
    rw [Nat.cast_zero, opow_zero]
#align ordinal.sup_opow_nat Ordinal.sup_opow_nat

end Ordinal

namespace Tactic

open Ordinal Positivity

/-- Extension for the `positivity` tactic: `ordinal.opow` takes positive values on positive inputs.
-/
@[positivity]
unsafe def positivity_opow : expr → tactic strictness
  | q(@Pow.pow _ _ $(inst) $(a) $(b)) => do
    let strictness_a ← core a
    match strictness_a with
      | positive p => positive <$> mk_app `` opow_pos [b, p]
      | _ => failed
  |-- We already know that `0 ≤ x` for all `x : ordinal`
    _ =>
    failed
#align tactic.positivity_opow tactic.positivity_opow

end Tactic

