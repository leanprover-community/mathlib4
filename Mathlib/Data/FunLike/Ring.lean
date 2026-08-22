/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Data.FunLike.GroupWithZero
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Tactic.Finiteness.Attr

/-! # Ring instances for `FunLike` types
In this file we define various instances related to ring for `FunLike` types.
There are two different variants: either the multiplication is given by composition or it is
pointwise multiplication.

Note that currently, these are not registered as instances, but only `abbrev`s to avoid long
typeclass searches.
-/

public section

variable {F α β : Type*}

namespace FunLike

section Comp

section Semiring

variable [FunLike F α α] [Zero F] [One F] [Mul F] [Add F] [AddCommMonoid α]
  [IsZeroApply F α α] [IsAddApply F α α] [IsOneApplyEqSelf F α] [IsMulApplyEqComp F α]
  [SMul ℕ F] [IsSMulApply ℕ F α α] [AddMonoidHomClass F α α] [NatCast F] [IsNatCastApplyEqSMul F α]

/-- A `FunLike` type with `(f * g) x = f (g x)` is a `Semiring`. -/
protected abbrev compSemiring : Semiring F where
  __ := FunLike.compMonoidWithZero
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
  [NatCast F] [IsNatCastApplyEqSMul F α] [IntCast F] [IsIntCastApplyEqSMul F α]

/-- A `FunLike` type with `(f * g) x = f (g x)` is a `Ring`. -/
protected abbrev compRing : Ring F where
  __ := FunLike.compSemiring
  __ := FunLike.addCommGroup
  intCast_ofNat _ := by apply DFunLike.ext; simp
  intCast_negSucc n := by apply DFunLike.ext; simp [succ_nsmul]

end Ring

end Comp

section PointwiseMul

variable [FunLike F α β] [Zero F] [One F] [Add F] [Neg F] [Sub F] [Mul F] [SMul ℕ F] [SMul ℤ F]
  [Pow F ℕ] [NatCast F] [IntCast F]

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `Distrib` if `β` is a `Distrib`. -/
protected abbrev distrib [Distrib β] [IsAddApply F α β] [IsMulApply F α β] :
    Distrib F :=
  DFunLike.coe_injective.distrib (fun (f : F) ↦ (f : α → β)) coe_add coe_mul

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `HasDistribNeg` if `β` is a
`HasDistribNeg`. -/
protected abbrev hasDistribNeg [Mul β] [HasDistribNeg β] [IsNegApply F α β] [IsMulApply F α β] :
    HasDistribNeg F :=
  DFunLike.coe_injective.hasDistribNeg (fun (f : F) ↦ (f : α → β)) coe_neg coe_mul

/-- A `FunLike` type with `(f * g) x = f x * g x` is an `AddMonoidWithOne` if `β` is an
`AddMonoidWithOne`. -/
protected abbrev addMonoidWithOne [AddMonoidWithOne β] [IsZeroApply F α β] [IsOneApply F α β]
    [IsAddApply F α β] [IsSMulApply ℕ F α β] [IsNatCastApply F α β] :
    AddMonoidWithOne F :=
  DFunLike.coe_injective.addMonoidWithOne (fun (f : F) ↦ (f : α → β)) coe_zero coe_one coe_add
    coe_smul coe_natCast

/-- A `FunLike` type with `(f * g) x = f x * g x` is an `AddGroupWithOne` if `β` is an
`AddGroupWithOne`. -/
protected abbrev addGroupWithOne [AddGroupWithOne β] [IsZeroApply F α β] [IsOneApply F α β]
    [IsAddApply F α β] [IsNegApply F α β] [IsSubApply F α β] [IsSMulApply ℕ F α β]
    [IsSMulApply ℤ F α β] [IsNatCastApply F α β] [IsIntCastApply F α β] :
    AddGroupWithOne F :=
  DFunLike.coe_injective.addGroupWithOne (fun (f : F) ↦ (f : α → β)) coe_zero coe_one coe_add
    coe_neg coe_sub coe_smul coe_smul coe_natCast coe_intCast

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `NonUnitalNonAssocSemiring` if `β` is a
`NonUnitalNonAssocSemiring`. -/
protected abbrev nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring β] [IsZeroApply F α β]
    [IsAddApply F α β] [IsMulApply F α β] [IsSMulApply ℕ F α β] :
    NonUnitalNonAssocSemiring F :=
  DFunLike.coe_injective.nonUnitalNonAssocSemiring (fun (f : F) ↦ (f : α → β)) coe_zero coe_add
    coe_mul coe_smul

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `NonUnitalSemiring` if `β` is a
`NonUnitalSemiring`. -/
protected abbrev nonUnitalSemiring [NonUnitalSemiring β] [IsZeroApply F α β]
    [IsAddApply F α β] [IsMulApply F α β] [IsSMulApply ℕ F α β] :
    NonUnitalSemiring F :=
  DFunLike.coe_injective.nonUnitalSemiring (fun (f : F) ↦ (f : α → β)) coe_zero coe_add coe_mul
    coe_smul

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `NonAssocSemiring` if `β` is a
`NonAssocSemiring`. -/
protected abbrev nonAssocSemiring [NonAssocSemiring β] [IsZeroApply F α β] [IsOneApply F α β]
    [IsAddApply F α β] [IsMulApply F α β] [IsSMulApply ℕ F α β] [IsNatCastApply F α β] :
    NonAssocSemiring F :=
  DFunLike.coe_injective.nonAssocSemiring (fun (f : F) ↦ (f : α → β)) coe_zero coe_one coe_add
    coe_mul coe_smul coe_natCast

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `Semiring` if `β` is a `Semiring`. -/
protected abbrev semiring [Semiring β] [IsZeroApply F α β] [IsOneApply F α β] [IsAddApply F α β]
    [IsMulApply F α β] [IsSMulApply ℕ F α β] [IsPowApply ℕ F α β] [IsNatCastApply F α β] :
    Semiring F :=
  DFunLike.coe_injective.semiring (fun (f : F) ↦ (f : α → β)) coe_zero coe_one coe_add
    coe_mul coe_smul coe_pow coe_natCast

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `NonUnitalCommSemiring` if `β` is a
`NonUnitalCommSemiring`. -/
protected abbrev nonUnitalCommSemiring [NonUnitalCommSemiring β] [IsZeroApply F α β]
    [IsAddApply F α β] [IsMulApply F α β] [IsSMulApply ℕ F α β] :
    NonUnitalCommSemiring F :=
  DFunLike.coe_injective.nonUnitalCommSemiring (fun (f : F) ↦ (f : α → β)) coe_zero coe_add coe_mul
    coe_smul

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `CommSemiring` if `β` is a `CommSemiring`. -/
protected abbrev commSemiring [CommSemiring β] [IsZeroApply F α β] [IsOneApply F α β]
    [IsAddApply F α β] [IsMulApply F α β] [IsSMulApply ℕ F α β] [IsPowApply ℕ F α β]
    [IsNatCastApply F α β] :
    CommSemiring F :=
  DFunLike.coe_injective.commSemiring (fun (f : F) ↦ (f : α → β)) coe_zero coe_one coe_add
    coe_mul coe_smul coe_pow coe_natCast

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `NonUnitalNonAssocRing` if `β` is a
`NonUnitalNonAssocRing`. -/
protected abbrev nonUnitalNonAssocRing [NonUnitalNonAssocRing β] [IsZeroApply F α β]
    [IsAddApply F α β] [IsMulApply F α β] [IsNegApply F α β] [IsSubApply F α β]
    [IsSMulApply ℕ F α β] [IsSMulApply ℤ F α β] :
    NonUnitalNonAssocRing F :=
  DFunLike.coe_injective.nonUnitalNonAssocRing (fun (f : F) ↦ (f : α → β)) coe_zero coe_add
    coe_mul coe_neg coe_sub coe_smul coe_smul

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `NonUnitalRing` if `β` is a
`NonUnitalRing`. -/
protected abbrev nonUnitalRing [NonUnitalRing β] [IsZeroApply F α β]
    [IsAddApply F α β] [IsMulApply F α β] [IsNegApply F α β] [IsSubApply F α β]
    [IsSMulApply ℕ F α β] [IsSMulApply ℤ F α β] :
    NonUnitalRing F :=
  DFunLike.coe_injective.nonUnitalRing (fun (f : F) ↦ (f : α → β)) coe_zero coe_add
    coe_mul coe_neg coe_sub coe_smul coe_smul

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `NonAssocRing` if `β` is a `NonAssocRing`. -/
protected abbrev nonAssocRing [NonAssocRing β] [IsZeroApply F α β] [IsOneApply F α β]
    [IsAddApply F α β] [IsMulApply F α β] [IsNegApply F α β] [IsSubApply F α β]
    [IsSMulApply ℕ F α β] [IsSMulApply ℤ F α β] [IsNatCastApply F α β]
    [IsIntCastApply F α β] :
    NonAssocRing F :=
  DFunLike.coe_injective.nonAssocRing (fun (f : F) ↦ (f : α → β)) coe_zero coe_one coe_add
    coe_mul coe_neg coe_sub coe_smul coe_smul coe_natCast coe_intCast

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `Ring` if `β` is a `Ring`. -/
protected abbrev ring [Ring β] [IsZeroApply F α β] [IsOneApply F α β]
    [IsAddApply F α β] [IsMulApply F α β] [IsNegApply F α β] [IsSubApply F α β]
    [IsSMulApply ℕ F α β] [IsSMulApply ℤ F α β] [IsPowApply ℕ F α β] [IsNatCastApply F α β]
    [IsIntCastApply F α β] :
    Ring F :=
  DFunLike.coe_injective.ring (fun (f : F) ↦ (f : α → β)) coe_zero coe_one coe_add
    coe_mul coe_neg coe_sub coe_smul coe_smul coe_pow coe_natCast coe_intCast

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `NonUnitalCommRing` if `β` is a
`NonUnitalCommRing`. -/
protected abbrev nonUnitalCommRing [NonUnitalCommRing β] [IsZeroApply F α β]
    [IsAddApply F α β] [IsMulApply F α β] [IsNegApply F α β] [IsSubApply F α β]
    [IsSMulApply ℕ F α β] [IsSMulApply ℤ F α β] :
    NonUnitalCommRing F :=
  DFunLike.coe_injective.nonUnitalCommRing (fun (f : F) ↦ (f : α → β)) coe_zero coe_add
    coe_mul coe_neg coe_sub coe_smul coe_smul

/-- A `FunLike` type with `(f * g) x = f x * g x` is a `CommRing` if `β` is a `CommRing`. -/
protected abbrev commRing [CommRing β] [IsZeroApply F α β] [IsOneApply F α β]
    [IsAddApply F α β] [IsMulApply F α β] [IsNegApply F α β] [IsSubApply F α β]
    [IsSMulApply ℕ F α β] [IsSMulApply ℤ F α β] [IsPowApply ℕ F α β] [IsNatCastApply F α β]
    [IsIntCastApply F α β] :
    CommRing F :=
  DFunLike.coe_injective.commRing (fun (f : F) ↦ (f : α → β)) coe_zero coe_one coe_add
    coe_mul coe_neg coe_sub coe_smul coe_smul coe_pow coe_natCast coe_intCast

end PointwiseMul

end FunLike
