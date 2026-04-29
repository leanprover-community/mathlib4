/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Data.FunLike.IsApply
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic

/-! # Group instances for `FunLike` types
In this file we define various instances related to groups for `FunLike` types.

For example given a `FunLike F α β` with `IsMulApply F α β` and `Semigroup β`, then `F` is naturally
a semigroup.

Moreover, we define the homomorphism `FunLike.coeMulHom : F →* α → β` that acts by coercion. This
definition is mainly needed to define a module instance on `F`.

-/

@[expose] public section

namespace FunLike

variable {F α β : Type*} [FunLike F α β]

section CoercionHom

variable [MulOne F] [MulOneClass β] [IsOneApply F α β] [IsMulApply F α β]

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

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` is a semigroup if `β` is a semigroup. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` is an additive semigroup
if `β` is an additive semigroup. -/]
protected abbrev semigroup [Semigroup β] [IsMulApply F α β] : Semigroup F :=
  DFunLike.coe_injective.semigroup (fun (f : F) ↦ (f : α → β)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` is a commutative semigroup if `β` is a
commutative semigroup. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` is a commatative additive
semigroup if `β` is a commatative additive semigroup. -/]
protected abbrev commSemigroup [CommSemigroup β] [IsMulApply F α β] :
    CommSemigroup F :=
  DFunLike.coe_injective.commSemigroup (fun (f : F) ↦ (f : α → β)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` has left cancellative multiplication if
`β` has left cancellative multiplication. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` has left cancellative
addition if `β` has left cancellative addition. -/]
protected theorem isLeftCancelMul [Mul β] [IsLeftCancelMul β] [IsMulApply F α β] :
    IsLeftCancelMul F :=
  DFunLike.coe_injective.isLeftCancelMul (fun (f : F) ↦ (f : α → β)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` has right cancellative multiplication if
`β` has right cancellative multiplication. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` has right cancellative
addition if `β` has right cancellative addition. -/]
protected theorem isRightCancelMul [Mul β] [IsRightCancelMul β] [IsMulApply F α β] :
    IsRightCancelMul F :=
  DFunLike.coe_injective.isRightCancelMul (fun (f : F) ↦ (f : α → β)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` has right multiplication if
`β` has right multiplication. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` has right
addition if `β` has cancellative addition. -/]
protected theorem isCancelMul [Mul β] [IsCancelMul β] [IsMulApply F α β] :
    IsCancelMul F :=
  DFunLike.coe_injective.isCancelMul (fun (f : F) ↦ (f : α → β)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` is a left cancel semigroup if `β` is a
left cancel semigroup. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` is a left cancel additive
semigroup if `β` is a left cancel additive semigroup. -/]
protected abbrev leftCancelSemigroup [LeftCancelSemigroup β] [IsMulApply F α β] :
    LeftCancelSemigroup F :=
  DFunLike.coe_injective.leftCancelSemigroup (fun (f : F) ↦ (f : α → β)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` is a right cancel semigroup if `β` is a
right cancel semigroup. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` is a right cancel additive
semigroup if `β` is a right cancel additive semigroup. -/]
protected abbrev rightCancelSemigroup [RightCancelSemigroup β] [IsMulApply F α β] :
    RightCancelSemigroup F :=
  DFunLike.coe_injective.rightCancelSemigroup (fun (f : F) ↦ (f : α → β)) coe_mul

variable [One F]

/-- A `FunLike` type with `1` and `*` is `MulOneClass` if `β` is a `MulOneClass`. -/
@[to_additive /-- A `FunLike` type with `0` and `+` is `AddZeroClass` if `β` is a
`AddZeroClass`. -/]
protected abbrev mulOneClass [MulOneClass β] [IsOneApply F α β] [IsMulApply F α β] :
    MulOneClass F :=
  DFunLike.coe_injective.mulOneClass (fun (f : F) ↦ (f : α → β)) coe_one coe_mul

variable [Pow F ℕ]

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a monoid if `β` is a monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is an additive monoid if `β` is an additive monoid. -/]
protected abbrev monoid [Monoid β] [IsOneApply F α β] [IsMulApply F α β] [IsPowApply ℕ F α β] :
    Monoid F :=
  DFunLike.coe_injective.monoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a left cancel monoid if `β` is a left cancel monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a left cancel additive monoid if `β` is a left cancel additive monoid. -/]
protected abbrev leftCancelMonoid [LeftCancelMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsPowApply ℕ F α β] : LeftCancelMonoid F :=
  DFunLike.coe_injective.leftCancelMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a right cancel monoid if `β` is a right cancel monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a right cancel additive monoid if `β` is a right cancel
additive monoid. -/]
protected abbrev rightCancelMonoid [RightCancelMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsPowApply ℕ F α β] : RightCancelMonoid F :=
  DFunLike.coe_injective.rightCancelMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a cancel monoid if `β` is a cancel monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a cancel additive monoid if `β` is a cancel additive monoid. -/]
protected abbrev cancelMonoid [CancelMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsPowApply ℕ F α β] : CancelMonoid F :=
  DFunLike.coe_injective.cancelMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a commutative monoid if `β` is a commutative monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a commutative additive monoid if `β` is a commutative additive monoid. -/]
protected abbrev commMonoid [CommMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsPowApply ℕ F α β] : CommMonoid F :=
  DFunLike.coe_injective.commMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a cancel commutative monoid if `β` is a cancel commutative monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a cancel commutative additive monoid if `β` is a cancel commutative
additive monoid. -/]
protected abbrev cancelCommMonoid [CancelCommMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsPowApply ℕ F α β] : CancelCommMonoid F :=
  DFunLike.coe_injective.cancelCommMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_pow

variable [Inv F]

/-- A `FunLike` type with inverse that satisfies `(f⁻¹) x = (f x)⁻¹` is an involutive inversion
if `β` is an involutive inversion. -/
@[to_additive /-- A `FunLike` type with negation that satisfies `(- f) x = - (f x)` is an involutive
negation if `β` is an involutive negation. -/]
protected abbrev involutiveInv [InvolutiveInv β] [IsInvApply F α β] : InvolutiveInv F :=
  DFunLike.coe_injective.involutiveInv (fun (f : F) ↦ (f : α → β)) coe_inv

/-- A `FunLike` type with `1` and inverse is an `InvOneClass` if `β` is an `InvOneClass`. -/
@[to_additive /-- A `FunLike` type with `0` and negation is a `NegZeroClass` if `β` is a
`NegZeroClass`. -/]
protected abbrev invOneClass [InvOneClass β] [IsOneApply F α β] [IsInvApply F α β] :
    InvOneClass F :=
  DFunLike.coe_injective.invOneClass (fun (f : F) ↦ (f : α → β)) coe_one coe_inv

variable [Div F] [Pow F ℤ]

/-- A `FunLike` type is a `DivInvMonoid` if `β` is a `DivInvMonoid`. -/
@[to_additive subNegMonoid /-- A `FunLike` type is a `SubNegMonoid` if `β` is a `SubNegMonoid`. -/]
protected abbrev divInvMonoid [DivInvMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsInvApply F α β] [IsDivApply F α β] [IsPowApply ℕ F α β] [IsPowApply ℤ F α β] :
    DivInvMonoid F :=
  DFunLike.coe_injective.divInvMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_inv coe_div
    coe_pow coe_pow

/-- A `FunLike` type is a `DivInvOneMonoid` if `β` is a `DivInvOneMonoid`. -/
@[to_additive
/-- A `FunLike` type is a `SubNegOneMonoid` if `β` is a `SubNegOneMonoid`. -/]
protected abbrev divInvOneMonoid [DivInvOneMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsInvApply F α β] [IsDivApply F α β] [IsPowApply ℕ F α β] [IsPowApply ℤ F α β] :
    DivInvOneMonoid F :=
  DFunLike.coe_injective.divInvOneMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul
    coe_inv coe_div coe_pow coe_pow

/-- A `FunLike` type is a division monoid if `β` is a division monoid. -/
@[to_additive /-- A `FunLike` type is a subtraction monoid if `β` is a subtraction monoid. -/]
protected abbrev divisionMonoid [DivisionMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsInvApply F α β] [IsDivApply F α β] [IsPowApply ℕ F α β] [IsPowApply ℤ F α β] :
    DivisionMonoid F :=
  DFunLike.coe_injective.divisionMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul
    coe_inv coe_div coe_pow coe_pow

/-- A `FunLike` type is a division commutative monoid if `β` is a division commutative monoid. -/
@[to_additive subtractionCommMonoid /-- A `FunLike` type is a subtraction commutative monoid if `β`
is a subtraction commutative monoid. -/]
protected abbrev divisionCommMonoid [DivisionCommMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsInvApply F α β] [IsDivApply F α β] [IsPowApply ℕ F α β] [IsPowApply ℤ F α β] :
    DivisionCommMonoid F :=
  DFunLike.coe_injective.divisionCommMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_inv
    coe_div coe_pow coe_pow

/-- A `FunLike` type is a group if `β` is a group. -/
@[to_additive /-- A `FunLike` type is an additive group if `β` is an additive group. -/]
protected abbrev group [Group β] [IsOneApply F α β] [IsMulApply F α β] [IsInvApply F α β]
    [IsDivApply F α β] [IsPowApply ℕ F α β] [IsPowApply ℤ F α β] :
    Group F :=
  DFunLike.coe_injective.group (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_inv coe_div coe_pow
    coe_pow

/-- A `FunLike` type is a commutative group if `β` is a commutative group. -/
@[to_additive /-- A `FunLike` type is an additive commutative group if `β` is an additive
commutative group. -/]
protected abbrev commGroup [CommGroup β] [IsOneApply F α β] [IsMulApply F α β] [IsInvApply F α β]
    [IsDivApply F α β] [IsPowApply ℕ F α β] [IsPowApply ℤ F α β] :
    CommGroup F :=
  DFunLike.coe_injective.commGroup (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_inv coe_div
    coe_pow coe_pow

end GroupInstances

end FunLike
