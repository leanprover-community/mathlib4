/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Algebra.Group.Pi.Torsion
public import Mathlib.Algebra.Group.PowIterate

/-! # Group instances for `FunLike` types
In this file we define various instances related to groups for `FunLike` types.

For example given a `FunLike F α β` with `IsMulApply F` and `Semigroup β`, then `F` is naturally
a semigroup. Note that currently, these are not registered as instances, but only `abbrev`s to
avoid long typeclass searches.

Moreover, we define the homomorphism `FunLike.coeMulHom : F →* (a : α) → β a` that acts by coercion.
This definition is mainly needed to define a module instance on `F`.
-/

@[expose] public section

namespace FunLike

variable {F α : Type*} {β : α → Type*} [DFunLike F α β]

section CoercionHom

section MulHom

variable [Mul F] [∀ a, Mul (β a)] [IsMulApply F]

variable (F α β) in
/-- Coercion as a multiplicative homomorphism. -/
@[to_additive
/-- Coercion as an additive homomorphism. -/]
def coeMulHom : F →ₙ* (a : α) → β a where
  toFun f := f
  map_mul' := coe_mul

@[to_additive (attr := simp)]
theorem coeMulHom_apply (f : F) : coeMulHom F α β f = f := rfl

@[to_additive (attr := norm_cast)]
theorem coe_coeMulHom : (coeMulHom F α β : F → (a : α) → β a) = DFunLike.coe := rfl

@[to_additive]
theorem coeMulHom_injective : Function.Injective (coeMulHom F α β) := by
  rw [coe_coeMulHom]
  exact DFunLike.coe_injective

end MulHom

section MonoidHom

variable [MulOne F] [∀ a, MulOneClass (β a)] [IsOneApply F] [IsMulApply F]

variable (F α β) in
/-- Coercion as a monoid homomorphism. -/
@[to_additive
/-- Coercion as an additive monoid homomorphism. -/]
def coeMonoidHom : F →* (a : α) → β a where
  toFun f := f
  map_one' := coe_one
  map_mul' := coe_mul

@[to_additive (attr := simp)]
theorem coeMonoidHom_apply (f : F) : coeMonoidHom F α β f = f := rfl

@[to_additive (attr := norm_cast)]
theorem coe_coeMonoidHom : (coeMonoidHom F α β : F → (a : α) → β a) = DFunLike.coe := rfl

@[to_additive (attr := norm_cast)]
theorem coe_coeMonoidHom' : (coeMonoidHom F α β : F →ₙ* (a : α) → β a) = coeMulHom F α β := rfl

@[to_additive]
theorem coeMonoidHom_injective : Function.Injective (coeMonoidHom F α β) := by
  rw [coe_coeMonoidHom]
  exact DFunLike.coe_injective

end MonoidHom

end CoercionHom

section GroupInstances

variable [Mul F]

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` is a semigroup if `β` is a semigroup. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` is an additive semigroup
if `β` is an additive semigroup. -/]
protected abbrev semigroup [∀ a, Semigroup (β a)] [IsMulApply F] : Semigroup F :=
  DFunLike.coe_injective.semigroup (fun (f : F) ↦ (f : (a : α) → β a)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` is a commutative semigroup if `β` is a
commutative semigroup. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` is a commutative additive
semigroup if `β` is a commutative additive semigroup. -/]
protected abbrev commSemigroup [∀ a, CommSemigroup (β a)] [IsMulApply F] :
    CommSemigroup F :=
  DFunLike.coe_injective.commSemigroup (fun (f : F) ↦ (f : (a : α) → β a)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` has left cancellative multiplication if
`β` has left cancellative multiplication. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` has left cancellative
addition if `β` has left cancellative addition. -/]
protected theorem isLeftCancelMul [∀ a, Mul (β a)] [∀ a, IsLeftCancelMul (β a)] [IsMulApply F] :
    IsLeftCancelMul F :=
  DFunLike.coe_injective.isLeftCancelMul (fun (f : F) ↦ (f : (a : α) → β a)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` has right cancellative multiplication if
`β` has right cancellative multiplication. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` has right cancellative
addition if `β` has right cancellative addition. -/]
protected theorem isRightCancelMul [∀ a, Mul (β a)] [∀ a, IsRightCancelMul (β a)] [IsMulApply F] :
    IsRightCancelMul F :=
  DFunLike.coe_injective.isRightCancelMul (fun (f : F) ↦ (f : (a : α) → β a)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` has right multiplication if
`β` has right multiplication. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` has right
addition if `β` has cancellative addition. -/]
protected theorem isCancelMul [∀ a, Mul (β a)] [∀ a, IsCancelMul (β a)] [IsMulApply F] :
    IsCancelMul F :=
  DFunLike.coe_injective.isCancelMul (fun (f : F) ↦ (f : (a : α) → β a)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` is a left cancel semigroup if `β` is a
left cancel semigroup. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` is a left cancel additive
semigroup if `β` is a left cancel additive semigroup. -/]
protected abbrev leftCancelSemigroup [∀ a, LeftCancelSemigroup (β a)] [IsMulApply F] :
    LeftCancelSemigroup F :=
  DFunLike.coe_injective.leftCancelSemigroup (fun (f : F) ↦ (f : (a : α) → β a)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` is a right cancel semigroup if `β` is a
right cancel semigroup. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` is a right cancel additive
semigroup if `β` is a right cancel additive semigroup. -/]
protected abbrev rightCancelSemigroup [∀ a, RightCancelSemigroup (β a)] [IsMulApply F] :
    RightCancelSemigroup F :=
  DFunLike.coe_injective.rightCancelSemigroup (fun (f : F) ↦ (f : (a : α) → β a)) coe_mul

variable [One F]

/-- A `FunLike` type with `1` and `*` is `MulOneClass` if `β` is a `MulOneClass`. -/
@[to_additive /-- A `FunLike` type with `0` and `+` is `AddZeroClass` if `β` is a
`AddZeroClass`. -/]
protected abbrev mulOneClass [∀ a, MulOneClass (β a)] [IsOneApply F] [IsMulApply F] :
    MulOneClass F :=
  DFunLike.coe_injective.mulOneClass (fun (f : F) ↦ (f : (a : α) → β a)) coe_one coe_mul

variable [Pow F ℕ]

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a monoid if `β` is a monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is an additive monoid if `β` is an additive monoid. -/]
protected abbrev monoid [∀ a, Monoid (β a)] [IsOneApply F] [IsMulApply F] [IsPowApply ℕ F] :
    Monoid F :=
  DFunLike.coe_injective.monoid (fun (f : F) ↦ (f : (a : α) → β a)) coe_one coe_mul coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a left cancel monoid if `β` is a left cancel monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a left cancel additive monoid if `β` is a left cancel additive monoid. -/]
protected abbrev leftCancelMonoid [∀ a, LeftCancelMonoid (β a)] [IsOneApply F] [IsMulApply F]
    [IsPowApply ℕ F] : LeftCancelMonoid F :=
  DFunLike.coe_injective.leftCancelMonoid (fun (f : F) ↦ (f : (a : α) → β a)) coe_one coe_mul
    coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a right cancel monoid if `β` is a right cancel monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a right cancel additive monoid if `β` is a right cancel
additive monoid. -/]
protected abbrev rightCancelMonoid [∀ a, RightCancelMonoid (β a)] [IsOneApply F] [IsMulApply F]
    [IsPowApply ℕ F] : RightCancelMonoid F :=
  DFunLike.coe_injective.rightCancelMonoid (fun (f : F) ↦ (f : (a : α) → β a)) coe_one coe_mul
    coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a cancel monoid if `β` is a cancel monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a cancel additive monoid if `β` is a cancel additive monoid. -/]
protected abbrev cancelMonoid [∀ a, CancelMonoid (β a)] [IsOneApply F] [IsMulApply F]
    [IsPowApply ℕ F] : CancelMonoid F :=
  DFunLike.coe_injective.cancelMonoid (fun (f : F) ↦ (f : (a : α) → β a)) coe_one coe_mul coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a commutative monoid if `β` is a commutative monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a commutative additive monoid if `β` is a commutative additive monoid. -/]
protected abbrev commMonoid [∀ a, CommMonoid (β a)] [IsOneApply F] [IsMulApply F]
    [IsPowApply ℕ F] : CommMonoid F :=
  DFunLike.coe_injective.commMonoid (fun (f : F) ↦ (f : (a : α) → β a)) coe_one coe_mul coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a cancel commutative monoid if `β` is a cancel commutative monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a cancel commutative additive monoid if `β` is a cancel commutative
additive monoid. -/]
protected abbrev cancelCommMonoid [∀ a, CancelCommMonoid (β a)] [IsOneApply F] [IsMulApply F]
    [IsPowApply ℕ F] : CancelCommMonoid F :=
  DFunLike.coe_injective.cancelCommMonoid (fun (f : F) ↦ (f : (a : α) → β a)) coe_one coe_mul
    coe_pow

variable [Inv F]

/-- A `FunLike` type with inverse that satisfies `(f⁻¹) x = (f x)⁻¹` is an involutive inversion
if `β` is an involutive inversion. -/
@[to_additive /-- A `FunLike` type with negation that satisfies `(- f) x = - (f x)` is an involutive
negation if `β` is an involutive negation. -/]
protected abbrev involutiveInv [∀ a, InvolutiveInv (β a)] [IsInvApply F] : InvolutiveInv F :=
  DFunLike.coe_injective.involutiveInv (fun (f : F) ↦ (f : (a : α) → β a)) coe_inv

/-- A `FunLike` type with `1` and inverse is an `InvOneClass` if `β` is an `InvOneClass`. -/
@[to_additive /-- A `FunLike` type with `0` and negation is a `NegZeroClass` if `β` is a
`NegZeroClass`. -/]
protected abbrev invOneClass [∀ a, InvOneClass (β a)] [IsOneApply F] [IsInvApply F] :
    InvOneClass F :=
  DFunLike.coe_injective.invOneClass (fun (f : F) ↦ (f : (a : α) → β a)) coe_one coe_inv

variable [Div F] [Pow F ℤ]

/-- A `FunLike` type is a `DivInvMonoid` if `β` is a `DivInvMonoid`. -/
@[to_additive subNegMonoid /-- A `FunLike` type is a `SubNegMonoid` if `β` is a `SubNegMonoid`. -/]
protected abbrev divInvMonoid [∀ a, DivInvMonoid (β a)] [IsOneApply F] [IsMulApply F]
    [IsInvApply F] [IsDivApply F] [IsPowApply ℕ F] [IsPowApply ℤ F] :
    DivInvMonoid F :=
  DFunLike.coe_injective.divInvMonoid (fun (f : F) ↦ (f : (a : α) → β a)) coe_one coe_mul coe_inv
    coe_div coe_pow coe_pow

/-- A `FunLike` type is a `DivInvOneMonoid` if `β` is a `DivInvOneMonoid`. -/
@[to_additive
/-- A `FunLike` type is a `SubNegOneMonoid` if `β` is a `SubNegOneMonoid`. -/]
protected abbrev divInvOneMonoid [∀ a, DivInvOneMonoid (β a)] [IsOneApply F] [IsMulApply F]
    [IsInvApply F] [IsDivApply F] [IsPowApply ℕ F] [IsPowApply ℤ F] :
    DivInvOneMonoid F :=
  DFunLike.coe_injective.divInvOneMonoid (fun (f : F) ↦ (f : (a : α) → β a)) coe_one coe_mul
    coe_inv coe_div coe_pow coe_pow

/-- A `FunLike` type is a division monoid if `β` is a division monoid. -/
@[to_additive /-- A `FunLike` type is a subtraction monoid if `β` is a subtraction monoid. -/]
protected abbrev divisionMonoid [∀ a, DivisionMonoid (β a)] [IsOneApply F] [IsMulApply F]
    [IsInvApply F] [IsDivApply F] [IsPowApply ℕ F] [IsPowApply ℤ F] :
    DivisionMonoid F :=
  DFunLike.coe_injective.divisionMonoid (fun (f : F) ↦ (f : (a : α) → β a)) coe_one coe_mul
    coe_inv coe_div coe_pow coe_pow

/-- A `FunLike` type is a division commutative monoid if `β` is a division commutative monoid. -/
@[to_additive subtractionCommMonoid /-- A `FunLike` type is a subtraction commutative monoid if `β`
is a subtraction commutative monoid. -/]
protected abbrev divisionCommMonoid [∀ a, DivisionCommMonoid (β a)] [IsOneApply F] [IsMulApply F]
    [IsInvApply F] [IsDivApply F] [IsPowApply ℕ F] [IsPowApply ℤ F] :
    DivisionCommMonoid F :=
  DFunLike.coe_injective.divisionCommMonoid (fun (f : F) ↦ (f : (a : α) → β a)) coe_one coe_mul
    coe_inv coe_div coe_pow coe_pow

/-- A `FunLike` type is a group if `β` is a group. -/
@[to_additive /-- A `FunLike` type is an additive group if `β` is an additive group. -/]
protected abbrev group [∀ a, Group (β a)] [IsOneApply F] [IsMulApply F] [IsInvApply F]
    [IsDivApply F] [IsPowApply ℕ F] [IsPowApply ℤ F] :
    Group F :=
  DFunLike.coe_injective.group (fun (f : F) ↦ (f : (a : α) → β a)) coe_one coe_mul coe_inv coe_div
    coe_pow coe_pow

/-- A `FunLike` type is a commutative group if `β` is a commutative group. -/
@[to_additive /-- A `FunLike` type is an additive commutative group if `β` is an additive
commutative group. -/]
protected abbrev commGroup [∀ a, CommGroup (β a)] [IsOneApply F] [IsMulApply F] [IsInvApply F]
    [IsDivApply F] [IsPowApply ℕ F] [IsPowApply ℤ F] :
    CommGroup F :=
  DFunLike.coe_injective.commGroup (fun (f : F) ↦ (f : (a : α) → β a)) coe_one coe_mul coe_inv
    coe_div coe_pow coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f (g x)` and `1 x = x` is a monoid. -/
protected abbrev compMonoid {F : Type*} [FunLike F α α] [One F] [Mul F] [NPow F]
    [IsOneApplyEqSelf F] [IsMulApplyEqComp F] [IsNPowApplyEqIterate F] : Monoid F where
  mul_assoc _ _ _ := by apply DFunLike.ext; simp
  one_mul _ := by apply DFunLike.ext; simp
  mul_one _ := by apply DFunLike.ext; simp
  npow_zero _ := by apply DFunLike.ext; simp [pow_apply_eq_iterate]
  npow_succ _ _ := by apply DFunLike.ext; simp [pow_apply_eq_iterate]

end GroupInstances

section TorsionFree

/-- A type `F` that satisfies `FunLike F α β` is torsion-free if `β` is torsion-free. -/
@[to_additive /-- A type `F` that satisfies `FunLike F α β` is torsion-free if `β` is
torsion-free. -/]
protected theorem isMulTorsionFree [∀ a, Monoid (β a)] [Monoid F] [IsOneApply F] [IsMulApply F]
    [∀ a, IsMulTorsionFree (β a)] : IsMulTorsionFree F :=
  DFunLike.coe_injective.isMulTorsionFree (coeMonoidHom F α β)

end TorsionFree

end FunLike
