/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Group.FunLike
public import Mathlib.Algebra.GroupWithZero.Action.Pi

/-! # `SMul` instances for `FunLike` types

In this file we define various instances related to scalar multiplications for `FunLike` types.

Note that currently, these are not registered as instances, but only `abbrev`s to avoid long
typeclass searches.
-/

public section

namespace FunLike

variable {M M' F α : Type*} {β : α → Type*} [i : DFunLike F α β]

/-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x` and
`0 x = 0`, `(f + g) x = f x + g x` is a `DistribSMul` if `β` is a `DistribSMul`. -/
protected abbrev distribSMul [∀ a, AddZeroClass (β a)] [AddZeroClass F] [∀ a, DistribSMul M (β a)]
    [SMul M F] [IsZeroApply F] [IsAddApply F] [IsSMulApply M F] :
    DistribSMul M F :=
  DFunLike.coe_injective.distribSMul (coeAddMonoidHom F α β) FunLike.coe_smul

/-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x`, `0 x = 0`,
`(f + g) x = f x + g x` is a `DistribMulAction` if `β` is a `DistribMulAction`. -/
protected abbrev distribMulAction [Monoid M] [∀ a, AddMonoid (β a)] [AddMonoid F]
    [∀ a, DistribMulAction M (β a)] [SMul M F] [IsZeroApply F] [IsAddApply F] [IsSMulApply M F] :
    DistribMulAction M F :=
  DFunLike.coe_injective.distribMulAction (coeAddMonoidHom F α β) FunLike.coe_smul

end FunLike
