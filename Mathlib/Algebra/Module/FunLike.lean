/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Group.FunLike
public import Mathlib.Algebra.Module.Torsion.Pi

/-! # Module instances for `FunLike` types
In this file we define various instances related to modules for `FunLike` types.

Note that currently, these are not registered as instances, but only `abbrev`s to avoid long
typeclass searches.

## TODO:
Add definitions and API for the coercion being a linear map, similar to `FunLike.coeMonoidHom`,
and related definitions.

-/

public section

namespace FunLike

variable {M F α β : Type*} [FunLike F α β]
  [Semiring M] [AddCommMonoid β] [Module M β] [AddCommMonoid F]

/-- A `FunLike` type is a `Module` if `β` is a `Module`. -/
protected abbrev module [IsZeroApply F] [IsAddApply F] [SMul M F] [IsSMulApply M F] :
    Module M F :=
  coeAddHom_injective.module M (coeAddMonoidHom F α β) coe_smul

protected theorem moduleIsTorsionFree [Module M F] [IsSMulApply M F]
    [Module.IsTorsionFree M β] : Module.IsTorsionFree M F :=
  DFunLike.coe_injective.moduleIsTorsionFree _ FunLike.coe_smul

end FunLike
