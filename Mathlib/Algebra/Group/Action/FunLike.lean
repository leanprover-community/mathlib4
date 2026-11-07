/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.IsApply

/-! # SMul instances for `FunLike` types

In this file we define various instances related to scalar multiplications for `FunLike` types.

Note that currently, these are not registered as instances, but only `abbrev`s to avoid long
typeclass searches.

-/

public section

variable {M M' F α β : Type*} [i : FunLike F α β]

namespace FunLike

section SMulInstances

variable [SMul M β] [SMul M' β] [SMul M F] [SMul M' F] [IsSMulApply M F] [IsSMulApply M' F]

include i in
protected theorem isScalarTower [SMul M M'] [IsScalarTower M M' β] : IsScalarTower M M' F where
  smul_assoc _ _ _ := by apply DFunLike.ext; simp

include i in
@[to_additive]
protected theorem smulCommClass [SMulCommClass M M' β] : SMulCommClass M M' F where
  smul_comm _ _ _ := by apply DFunLike.ext; simp [smul_comm]

end SMulInstances

section ModuleInstance

include i in
protected theorem isCentralScalar [SMul M F] [SMul Mᵐᵒᵖ F] [SMul M β] [SMul Mᵐᵒᵖ β]
    [IsCentralScalar M β] [IsSMulApply M F] [IsSMulApply Mᵐᵒᵖ F] :
    IsCentralScalar M F where
  op_smul_eq_smul a b := by apply DFunLike.ext; simp [op_smul_eq_smul]

/-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x`
is a `MulAction` if `β` is a `MulAction`. -/
@[to_additive /-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x`
is an `AddAction` if `β` is an `AddAction`. -/]
protected abbrev mulAction [SMul M F] [Monoid M] [MulAction M β] [IsSMulApply M F] :
    MulAction M F :=
  DFunLike.coe_injective.mulAction _ FunLike.coe_smul

end ModuleInstance

end FunLike
