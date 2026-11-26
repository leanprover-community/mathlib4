/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.IsApply

/-! # `SMul` instances for `FunLike` types

In this file we define various instances related to scalar multiplications for `FunLike` types.

Note that currently, these are not registered as instances, but only `abbrev`s to avoid long
typeclass searches.
-/

public section

variable {M M' F α : Type*} {β : α → Type*} [i : DFunLike F α β]

namespace FunLike

section SMulInstances

variable [∀ a, SMul M (β a)] [∀ a, SMul M' (β a)] [SMul M F] [SMul M' F] [IsSMulApply M F]
  [IsSMulApply M' F]

include i in
protected theorem isScalarTower [SMul M M'] [∀ a, IsScalarTower M M' (β a)] :
    IsScalarTower M M' F where
  smul_assoc _ _ _ := by apply DFunLike.ext; simp

include i in
@[to_additive]
protected theorem smulCommClass [∀ a, SMulCommClass M M' (β a)] : SMulCommClass M M' F where
  smul_comm _ _ _ := by apply DFunLike.ext; simp [smul_comm]

end SMulInstances

include i in
protected theorem isCentralScalar [SMul M F] [SMul Mᵐᵒᵖ F] [∀ a, SMul M (β a)]
    [∀ a, SMul Mᵐᵒᵖ (β a)] [∀ a, IsCentralScalar M (β a)] [IsSMulApply M F] [IsSMulApply Mᵐᵒᵖ F] :
    IsCentralScalar M F where
  op_smul_eq_smul a b := by apply DFunLike.ext; simp [op_smul_eq_smul]

/-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x`
is a `MulAction` if `β` is a `MulAction`. -/
@[to_additive /-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x`
is an `AddAction` if `β` is an `AddAction`. -/]
protected abbrev mulAction [SMul M F] [Monoid M] [∀ a, MulAction M (β a)] [IsSMulApply M F] :
    MulAction M F :=
  DFunLike.coe_injective.mulAction _ FunLike.coe_smul

end FunLike
