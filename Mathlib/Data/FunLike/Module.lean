/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Data.FunLike.Group
public import Mathlib.Algebra.Module.Pi

/-! # Module instances for `FunLike` types
In this file we define various instances related to modules for `FunLike` types.
-/

public section

variable {M M' F α β : Type*} [i : FunLike F α β]

namespace FunLike

section SMulInstances

variable [SMul M β] [SMul M' β] [SMul M F] [SMul M' F] [IsSMulApply M F α β] [IsSMulApply M' F α β]

include i in
protected theorem isScalarTower [SMul M M'] [IsScalarTower M M' β] : IsScalarTower M M' F where
  smul_assoc _ _ _ := by apply DFunLike.ext; simp

include i in
protected theorem smulCommClass [SMulCommClass M M' β] : SMulCommClass M M' F where
  smul_comm _ _ _ := by apply DFunLike.ext; simp [smul_comm]

end SMulInstances

section ModuleInstance

include i in
protected theorem isCentralScalar [SMul M F] [SMul Mᵐᵒᵖ F] [SMul M β] [SMul Mᵐᵒᵖ β]
    [IsCentralScalar M β] [IsSMulApply M F α β] [IsSMulApply Mᵐᵒᵖ F α β] :
    IsCentralScalar M F where
  op_smul_eq_smul a b := by apply DFunLike.ext; simp [op_smul_eq_smul]

/-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x` and
`0 x = 0`, `(f + g) x = f x + g x` is a `DistribSMul` if `β` is a `DistribSMul`. -/
protected abbrev distribSMul [AddZeroClass β] [AddZeroClass F] [DistribSMul M β]
    [SMul M F] [IsZeroApply F α β] [IsAddApply F α β] [IsSMulApply M F α β] :
    DistribSMul M F :=
  DFunLike.coe_injective.distribSMul (coeAddHom F α β) FunLike.coe_smul

/-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x`
is a `MulAction` if `β` is a `MulAction`. -/
@[to_additive /-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x`
is an `AddAction` if `β` is an `AddAction`. -/]
protected abbrev mulAction [SMul M F] [Monoid M] [MulAction M β] [IsSMulApply M F α β] :
    MulAction M F :=
  DFunLike.coe_injective.mulAction _ FunLike.coe_smul

/-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x`, `0 x = 0`,
`(f + g) x = f x + g x` is a `DistribMulAction` if `β` is a `DistribMulAction`. -/
protected abbrev distribMulAction [Monoid M] [AddMonoid β] [AddMonoid F] [DistribMulAction M β]
    [SMul M F] [IsZeroApply F α β] [IsAddApply F α β] [IsSMulApply M F α β] :
    DistribMulAction M F :=
  DFunLike.coe_injective.distribMulAction (coeAddHom F α β) FunLike.coe_smul

variable [Semiring M] [AddCommMonoid β] [Module M β] [AddCommMonoid F] [SMul M F]
  [IsZeroApply F α β] [IsAddApply F α β] [IsSMulApply ℕ F α β] [IsSMulApply M F α β]

/-- A `FunLike` type is a `Module` if `β` is a `Module`. -/
protected abbrev module : Module M F :=
  coeAddHom_injective.module M (coeAddHom F α β) coe_smul

end ModuleInstance

end FunLike
