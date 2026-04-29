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

variable {M M' F α β : Type*} [FunLike F α β]

namespace FunLike

section SMulInstances

variable [SMul M β] [SMul M' β] [SMul M F] [SMul M' F] [IsSMulApply M F α β] [IsSMulApply M' F α β]

protected abbrev isScalarTower [SMul M M'] [IsScalarTower M M' β] : IsScalarTower M M' F where
  smul_assoc _ _ _ := by apply DFunLike.ext; simp

protected abbrev smulCommClass [SMulCommClass M M' β] : SMulCommClass M M' F where
  smul_comm _ _ _ := by apply DFunLike.ext; simp [smul_comm]

end SMulInstances

section ModuleInstance

protected abbrev isCentralScalar [SMul M F] [SMul Mᵐᵒᵖ F] [SMul M β] [SMul Mᵐᵒᵖ β]
    [IsCentralScalar M β] [IsSMulApply M F α β] [IsSMulApply Mᵐᵒᵖ F α β] :
    IsCentralScalar M F where
  op_smul_eq_smul a b := by apply DFunLike.ext; simp [op_smul_eq_smul]

protected abbrev distribSMul [AddZeroClass β] [AddZeroClass F] [DistribSMul M β]
    [SMul M F] [IsZeroApply F α β] [IsAddApply F α β] [IsSMulApply M F α β] :
    DistribSMul M F :=
  DFunLike.coe_injective.distribSMul (coeAddHom F α β) FunLike.coe_smul

@[to_additive]
protected abbrev mulAction [SMul M F] [Monoid M] [MulAction M β] [IsSMulApply M F α β] :
    MulAction M F :=
  DFunLike.coe_injective.mulAction _ FunLike.coe_smul

protected abbrev distribMulAction [Monoid M] [AddMonoid β] [AddMonoid F] [DistribMulAction M β]
    [SMul M F] [IsZeroApply F α β] [IsAddApply F α β] [IsSMulApply M F α β] :
    DistribMulAction M F :=
  DFunLike.coe_injective.distribMulAction (coeAddHom F α β) FunLike.coe_smul

variable [Semiring M] [AddCommMonoid β] [Module M β] [AddCommMonoid F] [SMul M F]
  [IsZeroApply F α β] [IsAddApply F α β] [IsSMulApply ℕ F α β] [IsSMulApply M F α β]

protected abbrev module : Module M F :=
  coeAddHom_injective.module M (coeAddHom F α β) coe_smul

end ModuleInstance

end FunLike
