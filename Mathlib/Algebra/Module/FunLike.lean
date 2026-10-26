/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Group.FunLike
public import Mathlib.LinearAlgebra.Pi

/-! # Module instances for `FunLike` types
In this file we define various instances related to modules for `FunLike` types.

Note that currently, these are not registered as instances, but only `abbrev`s to avoid long
typeclass searches.

-/

public section

variable {R M M' F α β : Type*} [i : FunLike F α β]

namespace FunLike

section LinearMap

variable [Semiring R] [AddCommMonoid F] [AddCommMonoid β] [IsAddApply F] [Module R F] [Module R β]
  [IsSMulApply R F]

variable (R F) in
/-- Coercion as a linear map. -/
@[expose]
def coeₗ : F →ₗ[R] α → β where
  toFun f := f
  map_add' := by simp
  map_smul' := by simp

@[simp]
theorem coeₗ_apply (f : F) : coeₗ R F f = f := rfl

@[norm_cast]
theorem coe_coeₗ : (coeₗ R F : F → α → β) = DFunLike.coe := rfl

@[simp]
theorem toAddMonoidHom_coeₗ [IsZeroApply F] : (coeₗ R F).toAddMonoidHom = coeAddMonoidHom F α β :=
  rfl

variable (R F) in
/-- Evaluation as a linear map. -/
@[expose]
def evalₗ (x : α) : F →ₗ[R] β := (LinearMap.proj x).comp (coeₗ R F)

@[simp]
theorem evalₗ_apply (x : α) (f : F) : evalₗ R F x f = f x := rfl

@[simp]
theorem toAddMonoidHom_evalₗ [IsZeroApply F] (x : α) :
    (evalₗ R F x).toAddMonoidHom = evalAddMonoidHom F x := rfl

end LinearMap

section SMulInstances

variable [SMul M β] [SMul M' β] [SMul M F] [SMul M' F] [IsSMulApply M F] [IsSMulApply M' F]

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
    [IsCentralScalar M β] [IsSMulApply M F] [IsSMulApply Mᵐᵒᵖ F] :
    IsCentralScalar M F where
  op_smul_eq_smul a b := by apply DFunLike.ext; simp [op_smul_eq_smul]

/-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x` and
`0 x = 0`, `(f + g) x = f x + g x` is a `DistribSMul` if `β` is a `DistribSMul`. -/
protected abbrev distribSMul [AddZeroClass β] [AddZeroClass F] [DistribSMul M β]
    [SMul M F] [IsZeroApply F] [IsAddApply F] [IsSMulApply M F] :
    DistribSMul M F :=
  DFunLike.coe_injective.distribSMul (coeAddMonoidHom F α β) FunLike.coe_smul

/-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x`
is a `MulAction` if `β` is a `MulAction`. -/
@[to_additive /-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x`
is an `AddAction` if `β` is an `AddAction`. -/]
protected abbrev mulAction [SMul M F] [Monoid M] [MulAction M β] [IsSMulApply M F] :
    MulAction M F :=
  DFunLike.coe_injective.mulAction _ FunLike.coe_smul

/-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x`, `0 x = 0`,
`(f + g) x = f x + g x` is a `DistribMulAction` if `β` is a `DistribMulAction`. -/
protected abbrev distribMulAction [Monoid M] [AddMonoid β] [AddMonoid F] [DistribMulAction M β]
    [SMul M F] [IsZeroApply F] [IsAddApply F] [IsSMulApply M F] :
    DistribMulAction M F :=
  DFunLike.coe_injective.distribMulAction (coeAddMonoidHom F α β) FunLike.coe_smul

variable [Semiring M] [AddCommMonoid β] [Module M β] [AddCommMonoid F]

/-- A `FunLike` type is a `Module` if `β` is a `Module`. -/
protected abbrev module [IsZeroApply F] [IsAddApply F] [SMul M F] [IsSMulApply M F] :
    Module M F :=
  coeAddHom_injective.module M (coeAddMonoidHom F α β) coe_smul

protected theorem moduleIsTorsionFree [Module M F] [IsSMulApply M F]
    [Module.IsTorsionFree M β] : Module.IsTorsionFree M F :=
  DFunLike.coe_injective.moduleIsTorsionFree _ FunLike.coe_smul

end ModuleInstance

end FunLike
