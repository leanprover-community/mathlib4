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

-/

public section

variable {R M F α β : Type*} [i : FunLike F α β]

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

section ModuleInstance

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
