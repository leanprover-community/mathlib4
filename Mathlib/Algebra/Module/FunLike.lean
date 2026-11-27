/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Module.Torsion.Pi

import Mathlib.Algebra.Group.FunLike

/-! # Module instances for `FunLike` types
In this file we define various instances related to modules for `FunLike` types.

Note that currently, these are not registered as instances, but only `abbrev`s to avoid long
typeclass searches.

We also define the linear map `FunLike.coeLinearMap : F →ₗ[M] (a : α) → β a` that acts by
coercion.
-/

@[expose] public section

namespace FunLike

variable {M F α : Type*} {β : α → Type*} [DFunLike F α β]
  [Semiring M] [∀ a, AddCommMonoid (β a)] [∀ a, Module M (β a)] [AddCommMonoid F]

/-- A `FunLike` type is a `Module` if `β` is a `Module`. -/
protected abbrev module [IsZeroApply F] [IsAddApply F] [SMul M F] [IsSMulApply M F] :
    Module M F :=
  coeAddHom_injective.module M (coeAddMonoidHom F α β) coe_smul

protected theorem moduleIsTorsionFree [Module M F] [IsSMulApply M F]
    [∀ a, Module.IsTorsionFree M (β a)] : Module.IsTorsionFree M F :=
  DFunLike.coe_injective.moduleIsTorsionFree _ FunLike.coe_smul

section CoeLinearMap

variable [Module M F] [IsAddApply F] [IsSMulApply M F]

variable (M F α β) in
/-- Coercion as a linear map. -/
def coeLinearMap : F →ₗ[M] (a : α) → β a where
  toFun f := f
  map_add' := coe_add
  map_smul' := coe_smul

@[simp]
theorem coeLinearMap_apply (f : F) : coeLinearMap M F α β f = f := rfl

@[norm_cast]
theorem coe_coeLinearMap : (coeLinearMap M F α β : F → (a : α) → β a) = DFunLike.coe := rfl

theorem coeLinearMap_injective : Function.Injective (coeLinearMap M F α β) :=
  DFunLike.coe_injective

@[simp]
theorem toAddMonoidHom_coeLinearMap [IsZeroApply F] :
    (coeLinearMap M F α β).toAddMonoidHom = coeAddMonoidHom F α β :=
  rfl

end CoeLinearMap

end FunLike
