/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Data.Fintype.Basic

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

assert_not_exists MonoidWithZero

namespace Equiv
variable {M N O α β : Type*}

variable (M) [Monoid M] in
/-- Transfer `MulAction` across an `Equiv` -/
@[to_additive /-- Transfer `AddAction` across an `Equiv` -/]
protected abbrev mulAction (e : α ≃ β) [MulAction M β] : MulAction M α where
  __ := e.smul M
  one_smul := by simp [smul_def]
  mul_smul := by simp [smul_def, mul_smul]

variable (M N) [SMul M β] [SMul N β] in
/-- Transfer `SMulCommClass` across an `Equiv` -/
@[to_additive /-- Transfer `VAddCommClass` across an `Equiv` -/]
protected lemma smulCommClass (e : α ≃ β) [SMulCommClass M N β] :
    letI := e.smul M
    letI := e.smul N
    SMulCommClass M N α :=
  letI := e.smul M
  letI := e.smul N
  { smul_comm := by simp [smul_def, smul_comm] }

variable (M N) [SMul M N] [SMul M β] [SMul N β] in
/-- Transfer `IsScalarTower` across an `Equiv` -/
@[to_additive /-- Transfer `VAddAssocClass` across an `Equiv` -/]
protected lemma isScalarTower (e : α ≃ β) [IsScalarTower M N β] :
    letI := e.smul M
    letI := e.smul N
    IsScalarTower M N α :=
  letI := e.smul M
  letI := e.smul N
  { smul_assoc := by simp [smul_def, smul_assoc] }

variable (M) [SMul M β] [SMul Mᵐᵒᵖ β] in
/-- Transfer `IsCentralScalar` across an `Equiv` -/
@[to_additive /-- Transfer `IsCentralVAdd` across an `Equiv` -/]
protected lemma isCentralScalar (e : α ≃ β) [IsCentralScalar M β] :
    letI := e.smul M
    letI := e.smul Mᵐᵒᵖ
    IsCentralScalar M α :=
  letI := e.smul M
  letI := e.smul Mᵐᵒᵖ
  { op_smul_eq_smul := by simp [smul_def, op_smul_eq_smul] }

variable (M) [Monoid M] [Monoid O] in
/-- Transfer `MulDistribMulAction` across an `Equiv` -/
protected abbrev mulDistribMulAction (e : N ≃ O) [MulDistribMulAction M O] :
    letI := e.monoid
    MulDistribMulAction M N :=
  letI := e.monoid
  { e.mulAction M with
    smul_one := by simp [one_def, smul_def, smul_one]
    smul_mul := by simp [mul_def, smul_def, smul_mul'] }

end Equiv
