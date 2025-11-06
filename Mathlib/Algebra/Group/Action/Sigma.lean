/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Data.Sigma.Basic

/-!
# Sigma instances for additive and multiplicative actions

This file defines instances for arbitrary sum of additive and multiplicative actions.

## See also

* `Mathlib/Algebra/Group/Action/Option.lean`
* `Mathlib/Algebra/Group/Action/Pi.lean`
* `Mathlib/Algebra/Group/Action/Prod.lean`
* `Mathlib/Algebra/Group/Action/Sum.lean`
-/

assert_not_exists MonoidWithZero


variable {ι : Type*} {M N : Type*} {α : ι → Type*}

namespace Sigma

section SMul

variable [∀ i, SMul M (α i)] [∀ i, SMul N (α i)] (a : M) (i : ι) (b : α i) (x : Σ i, α i)

@[to_additive Sigma.VAdd]
instance : SMul M (Σ i, α i) :=
  ⟨fun a => (Sigma.map id) fun _ => (a • ·)⟩

@[to_additive]
theorem smul_def : a • x = x.map id fun _ => (a • ·) :=
  rfl

@[to_additive (attr := simp)]
theorem smul_mk : a • mk i b = ⟨i, a • b⟩ :=
  rfl

@[to_additive]
instance instIsScalarTowerOfSMul [SMul M N] [∀ i, IsScalarTower M N (α i)] :
    IsScalarTower M N (Σ i, α i) :=
  ⟨fun a b x => by
    cases x
    rw [smul_mk, smul_mk, smul_mk, smul_assoc]⟩

@[to_additive]
instance [∀ i, SMulCommClass M N (α i)] : SMulCommClass M N (Σ i, α i) :=
  ⟨fun a b x => by
    cases x
    rw [smul_mk, smul_mk, smul_mk, smul_mk, smul_comm]⟩

@[to_additive]
instance [∀ i, SMul Mᵐᵒᵖ (α i)] [∀ i, IsCentralScalar M (α i)] : IsCentralScalar M (Σ i, α i) :=
  ⟨fun a x => by
    cases x
    rw [smul_mk, smul_mk, op_smul_eq_smul]⟩

/-- This is not an instance because `i` becomes a metavariable. -/
@[to_additive /-- This is not an instance because `i` becomes a metavariable. -/]
protected theorem FaithfulSMul' [FaithfulSMul M (α i)] : FaithfulSMul M (Σ i, α i) :=
  ⟨fun h => eq_of_smul_eq_smul fun a : α i => heq_iff_eq.1 (Sigma.ext_iff.1 <| h <| mk i a).2⟩

@[to_additive]
instance [Nonempty ι] [∀ i, FaithfulSMul M (α i)] : FaithfulSMul M (Σ i, α i) :=
  (Nonempty.elim ‹_›) fun i => Sigma.FaithfulSMul' i

end SMul

@[to_additive]
instance {m : Monoid M} [∀ i, MulAction M (α i)] :
    MulAction M (Σ i, α i) where
  mul_smul a b x := by
    cases x
    rw [smul_mk, smul_mk, smul_mk, mul_smul]
  one_smul x := by
    cases x
    rw [smul_mk, one_smul]

end Sigma
