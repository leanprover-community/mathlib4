/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Sigma instances for additive and multiplicative actions

This file defines instances for arbitrary sum of additive and multiplicative actions.

## See also

* `group_theory.group_action.pi`
* `group_theory.group_action.prod`
* `group_theory.group_action.sum`
-/


variable {ι : Type _} {M N : Type _} {α : ι → Type _}

namespace Sigma

section HasSmul

variable [∀ i, HasSmul M (α i)] [∀ i, HasSmul N (α i)] (a : M) (i : ι) (b : α i) (x : Σi, α i)

@[to_additive Sigma.hasVadd]
instance : HasSmul M (Σi, α i) :=
  ⟨fun a => (Sigma.map id) fun i => (· • ·) a⟩

@[to_additive]
theorem smul_def : a • x = x.map id fun i => (· • ·) a :=
  rfl
#align sigma.smul_def Sigma.smul_def

@[simp, to_additive]
theorem smul_mk : a • mk i b = ⟨i, a • b⟩ :=
  rfl
#align sigma.smul_mk Sigma.smul_mk

@[to_additive]
instance [HasSmul M N] [∀ i, IsScalarTower M N (α i)] : IsScalarTower M N (Σi, α i) :=
  ⟨fun a b x => by
    cases x
    rw [smul_mk, smul_mk, smul_mk, smul_assoc]⟩

@[to_additive]
instance [∀ i, SmulCommClass M N (α i)] : SmulCommClass M N (Σi, α i) :=
  ⟨fun a b x => by
    cases x
    rw [smul_mk, smul_mk, smul_mk, smul_mk, smul_comm]⟩

@[to_additive]
instance [∀ i, HasSmul Mᵐᵒᵖ (α i)] [∀ i, IsCentralScalar M (α i)] : IsCentralScalar M (Σi, α i) :=
  ⟨fun a x => by
    cases x
    rw [smul_mk, smul_mk, op_smul_eq_smul]⟩

/-- This is not an instance because `i` becomes a metavariable. -/
@[to_additive "This is not an instance because `i` becomes a metavariable."]
protected theorem has_faithful_smul' [HasFaithfulSmul M (α i)] : HasFaithfulSmul M (Σi, α i) :=
  ⟨fun x y h => eq_of_smul_eq_smul fun a : α i => heq_iff_eq.1 (ext_iff.1 <| h <| mk i a).2⟩
#align sigma.has_faithful_smul' Sigma.has_faithful_smul'

@[to_additive]
instance [Nonempty ι] [∀ i, HasFaithfulSmul M (α i)] : HasFaithfulSmul M (Σi, α i) :=
  (Nonempty.elim ‹_›) fun i => Sigma.has_faithful_smul' i

end HasSmul

@[to_additive]
instance {m : Monoid M} [∀ i, MulAction M (α i)] :
    MulAction M
      (Σi,
        α
          i) where
  mul_smul a b x := by
    cases x
    rw [smul_mk, smul_mk, smul_mk, mul_smul]
  one_smul x := by
    cases x
    rw [smul_mk, one_smul]

end Sigma
