/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.GroupTheory.GroupAction.Defs

#align_import group_theory.group_action.sigma from "leanprover-community/mathlib"@"f1a2caaf51ef593799107fe9a8d5e411599f3996"

/-!
# Sigma instances for additive and multiplicative actions

This file defines instances for arbitrary sum of additive and multiplicative actions.

## See also

* `GroupTheory.GroupAction.Pi`
* `GroupTheory.GroupAction.Prod`
* `GroupTheory.GroupAction.Sum`
-/


variable {ι : Type*} {M N : Type*} {α : ι → Type*}

namespace Sigma

section SMul

variable [∀ i, SMul M (α i)] [∀ i, SMul N (α i)] (a : M) (i : ι) (b : α i) (x : Σi, α i)

@[to_additive Sigma.VAdd]
instance : SMul M (Σi, α i) :=
  ⟨fun a => (Sigma.map id) fun _ => (· • ·) a⟩

@[to_additive]
theorem smul_def : a • x = x.map id fun _ => (· • ·) a :=
  rfl
#align sigma.smul_def Sigma.smul_def
#align sigma.vadd_def Sigma.vadd_def

@[to_additive (attr := simp)]
theorem smul_mk : a • mk i b = ⟨i, a • b⟩ :=
  rfl
#align sigma.smul_mk Sigma.smul_mk
#align sigma.vadd_mk Sigma.vadd_mk

@[to_additive]
instance [SMul M N] [∀ i, IsScalarTower M N (α i)] : IsScalarTower M N (Σi, α i) :=
  ⟨fun a b x => by
    cases x
    -- ⊢ (a • b) • { fst := fst✝, snd := snd✝ } = a • b • { fst := fst✝, snd := snd✝ }
    rw [smul_mk, smul_mk, smul_mk, smul_assoc]⟩
    -- 🎉 no goals

@[to_additive]
instance [∀ i, SMulCommClass M N (α i)] : SMulCommClass M N (Σi, α i) :=
  ⟨fun a b x => by
    cases x
    -- ⊢ a • b • { fst := fst✝, snd := snd✝ } = b • a • { fst := fst✝, snd := snd✝ }
    rw [smul_mk, smul_mk, smul_mk, smul_mk, smul_comm]⟩
    -- 🎉 no goals

@[to_additive]
instance [∀ i, SMul Mᵐᵒᵖ (α i)] [∀ i, IsCentralScalar M (α i)] : IsCentralScalar M (Σi, α i) :=
  ⟨fun a x => by
    cases x
    -- ⊢ MulOpposite.op a • { fst := fst✝, snd := snd✝ } = a • { fst := fst✝, snd :=  …
    rw [smul_mk, smul_mk, op_smul_eq_smul]⟩
    -- 🎉 no goals

/-- This is not an instance because `i` becomes a metavariable. -/
@[to_additive "This is not an instance because `i` becomes a metavariable."]
protected theorem FaithfulSMul' [FaithfulSMul M (α i)] : FaithfulSMul M (Σi, α i) :=
  ⟨fun h => eq_of_smul_eq_smul fun a : α i => heq_iff_eq.1 (ext_iff.1 <| h <| mk i a).2⟩
#align sigma.has_faithful_smul' Sigma.FaithfulSMul'
#align sigma.has_faithful_vadd' Sigma.FaithfulVAdd'

@[to_additive]
instance [Nonempty ι] [∀ i, FaithfulSMul M (α i)] : FaithfulSMul M (Σi, α i) :=
  (Nonempty.elim ‹_›) fun i => Sigma.FaithfulSMul' i

end SMul

@[to_additive]
instance {m : Monoid M} [∀ i, MulAction M (α i)] :
    MulAction M (Σi, α i) where
  mul_smul a b x := by
    cases x
    -- ⊢ (a * b) • { fst := fst✝, snd := snd✝ } = a • b • { fst := fst✝, snd := snd✝ }
    rw [smul_mk, smul_mk, smul_mk, mul_smul]
    -- 🎉 no goals
    -- ⊢ 1 • { fst := fst✝, snd := snd✝ } = { fst := fst✝, snd := snd✝ }
  one_smul x := by
    -- 🎉 no goals
    cases x
    rw [smul_mk, one_smul]

end Sigma
