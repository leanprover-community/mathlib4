/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
Ported by: Joël Riou

! This file was ported from Lean 3 source module data.set.opposite
! leanprover-community/mathlib commit fc2ed6f838ce7c9b7c7171e58d78eaf7b438fb0e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Opposite
import Mathlib.Data.Set.Image

/-!
# The opposite of a set

The opposite of a set `s` is simply the set obtained by taking the opposite of each member of `s`.
-/

variable {α : Type _}

open Opposite

namespace Set

/-- The opposite of a set `s` is the set obtained by taking the opposite of each member of `s`. -/
protected def op (s : Set α) : Set αᵒᵖ :=
  unop ⁻¹' s

/-- The unop of a set `s` is the set obtained by taking the unop of each member of `s`. -/
protected def unop (s : Set αᵒᵖ) : Set α :=
  op ⁻¹' s

@[simp]
theorem mem_op {s : Set α} {a : αᵒᵖ} : a ∈ s.op ↔ unop a ∈ s :=
  Iff.rfl

@[simp 1100]
theorem op_mem_op {s : Set α} {a : α} : op a ∈ s.op ↔ a ∈ s := by rfl

@[simp]
theorem mem_unop {s : Set αᵒᵖ} {a : α} : a ∈ s.unop ↔ op a ∈ s :=
  Iff.rfl

@[simp 1100]
theorem unop_mem_unop {s : Set αᵒᵖ} {a : αᵒᵖ} : unop a ∈ s.unop ↔ a ∈ s := by rfl

@[simp]
theorem op_unop (s : Set α) : s.op.unop = s := rfl

@[simp]
theorem unop_op (s : Set αᵒᵖ) : s.unop.op = s := rfl

/-- The members of the opposite of a set are in bijection with the members of the set itself. -/
@[simps]
def opEquiv_self (s : Set α) : s.op ≃ s :=
  ⟨fun x ↦ ⟨unop x, x.2⟩, fun x ↦ ⟨op x, x.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
#align set.op_equiv_self Set.opEquiv_self

/-- Taking opposites as an equivalence of powersets. -/
@[simps]
def opEquiv : Set α ≃ Set αᵒᵖ :=
  ⟨Set.op, Set.unop, op_unop, unop_op⟩

@[simp]
theorem singleton_op (x : α) : ({x} : Set α).op = {op x} := rfl

@[simp]
theorem singleton_unop (x : αᵒᵖ) : ({x} : Set αᵒᵖ).unop = {unop x} := rfl

@[simp]
theorem singleton_op_unop (x : α) : ({op x} : Set αᵒᵖ).unop = {x} := rfl

@[simp]
theorem singleton_unop_op (x : αᵒᵖ) : ({unop x} : Set α).op = {x} := rfl

end Set
