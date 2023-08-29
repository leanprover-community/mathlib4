/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.Data.Opposite
import Mathlib.Data.Set.Image

#align_import data.set.opposite from "leanprover-community/mathlib"@"fc2ed6f838ce7c9b7c7171e58d78eaf7b438fb0e"

/-!
# The opposite of a set

The opposite of a set `s` is simply the set obtained by taking the opposite of each member of `s`.
-/

variable {α : Type*}

open Opposite

namespace Set

/-- The opposite of a set `s` is the set obtained by taking the opposite of each member of `s`. -/
protected def op (s : Set α) : Set αᵒᵖ :=
  unop ⁻¹' s
#align set.op Set.op

/-- The unop of a set `s` is the set obtained by taking the unop of each member of `s`. -/
protected def unop (s : Set αᵒᵖ) : Set α :=
  op ⁻¹' s
#align set.unop Set.unop

@[simp]
theorem mem_op {s : Set α} {a : αᵒᵖ} : a ∈ s.op ↔ unop a ∈ s :=
  Iff.rfl
#align set.mem_op Set.mem_op

@[simp 1100]
theorem op_mem_op {s : Set α} {a : α} : op a ∈ s.op ↔ a ∈ s := by rfl
                                                                  -- 🎉 no goals
#align set.op_mem_op Set.op_mem_op

@[simp]
theorem mem_unop {s : Set αᵒᵖ} {a : α} : a ∈ s.unop ↔ op a ∈ s :=
  Iff.rfl
#align set.mem_unop Set.mem_unop

@[simp 1100]
theorem unop_mem_unop {s : Set αᵒᵖ} {a : αᵒᵖ} : unop a ∈ s.unop ↔ a ∈ s := by rfl
                                                                              -- 🎉 no goals
#align set.unop_mem_unop Set.unop_mem_unop

@[simp]
theorem op_unop (s : Set α) : s.op.unop = s := rfl
#align set.op_unop Set.op_unop

@[simp]
theorem unop_op (s : Set αᵒᵖ) : s.unop.op = s := rfl
#align set.unop_op Set.unop_op

/-- The members of the opposite of a set are in bijection with the members of the set itself. -/
@[simps]
def opEquiv_self (s : Set α) : s.op ≃ s :=
  ⟨fun x ↦ ⟨unop x, x.2⟩, fun x ↦ ⟨op x, x.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
#align set.op_equiv_self Set.opEquiv_self
#align set.op_equiv_self_apply_coe Set.opEquiv_self_apply_coe
#align set.op_equiv_self_symm_apply_coe Set.opEquiv_self_symm_apply_coe

/-- Taking opposites as an equivalence of powersets. -/
@[simps]
def opEquiv : Set α ≃ Set αᵒᵖ :=
  ⟨Set.op, Set.unop, op_unop, unop_op⟩
#align set.op_equiv Set.opEquiv
#align set.op_equiv_symm_apply Set.opEquiv_symm_apply
#align set.op_equiv_apply Set.opEquiv_apply

@[simp]
theorem singleton_op (x : α) : ({x} : Set α).op = {op x} := by
  ext
  -- ⊢ x✝ ∈ Set.op {x} ↔ x✝ ∈ {op x}
  constructor
  -- ⊢ x✝ ∈ Set.op {x} → x✝ ∈ {op x}
  · apply unop_injective
    -- 🎉 no goals
  · apply op_injective
    -- 🎉 no goals
#align set.singleton_op Set.singleton_op

@[simp]
theorem singleton_unop (x : αᵒᵖ) : ({x} : Set αᵒᵖ).unop = {unop x} := by
  ext
  -- ⊢ x✝ ∈ Set.unop {x} ↔ x✝ ∈ {x.unop}
  constructor
  -- ⊢ x✝ ∈ Set.unop {x} → x✝ ∈ {x.unop}
  · apply op_injective
    -- 🎉 no goals
  · apply unop_injective
    -- 🎉 no goals
#align set.singleton_unop Set.singleton_unop

@[simp 1100]
theorem singleton_op_unop (x : α) : ({op x} : Set αᵒᵖ).unop = {x} := by
  ext
  -- ⊢ x✝ ∈ Set.unop {op x} ↔ x✝ ∈ {x}
  constructor
  -- ⊢ x✝ ∈ Set.unop {op x} → x✝ ∈ {x}
  · apply op_injective
    -- 🎉 no goals
  · apply unop_injective
    -- 🎉 no goals
#align set.singleton_op_unop Set.singleton_op_unop

@[simp 1100]
theorem singleton_unop_op (x : αᵒᵖ) : ({unop x} : Set α).op = {x} := by
  ext
  -- ⊢ x✝ ∈ Set.op {x.unop} ↔ x✝ ∈ {x}
  constructor
  -- ⊢ x✝ ∈ Set.op {x.unop} → x✝ ∈ {x}
  · apply unop_injective
    -- 🎉 no goals
  · apply op_injective
    -- 🎉 no goals
#align set.singleton_unop_op Set.singleton_unop_op

end Set
