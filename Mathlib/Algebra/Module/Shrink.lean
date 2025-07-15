/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.Module.TransferInstance

/-!
# Transfer module and algebra structures from `α` to `Shrink α`
-/

-- FIXME: `to_additive` is incompatible with `noncomputable section`.
-- See https://github.com/leanprover-community/mathlib4/issues/1074.
suppress_compilation

universe v
variable {R α : Type*} [Small.{v} α] [Semiring R] [AddCommMonoid α] [Module R α]

namespace Shrink

instance : Module R (Shrink.{v} α) := (equivShrink α).symm.module R

variable (R α) in
/-- Shrinking `α` to a smaller universe preserves module structure. -/
@[simps!]
def linearEquiv : Shrink.{v} α ≃ₗ[R] α := (equivShrink α).symm.linearEquiv _

end Shrink

/-- A small module is linearly equivalent to its small model. -/
@[deprecated Shrink.linearEquiv (since := "2025-07-11")]
def linearEquivShrink (α β) [Semiring α] [AddCommMonoid β] [Module α β] [Small β] :
    β ≃ₗ[α] Shrink β :=
  ((equivShrink β).symm.linearEquiv α).symm
