/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.Algebra.Group.Shrink

/-!
# Transfer module and algebra structures from `α` to `Shrink α`
-/

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
