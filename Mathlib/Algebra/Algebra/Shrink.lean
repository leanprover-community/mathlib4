/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Algebra.TransferInstance
import Mathlib.Algebra.Ring.Shrink

/-!
# Transfer module and algebra structures from `α` to `Shrink α`
-/

noncomputable section

universe v
variable {R α : Type*} [Small.{v} α] [CommSemiring R]

namespace Shrink

instance [Semiring α] [Algebra R α] : Algebra R (Shrink.{v} α) := (equivShrink α).symm.algebra _

variable (R α) in
/-- Shrinking `α` to a smaller universe preserves algebra structure. -/
@[simps!]
def algEquiv [Small.{v} α] [Semiring α] [Algebra R α] : Shrink.{v} α ≃ₐ[R] α :=
  (equivShrink α).symm.algEquiv _

end Shrink

/-- A small algebra is algebra equivalent to its small model. -/
@[deprecated Shrink.algEquiv (since := "2025-07-11")]
def algEquivShrink (α β) [CommSemiring α] [Semiring β] [Algebra α β] [Small β] :
    β ≃ₐ[α] Shrink β :=
  ((equivShrink β).symm.algEquiv α).symm
