/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.Algebra.Ring.Shrink

/-!
# Transfer module and algebra structures from `α` to `Shrink α`
-/

suppress_compilation

universe v
variable {R α : Type*} [Small.{v} α] [CommSemiring R]

namespace Shrink

instance [Semiring α] [Algebra R α] : Algebra R (Shrink.{v} α) := (equivShrink α).symm.algebra _

variable (R α) in
/-- Shrink `α` to a smaller universe preserves algebra structure. -/
@[simps!]
def _root_.Shrink.algEquiv [Small.{v} α] [Semiring α] [Algebra R α] : Shrink.{v} α ≃ₐ[R] α :=
  (equivShrink α).symm.algEquiv _

end Shrink
