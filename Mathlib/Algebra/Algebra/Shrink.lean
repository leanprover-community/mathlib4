/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Ring.Shrink
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Transfer module and algebra structures from `α` to `Shrink α`
-/

@[expose] public section

noncomputable section

universe v
variable {R α : Type*} [Small.{v} α] [CommSemiring R]

namespace Shrink

instance [Semiring α] [Algebra R α] : Algebra R (Shrink.{v} α) := (equivShrink α).symm.algebra _

variable (R α) in
/-- Shrinking `α` to a smaller universe preserves algebra structure. -/
@[simps!]
def algEquiv [Semiring α] [Algebra R α] : Shrink.{v} α ≃ₐ[R] α :=
  (equivShrink α).symm.algEquiv _

end Shrink
