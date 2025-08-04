/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/

import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.InformationTheory.Hamming.Group

/-! ### The `Module` instance on Hamming types -/

namespace DHamming

variable {α ι : Type*} {β γ : ι → Type*} {f : ∀ i, β i → γ i} {x y : DHamming β}

instance [Monoid α] [∀ i, AddCommMonoid (β i)] [∀ i, DistribMulAction α (β i)] :
    DistribMulAction α (DHamming β) := toPiEquiv.distribMulAction _

instance [∀ i, AddCommMonoid (β i)] [Semiring α] [∀ i, Module α (β i)] :
    Module α (DHamming β) := toPiEquiv.module _

/-- `Hamming.toPiEquiv` as a `LinearEquiv`. -/
def ofLinearEquiv (α) [Semiring α] [∀ i, AddCommMonoid (β i)] [∀ i, Module α (β i)] :
  DHamming β ≃ₗ[α] ∀ i, β i := toPiEquiv.linearEquiv α

end DHamming
