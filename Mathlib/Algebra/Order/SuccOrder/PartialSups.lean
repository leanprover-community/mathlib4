/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Lua Viana Reis
-/
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Order.PartialSups
import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# `PartialSups` in a `SuccOrder`

For related results, see also:

- `Mathlib/Order/PartialSups.lean`
- `Mathlib/Algebra/Order/PartialSups.lean`
- `Mathlib/Algebra/Order/AddGroup/PartialSups.lean`

-/

variable {α ι : Type*} [SemilatticeSup α]

/-- See `partialSups_succ` for another decomposition of `(partialSups f) (Order.succ i)`. -/
lemma partialSups_succ' {α : Type*} [SemilatticeSup α] [LinearOrder ι] [LocallyFiniteOrder ι]
    [SuccOrder ι] [OrderBot ι] (f : ι → α) (i : ι) :
    (partialSups f) (Order.succ i) = f ⊥ ⊔ (partialSups (f ∘ Order.succ)) i := by
  refine Succ.rec (by simp) (fun j _ h ↦ ?_) (bot_le (a := i))
  have : (partialSups (f ∘ Order.succ)) (Order.succ j) =
      ((partialSups (f ∘ Order.succ)) j ⊔ (f ∘ Order.succ) (Order.succ j)) := by simp
  simp [this, h, sup_assoc]

/-- See `partialSups_add_one` for another decomposition of `partialSups f (i + 1)`. -/
lemma partialSups_add_one' [Add ι] [One ι] [LinearOrder ι] [OrderBot ι] [LocallyFiniteOrder ι]
    [SuccAddOrder ι] (f : ι → α)  (i : ι) :
    partialSups f (i + 1) = f ⊥ ⊔ partialSups (f ∘ (fun k ↦ k + 1)) i := by
  simpa [← Order.succ_eq_add_one] using partialSups_succ' f i
