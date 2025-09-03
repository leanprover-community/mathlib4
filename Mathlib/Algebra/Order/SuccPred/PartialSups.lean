/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Oliver Butterley, Lua Viana Reis
-/
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Order.PartialSups
import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# `PartialSups` in a `SuccAddOrder`

Basic results concerning `PartialSups` which follow with minimal assumptions beyond the fact that
the `PartialSup` is defined over a `SuccAddOrder`.
-/

open Finset

variable {α ι : Type*} [SemilatticeSup α] [LinearOrder ι]

@[simp]
lemma partialSups_add_one [Add ι] [One ι] [LocallyFiniteOrderBot ι] [SuccAddOrder ι]
    (f : ι → α) (i : ι) : partialSups f (i + 1) = partialSups f i ⊔ f (i + 1) :=
  Order.succ_eq_add_one i ▸ partialSups_succ f i

/-- See `partialSups_succ` for another decomposition of `(partialSups f) (Order.succ i)`. -/
lemma partialSups_succ' {α : Type*} [SemilatticeSup α] [LocallyFiniteOrder ι]
    [SuccOrder ι] [OrderBot ι] (f : ι → α) (i : ι) :
    (partialSups f) (Order.succ i) = f ⊥ ⊔ (partialSups (f ∘ Order.succ)) i := by
  refine Succ.rec (by simp) (fun j _ h ↦ ?_) (bot_le (a := i))
  have : (partialSups (f ∘ Order.succ)) (Order.succ j) =
      ((partialSups (f ∘ Order.succ)) j ⊔ (f ∘ Order.succ) (Order.succ j)) := by simp
  simp [this, h, sup_assoc]

/-- See `partialSups_add_one` for another decomposition of `partialSups f (i + 1)`. -/
lemma partialSups_add_one' [Add ι] [One ι] [OrderBot ι] [LocallyFiniteOrder ι]
    [SuccAddOrder ι] (f : ι → α) (i : ι) :
    partialSups f (i + 1) = f ⊥ ⊔ partialSups (f ∘ (fun k ↦ k + 1)) i := by
  simpa [← Order.succ_eq_add_one] using partialSups_succ' f i
