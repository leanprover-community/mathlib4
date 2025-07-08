/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Order.PartialSups
import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# `PartialSups` in a `SuccAddOrder`
-/

open Finset

variable {α ι : Type*} [SemilatticeSup α]

@[simp]
lemma partialSups_add_one [Add ι] [One ι] [LinearOrder ι] [LocallyFiniteOrderBot ι] [SuccAddOrder ι]
    (f : ι → α) (i : ι) : partialSups f (i + 1) = partialSups f i ⊔ f (i + 1) :=
  Order.succ_eq_add_one i ▸ partialSups_succ f i

/-- See also `partialSups_succ` for an alternative decomposition of
`(partialSups f) (Order.succ i)`. -/
lemma partialSups_succ' {α : Type*} [SemilatticeSup α] [LinearOrder ι] [LocallyFiniteOrder ι]
    [SuccOrder ι] [OrderBot ι] (f : ι → α) (i : ι) :
    (partialSups f) (Order.succ i) = f ⊥ ⊔ (partialSups (f ∘ Order.succ)) i := by
  refine Succ.rec (by simp) (fun j _ h ↦ ?_) (bot_le (a := i))
  have : (partialSups (f ∘ Order.succ)) (Order.succ j) =
      ((partialSups (f ∘ Order.succ)) j ⊔ (f ∘ Order.succ) (Order.succ j)) := by simp
  simp [this, h, sup_assoc]

lemma partialSups_const_add {α : Type*} [Preorder ι] [LocallyFiniteOrderBot ι] [Lattice α]
    [AddGroup α] [CovariantClass α α (· + ·) (· ≤ ·)] (f : ι → α) (c : α) (i : ι) :
    partialSups (c + f ·) i = c + partialSups f i := by
  change (partialSups (OrderIso.addLeft c ∘ f)) i = _
  rw [comp_partialSups f (OrderIso.addLeft c)]; rfl

/-- See also `partialSups_add_one` for an alternative decomposition of
`partialSups f (i + 1)`. -/
lemma partialSups_add_one' [Add ι] [One ι] [LinearOrder ι] [OrderBot ι] [LocallyFiniteOrder ι]
    [SuccAddOrder ι] (f : ι → α)  (i : ι) :
    partialSups f (i + 1) = f ⊥ ⊔ partialSups (f ∘ (fun k ↦ k + 1)) i := by
  simpa [← Order.succ_eq_add_one] using partialSups_succ' f i
