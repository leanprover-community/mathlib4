/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Order.PartialSups

/-!
# `PartialSups` in a `SuccAddOrder`
-/

open Finset

variable {α ι : Type*} [SemilatticeSup α]

@[simp]
lemma partialSups_add_one [Add ι] [One ι] [LinearOrder ι] [LocallyFiniteOrderBot ι] [SuccAddOrder ι]
    (f : ι → α) (i : ι) : partialSups f (i + 1) = partialSups f i ⊔ f (i + 1) :=
  Order.succ_eq_add_one i ▸ partialSups_succ f i
