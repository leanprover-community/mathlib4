/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.Sign.Defs

@[expose] public section

/-!
# Order theorems

This file collects miscellaneous theorems on the order structure of `SignType`.
-/

variable {α ι : Type*}

namespace SignType

noncomputable instance : CompleteLinearOrder SignType := Fintype.toCompleteLinearOrder _

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

theorem sign_sum {s : Finset ι} {f : ι → α} (hs : s.Nonempty) (t : SignType)
    (h : ∀ i ∈ s, sign (f i) = t) : sign (∑ i ∈ s, f i) = t := by
  cases t
  · simp_rw [zero_eq_zero, sign_eq_zero_iff] at h ⊢
    exact Finset.sum_eq_zero h
  · simp_rw [neg_eq_neg_one, sign_eq_neg_one_iff] at h ⊢
    exact Finset.sum_neg h hs
  · simp_rw [pos_eq_one, sign_eq_one_iff] at h ⊢
    exact Finset.sum_pos h hs

end SignType
