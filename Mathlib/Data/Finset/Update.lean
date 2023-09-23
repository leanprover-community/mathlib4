/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Data.Finset.Basic

/-!
# Update a function on a set of values

This file defines `Function.updateFinset`, the operation that updates a function on a
(finite) set of values.
-/
variable {ι : Sort _} {π : ι → Sort _} {x : ∀ i, π i}

namespace Function

/-- `updateFinset x s y` is the vector `x` with the coordinates in `s` changed to the values of `y`.

We should generalize `updateFinset` to `SetLike` instead of restricting to `Finset`.
However, at the moment `Finset` is not `SetLike`, so we cannot do this yet.
-/
def updateFinset (x : ∀ i, π i) (s : Finset ι) [DecidablePred (· ∈ s)]
    (y : ∀ i : ↥s, π i) (i : ι) : π i :=
  if hi : i ∈ s then y ⟨i, hi⟩ else x i

open Finset Equiv

theorem updateFinset_empty [DecidableEq ι] {y} : updateFinset x ∅ y = x :=
  rfl

theorem updateFinset_singleton [DecidableEq ι] {i y} :
    updateFinset x {i} y = Function.update x i (y ⟨i, mem_singleton_self i⟩) := by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_same, updateFinset]
  · simp [hj, updateFinset]

theorem update_eq_updateFinset [DecidableEq ι] {i y} :
    Function.update x i y = updateFinset x {i} (uniqueElim y) := by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_same, updateFinset]
    exact uniqueElim_default (α := fun j : ({i} : Finset ι) => π j) y
  · simp [hj, updateFinset]

theorem updateFinset_updateFinset [DecidableEq ι] {s t : Finset ι} (hst : Disjoint s t)
    {y : ∀ i : ↥s, π i} {z : ∀ i : ↥t, π i} :
    updateFinset (updateFinset x s y) t z =
    updateFinset x (s ∪ t) (Equiv.piFinsetUnion π hst ⟨y, z⟩) := by
  set e₁ := finsetUnionEquivSum s t hst |>.symm
  congr with i
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;>
    simp only [updateFinset, his, hit, dif_pos, dif_neg, Finset.mem_union, true_or_iff, false_or_iff,
      not_false_iff]
  · exfalso; exact Finset.disjoint_left.mp hst his hit
  · exact piCongrLeft_sum_inl (fun b : ↥(s ∪ t) => π b) e₁ y z ⟨i, his⟩ |>.symm
  · exact piCongrLeft_sum_inr (fun b : ↥(s ∪ t) => π b) e₁ y z ⟨i, _⟩ |>.symm

end Function
