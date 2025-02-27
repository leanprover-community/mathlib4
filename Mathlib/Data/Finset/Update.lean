/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Defs

/-!
# Update a function on a set of values

This file defines `Function.updateFinset`, the operation that updates a function on a
(finite) set of values.

This is a very specific function used for `MeasureTheory.marginal`, and possibly not that useful
for other purposes.
-/
variable {ι : Sort _} {π : ι → Sort _} {x : ∀ i, π i} [DecidableEq ι]
  {s t : Finset ι} {y : ∀ i : s, π i} {z : ∀ i : t, π i} {i : ι}

namespace Function

/-- `updateFinset x s y` is the vector `x` with the coordinates in `s` changed to the values of `y`.
-/
def updateFinset (x : ∀ i, π i) (s : Finset ι) (y : ∀ i : ↥s, π i) (i : ι) : π i :=
  if hi : i ∈ s then y ⟨i, hi⟩ else x i

open Finset Equiv

theorem updateFinset_def :
    updateFinset x s y = fun i ↦ if hi : i ∈ s then y ⟨i, hi⟩ else x i :=
  rfl

@[simp] theorem updateFinset_empty {y} : updateFinset x ∅ y = x :=
  rfl

theorem updateFinset_singleton {y} :
    updateFinset x {i} y = Function.update x i (y ⟨i, mem_singleton_self i⟩) := by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_self, updateFinset]
  · simp [hj, updateFinset]

theorem update_eq_updateFinset {y} :
    Function.update x i y = updateFinset x {i} (uniqueElim y) := by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_self, updateFinset]
    exact uniqueElim_default (α := fun j : ({i} : Finset ι) => π j) y
  · simp [hj, updateFinset]

theorem updateFinset_updateFinset (hst : Disjoint s t) :
    updateFinset (updateFinset x s y) t z =
    updateFinset x (s ∪ t) (Equiv.piFinsetUnion π hst ⟨y, z⟩) := by
  set e := Equiv.Finset.union s t hst
  congr with i
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;>
    simp only [updateFinset, his, hit, dif_pos, dif_neg, Finset.mem_union, false_or, not_false_iff]
  · exfalso; exact Finset.disjoint_left.mp hst his hit
  · exact piCongrLeft_sumInl (fun b : ↥(s ∪ t) => π b) e y z ⟨i, his⟩ |>.symm
  · exact piCongrLeft_sumInr (fun b : ↥(s ∪ t) => π b) e y z ⟨i, hit⟩ |>.symm

-- this would be slightly nicer if we had a version of `Equiv.piFinsetUnion` for `insert`.
theorem update_updateFinset {z} (hi : i ∉ s) :
    Function.update (updateFinset x s y) i z = updateFinset x (s ∪ {i})
      ((Equiv.piFinsetUnion π <| Finset.disjoint_singleton_right.mpr hi) (y, uniqueElim z)) := by
  rw [update_eq_updateFinset, updateFinset_updateFinset]

theorem updateFinset_congr (h : s = t) :
    updateFinset x s y = updateFinset x t (fun i ↦ y ⟨i, h ▸ i.prop⟩) := by
  subst h; rfl

theorem updateFinset_univ [Fintype ι] {y : ∀ i : Finset.univ, π i} :
    updateFinset x .univ y = fun i : ι ↦ y ⟨i, Finset.mem_univ i⟩ := by
  simp [updateFinset_def]

end Function
