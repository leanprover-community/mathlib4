/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Equiv.Set

/-!
# Update a function on a set of values

This file defines `Function.updateFinset`, the operation that updates a function on a
(finite) set of values.

This is a very specific function used for `MeasureTheory.marginal`, and possibly not that useful
for other purposes.
-/

open Finset

variable {ι : Sort _} {π : ι → Sort _} {x : ∀ i, π i} [DecidableEq ι]
variable {α : Type*} [DecidableEq α] {s t : Finset α}

namespace Equiv.Finset

/-- The disjoint union of finsets is a sum -/
def union (s t : Finset α) (h : Disjoint s t) : s ⊕ t ≃ (s ∪ t : Finset α) :=
  Equiv.Set.ofEq (coe_union _ _) |>.trans (Equiv.Set.union (disjoint_coe.mpr h).le_bot) |>.symm

@[simp] lemma union_symm_inl (h : Disjoint s t) (x : s) :
    Finset.union s t h (Sum.inl x) = ⟨x, Finset.mem_union.mpr <| Or.inl x.2⟩ := rfl

@[simp] lemma union_symm_inr (h : Disjoint s t) (y : t) :
    Finset.union s t h (Sum.inr y) = ⟨y, Finset.mem_union.mpr <| Or.inr y.2⟩ := rfl

end Finset

/-- The type of dependent functions on the disjoint union of finsets `s ∪ t` is equivalent to the
type of pairs of functions on `s` and on `t`. This is similar to `Equiv.sumPiEquivProdPi`. -/
def piFinsetUnion {ι} [DecidableEq ι] (α : ι → Type*) {s t : Finset ι} (h : Disjoint s t) :
    ((∀ i : s, α i) × ∀ i : t, α i) ≃ ∀ i : (s ∪ t : Finset ι), α i :=
  let e := Equiv.Finset.union s t h
  sumPiEquivProdPi (fun b ↦ α (e b)) |>.symm.trans (.piCongrLeft (fun i : ↥(s ∪ t) ↦ α i) e)

end Equiv

namespace Function

/-- `updateFinset x s y` is the vector `x` with the coordinates in `s` changed to the values of `y`.
-/
def updateFinset (x : ∀ i, π i) (s : Finset ι) (y : ∀ i : ↥s, π i) (i : ι) : π i :=
  if hi : i ∈ s then y ⟨i, hi⟩ else x i

open Finset Equiv

theorem updateFinset_def {s : Finset ι} {y} :
    updateFinset x s y = fun i ↦ if hi : i ∈ s then y ⟨i, hi⟩ else x i :=
  rfl

@[simp] theorem updateFinset_empty {y} : updateFinset x ∅ y = x :=
  rfl

theorem updateFinset_singleton {i y} :
    updateFinset x {i} y = Function.update x i (y ⟨i, mem_singleton_self i⟩) := by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_same, updateFinset]
  · simp [hj, updateFinset]

theorem update_eq_updateFinset {i y} :
    Function.update x i y = updateFinset x {i} (uniqueElim y) := by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_same, updateFinset]
    exact uniqueElim_default (α := fun j : ({i} : Finset ι) => π j) y
  · simp [hj, updateFinset]

theorem updateFinset_updateFinset {s t : Finset ι} (hst : Disjoint s t)
    {y : ∀ i : ↥s, π i} {z : ∀ i : ↥t, π i} :
    updateFinset (updateFinset x s y) t z =
    updateFinset x (s ∪ t) (Equiv.piFinsetUnion π hst ⟨y, z⟩) := by
  set e := Equiv.Finset.union s t hst
  congr with i
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;>
    simp only [updateFinset, his, hit, dif_pos, dif_neg, Finset.mem_union, true_or_iff,
      false_or_iff, not_false_iff]
  · exfalso; exact Finset.disjoint_left.mp hst his hit
  · exact piCongrLeft_sum_inl (fun b : ↥(s ∪ t) => π b) e y z ⟨i, his⟩ |>.symm
  · exact piCongrLeft_sum_inr (fun b : ↥(s ∪ t) => π b) e y z ⟨i, hit⟩ |>.symm

end Function
