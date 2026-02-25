/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Data.Finset.Pi
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Logic.Function.DependsOn

/-!
# Update a function on a set of values

This file defines `Function.updateFinset`, the operation that updates a function on a
(finite) set of values.

This is a very specific function used for `MeasureTheory.marginal`, and possibly not that useful
for other purposes.
-/

@[expose] public section
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

set_option backward.isDefEq.respectTransparency false in
/-- If one replaces the variables indexed by a finite set `t`, then `f` no longer depends on
those variables. -/
theorem _root_.DependsOn.updateFinset {α : Type*} {f : (Π i, π i) → α} {s : Set ι}
    (hf : DependsOn f s) {t : Finset ι} (y : Π i : t, π i) :
    DependsOn (fun x ↦ f (updateFinset x t y)) (s \ t) := by
  refine fun x₁ x₂ h ↦ hf (fun i hi ↦ ?_)
  simp only [Function.updateFinset]
  split_ifs; · rfl
  simp_all

/-- If one replaces the variable indexed by `i`, then `f` no longer depends on
this variable. -/
theorem _root_.DependsOn.update {α : Type*} {f : (Π i, π i) → α} {s : Finset ι} (hf : DependsOn f s)
    (i : ι) (y : π i) : DependsOn (fun x ↦ f (Function.update x i y)) (s.erase i) := by
  simp_rw [Function.update_eq_updateFinset, erase_eq, coe_sdiff]
  exact hf.updateFinset _

theorem updateFinset_updateFinset (hst : Disjoint s t) :
    updateFinset (updateFinset x s y) t z =
    updateFinset x (s ∪ t) (Equiv.piFinsetUnion π hst ⟨y, z⟩) := by
  set e := Equiv.Finset.union s t hst
  ext i
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;>
    simp only [updateFinset, his, hit, dif_pos, dif_neg, Finset.mem_union, false_or, not_false_iff]
  · exfalso; exact Finset.disjoint_left.mp hst his hit
  · exact piCongrLeft_sumInl (fun b : ↥(s ∪ t) => π b) e y z ⟨i, his⟩ |>.symm
  · exact piCongrLeft_sumInr (fun b : ↥(s ∪ t) => π b) e y z ⟨i, hit⟩ |>.symm

lemma updateFinset_updateFinset_of_subset {s t : Finset ι} (hst : s ⊆ t)
    (x : Π i, π i) (y : Π i : s, π i) (z : Π i : t, π i) :
    updateFinset (updateFinset x s y) t z = updateFinset x t z := by
  ext i
  simp only [updateFinset]
  split_ifs with h1 h2 <;> try rfl
  exact (h1 (hst h2)).elim

lemma restrict_updateFinset_of_subset {s t : Finset ι} (hst : s ⊆ t) (x : Π i, π i)
    (y : Π i : t, π i) : s.restrict (updateFinset x t y) = restrict₂ hst y := by
  ext i
  simp [updateFinset, dif_pos (hst i.2)]

lemma restrict_updateFinset {s : Finset ι} (x : Π i, π i) (y : Π i : s, π i) :
    s.restrict (updateFinset x s y) = y := by
  rw [restrict_updateFinset_of_subset subset_rfl]
  rfl

@[simp]
lemma updateFinset_restrict {s : Finset ι} (x : Π i, π i) :
    updateFinset x s (s.restrict x) = x := by
  ext i
  simp [updateFinset]

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

theorem updateFinset_univ_apply [Fintype ι] {y : ∀ i : Finset.univ, π i} {i : ι} :
    updateFinset x .univ y i = y ⟨i, Finset.mem_univ i⟩ := by
  simp [updateFinset_def]

end Function
