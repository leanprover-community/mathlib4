/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.Order.Interval.Finset.Gaps
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Sum of gaps

This file proves that given a function `g` on `[a, b]`, `g b - g a` can be splitted according to a
given finite collection of pairwise disjoint closed subintervals of `[a, b]`. It is the sum two
terms:
- the sum of `g y - g x` for `[x, y]` in the collection,
- the sum of `g y - g x` for `[x, y]` in the complement (modulo endpoints) of the union of the
collection in `[a, b]`.

We use `Finset.intervalGapsWithin` to encode the complement.

Technically, we don't require pairwise disjointness or endpoints to be within `[a, b]` or even
require that `a ≤ b`, but it makes the most sense if they are actually satisfied.
-/

@[expose] public section

open Set

variable {α : Type*} [LinearOrder α] [AddCommGroup α] (F : Finset (α × α)) (a b : α) {i : ℕ}

theorem Finset.sum_intervalGapsWithin_add_sum_eq_sub (F : Finset (α × α)) {a b : α} (g : α → α) :
    ∑ i ∈ Finset.range (F.card + 1),
      (g (F.intervalGapsWithin a b i).2 - g (F.intervalGapsWithin a b i).1) +
    ∑ z ∈ F, (g z.2 - g z.1) = g b - g a := by
  let p := F.intervalGapsWithin a b
  have := Finset.sum_bij (s := Finset.range F.card) (t := F) (g := fun z ↦ g z.2 - g z.1)
    (f := fun i ↦ (g (p (i + 1)).1 - g (p i).2))
    (fun i hi ↦ ((p i).2, (p (i + 1)).1))
    (fun i hi ↦ F.intervalGapsWithin_mapsTo a b (x := i) (by grind))
    (fun i hi j hj hij ↦ F.intervalGapsWithin_injOn a b (by grind) (by grind) hij)
    (fun z hz ↦ by
      obtain ⟨i, hi₁, hi₂⟩ := F.intervalGapsWithin_surjOn a b hz
      exact ⟨i, by grind, hi₂⟩)
    (by simp)
  rw [← this, add_comm, Finset.sum_range_succ, ← add_assoc,
      ← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun _ _ ↦ sub_add_sub_cancel _ _ _),
      Finset.sum_range_sub (fun i ↦ g (F.intervalGapsWithin a b i).1)]
  simp

theorem Finset.sum_intervalGapsWithin_eq_sub_sub_sum (F : Finset (α × α)) {a b : α} (g : α → α) :
    ∑ i ∈ Finset.range (F.card + 1),
      (g (F.intervalGapsWithin a b i).2 - g (F.intervalGapsWithin a b i).1) =
    g b - g a - ∑ z ∈ F, (g z.2 - g z.1) :=
  eq_sub_iff_add_eq.mpr (F.sum_intervalGapsWithin_add_sum_eq_sub g)
