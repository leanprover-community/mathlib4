/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Data.List.Iterate

/-!
# Walks from iterated functions

Given a function `f : α → α` such that `G.Adj x (f x)` for all `x`,
we construct a walk of length `n` from `x` to `f^[n] x`.
-/

@[expose] public section

open Function

namespace SimpleGraph

namespace Walk

variable {α : Type*} {G : SimpleGraph α}

/-- The list `List.iterate f x (n + 1)` is a chain under `G.Adj` when every step is adjacent. -/
theorem isChain_adj_iterate (f : α → α) (hadj : ∀ x, G.Adj x (f x)) (x : α) (n : ℕ) :
    (List.iterate f x (n + 1)).IsChain G.Adj := by
  simp only [List.isChain_iff_getElem, List.getElem_iterate, iterate_succ']
  exact fun _ _ => hadj _

/-- The last element of `List.iterate f x (n + 1)` is `f^[n] x`. -/
theorem getLast_iterate (f : α → α) (x : α) (n : ℕ)
    (h : List.iterate f x (n + 1) ≠ []) :
    (List.iterate f x (n + 1)).getLast h = f^[n] x := by
  rw [List.getLast_eq_getElem, List.getElem_iterate]
  simp [List.length_iterate]

/-- Build a walk of length `n` from `x` to `f^[n] x` following `f`,
given that each step is adjacent in `G`. -/
def iterate (f : α → α) (hadj : ∀ x, G.Adj x (f x)) (x : α) (n : ℕ) : G.Walk x (f^[n] x) :=
  (Walk.ofSupport _ (by simp) (isChain_adj_iterate f hadj x n)).copy rfl
    (getLast_iterate f x n (by simp))

/-- The walk built by `Walk.iterate` has length `n`. -/
@[simp]
theorem length_iterate (f : α → α) (hadj : ∀ x, G.Adj x (f x)) (x : α) (n : ℕ) :
    (iterate f hadj x n).length = n := by
  simp only [iterate, length_copy, length_ofSupport, List.length_iterate, Nat.add_sub_cancel]

/-- The support of `Walk.iterate` is `[x, f x, f^[2] x, ..., f^[n] x]`. -/
@[simp]
theorem support_iterate (f : α → α) (hadj : ∀ x, G.Adj x (f x)) (x : α) (n : ℕ) :
    (iterate f hadj x n).support = List.iterate f x (n + 1) := by
  simp only [iterate, support_copy, support_ofSupport]

/-- The edges of `Walk.iterate` are `s(f^[i] x, f^[i+1] x)` for `i < n`. -/
theorem edges_iterate (f : α → α) (hadj : ∀ x, G.Adj x (f x)) (x : α) (n : ℕ) :
    (iterate f hadj x n).edges = (List.range n).map fun i ↦ s(f^[i] x, f^[i + 1] x) := by
  simp only [edges_eq_zipWith_support, support_iterate]
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    simp only [List.iterate, List.zipWith, List.tail_cons, List.range_succ_eq_map,
      List.map_cons, iterate_zero, id_eq, List.map_map]
    congr 1
    convert ih (f x) using 1

end Walk

end SimpleGraph
