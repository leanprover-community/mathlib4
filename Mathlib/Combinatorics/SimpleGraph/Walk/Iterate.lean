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

public section

open Function

namespace SimpleGraph

namespace Walk

variable {α : Type*} {G : SimpleGraph α}

/-- Build a walk of length `n` from `v` to `f^[n] v` following `f`,
given that each step is adjacent in `G`. -/
def iterate (f : V → V) (hadj : ∀ v, G.Adj v (f v)) (v : α) (n : ℕ) : G.Walk v (f^[n] v) :=
  (Walk.ofSupport _ (by simp) <| .iterate v hadj <| n + 1).copy rfl <|
    List.getLast_iterate f v (n + 1) <| by simp

/-- The walk built by `Walk.iterate` has length `n`. -/
@[simp]
theorem length_iterate (f : V → V) (hadj : ∀ v, G.Adj v (f v)) (v : V) (n : ℕ) :
    (iterate f hadj v n).length = n := by
  simp [iterate, -List.iterate]

/-- The support of `Walk.iterate` is `[v, f v, f^[2] v, ..., f^[n] v]`. -/
@[simp]
theorem support_iterate (f : V → V) (hadj : ∀ v, G.Adj v (f v)) (v : V) (n : ℕ) :
    (iterate f hadj v n).support = List.iterate f v (n + 1) := by
  simp [iterate, -List.iterate]

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
