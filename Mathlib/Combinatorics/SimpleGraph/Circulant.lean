/-
Copyright (c) 2024 Iván Renison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Combinatorics.SimpleGraph.Cycle

/-!
# Definition of circulant graphs

This file defines and proves several fact about circulant graphs.
A circulant graph over type `G` with jumps `s : Set G` is a graph in which two vertices `u` and `v`
are adjacent if and only if `u - v ∈ s` or `v - u ∈ s`. The elements of `s` are called jumps.

## Main declarations

* `SimpleGraph.circulantGraph s`: the circulant graph over `G` with jumps `s`.
-/

@[expose] public section

namespace SimpleGraph

/-- Circulant graph over additive group `G` with jumps `s` -/
@[simps!]
def circulantGraph {G : Type*} [AddGroup G] (s : Set G) : SimpleGraph G :=
  fromRel (· - · ∈ s)

variable {G : Type*} [AddGroup G] (s : Set G)

theorem circulantGraph_eq_erase_zero : circulantGraph s = circulantGraph (s \ {0}) := by
  ext (u v : G)
  simp only [circulantGraph, fromRel_adj, and_congr_right_iff]
  intro (h : u ≠ v)
  apply Iff.intro
  · intro h1
    cases h1 with
      | inl h1 => exact Or.inl ⟨h1, sub_ne_zero_of_ne h⟩
      | inr h1 => exact Or.inr ⟨h1, sub_ne_zero_of_ne h.symm⟩
  · intro h1
    cases h1 with
      | inl h1 => exact Or.inl h1.left
      | inr h1 => exact Or.inr h1.left

theorem circulantGraph_eq_symm : circulantGraph s = circulantGraph (s ∪ (-s)) := by
  ext
  simp only [circulantGraph_adj, Set.mem_union, Set.mem_neg, neg_sub]
  grind

instance [DecidableEq G] [DecidablePred (· ∈ s)] : DecidableRel (circulantGraph s).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem circulantGraph_adj_translate {s : Set G} {u v d : G} :
    (circulantGraph s).Adj (u + d) (v + d) ↔ (circulantGraph s).Adj u v := by simp

theorem cycleGraph_eq_circulantGraph (n : ℕ) : cycleGraph (n + 1) = circulantGraph {1} := by
  cases n
  · exact edgeFinset_inj.mp rfl
  · aesop

end SimpleGraph
