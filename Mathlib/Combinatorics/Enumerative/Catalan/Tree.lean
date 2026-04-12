/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Central

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Field


/-!
## Main results
* `treesOfNumNodesEq_card_eq_catalan`: The number of binary trees with `n` internal nodes
  is `catalan n`

-/

@[expose] public section

open Finset

open Finset.antidiagonal (fst_le snd_le)

namespace Tree

/-- Given two finsets, find all trees that can be formed with
  left child in `a` and right child in `b` -/
abbrev pairwiseNode (a b : Finset (Tree Unit)) : Finset (Tree Unit) :=
  (a ×ˢ b).map ⟨fun x => x.1 △ x.2, fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ => fun h => by simpa using h⟩

/-- A Finset of all trees with `n` nodes. See `mem_treesOfNodesEq` -/
def treesOfNumNodesEq : ℕ → Finset (Tree Unit)
  | 0 => {nil}
  | n + 1 =>
    (antidiagonal n).attach.biUnion fun ijh =>
      pairwiseNode (treesOfNumNodesEq ijh.1.1) (treesOfNumNodesEq ijh.1.2)
  decreasing_by
    · simp_wf; have := fst_le ijh.2; lia
    · simp_wf; have := snd_le ijh.2; lia

@[simp]
theorem treesOfNumNodesEq_zero : treesOfNumNodesEq 0 = {nil} := by rw [treesOfNumNodesEq]

theorem treesOfNumNodesEq_succ (n : ℕ) :
    treesOfNumNodesEq (n + 1) =
      (antidiagonal n).biUnion fun ij =>
        pairwiseNode (treesOfNumNodesEq ij.1) (treesOfNumNodesEq ij.2) := by
  rw [treesOfNumNodesEq]
  ext
  simp

@[simp]
theorem mem_treesOfNumNodesEq {x : Tree Unit} {n : ℕ} :
    x ∈ treesOfNumNodesEq n ↔ x.numNodes = n := by
  induction x using Tree.unitRecOn generalizing n <;> cases n <;>
    simp [treesOfNumNodesEq_succ, *]

theorem mem_treesOfNumNodesEq_numNodes (x : Tree Unit) : x ∈ treesOfNumNodesEq x.numNodes :=
  mem_treesOfNumNodesEq.mpr rfl

@[simp, norm_cast]
theorem coe_treesOfNumNodesEq (n : ℕ) :
    ↑(treesOfNumNodesEq n) = { x : Tree Unit | x.numNodes = n } :=
  Set.ext (by simp)

theorem treesOfNumNodesEq_card_eq_catalan (n : ℕ) : #(treesOfNumNodesEq n) = catalan n := by
  induction n using Nat.case_strong_induction_on with
  | hz => simp
  | hi n ih =>
    rw [treesOfNumNodesEq_succ, card_biUnion, catalan_succ']
    · apply sum_congr rfl
      rintro ⟨i, j⟩ H
      rw [card_map, card_product, ih _ (fst_le H), ih _ (snd_le H)]
    · simp_rw [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left]
      aesop

end Tree
