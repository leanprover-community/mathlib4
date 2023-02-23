/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer

! This file was ported from Lean 3 source module combinatorics.catalan
! leanprover-community/mathlib commit 26b40791e4a5772a4e53d0e28e4df092119dc7da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Fin
import Mathbin.Algebra.BigOperators.NatAntidiagonal
import Mathbin.Algebra.CharZero.Lemmas
import Mathbin.Data.Finset.NatAntidiagonal
import Mathbin.Data.Nat.Choose.Central
import Mathbin.Data.Tree
import Mathbin.Tactic.FieldSimp
import Mathbin.Tactic.LinearCombination

/-!
# Catalan numbers

The Catalan numbers (http://oeis.org/A000108) are probably the most ubiquitous sequence of integers
in mathematics. They enumerate several important objects like binary trees, Dyck paths, and
triangulations of convex polygons.

## Main definitions

* `catalan n`: the `n`th Catalan number, defined recursively as
  `catalan (n + 1) = ∑ i : fin n.succ, catalan i * catalan (n - i)`.

## Main results

* `catalan_eq_central_binom_div `: The explicit formula for the Catalan number using the central
  binomial coefficient, `catalan n = nat.central_binom n / (n + 1)`.

* `trees_of_nodes_eq_card_eq_catalan`: The number of binary trees with `n` internal nodes
  is `catalan n`

## Implementation details

The proof of `catalan_eq_central_binom_div` follows
https://math.stackexchange.com/questions/3304415/catalan-numbers-algebraic-proof-of-the-recurrence-relation

## TODO

* Prove that the Catalan numbers enumerate many interesting objects.
* Provide the many variants of Catalan numbers, e.g. associated to complex reflection groups,
  Fuss-Catalan, etc.

-/


open BigOperators

open Finset

open Finset.Nat.antidiagonal (fst_le snd_le)

/-- The recursive definition of the sequence of Catalan numbers:
`catalan (n + 1) = ∑ i : fin n.succ, catalan i * catalan (n - i)` -/
def catalan : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    ∑ i : Fin n.succ,
      have := i.2
      have := Nat.lt_succ_iff.mpr (n.sub_le i)
      catalan i * catalan (n - i)
#align catalan catalan

@[simp]
theorem catalan_zero : catalan 0 = 1 := by rw [catalan]
#align catalan_zero catalan_zero

theorem catalan_succ (n : ℕ) : catalan (n + 1) = ∑ i : Fin n.succ, catalan i * catalan (n - i) := by
  rw [catalan]
#align catalan_succ catalan_succ

theorem catalan_succ' (n : ℕ) :
    catalan (n + 1) = ∑ ij in Nat.antidiagonal n, catalan ij.1 * catalan ij.2 := by
  rw [catalan_succ, nat.sum_antidiagonal_eq_sum_range_succ (fun x y => catalan x * catalan y) n,
    sum_range]
#align catalan_succ' catalan_succ'

@[simp]
theorem catalan_one : catalan 1 = 1 := by simp [catalan_succ]
#align catalan_one catalan_one

/-- A helper sequence that can be used to prove the equality of the recursive and the explicit
definition using a telescoping sum argument. -/
private def gosper_catalan (n j : ℕ) : ℚ :=
  Nat.centralBinom j * Nat.centralBinom (n - j) * (2 * j - n) / (2 * n * (n + 1))
#align gosper_catalan gosper_catalan

private theorem gosper_trick {n i : ℕ} (h : i ≤ n) :
    gosperCatalan (n + 1) (i + 1) - gosperCatalan (n + 1) i =
      Nat.centralBinom i / (i + 1) * Nat.centralBinom (n - i) / (n - i + 1) :=
  by
  have : (n : ℚ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have : (n : ℚ) + 1 + 1 ≠ 0 := by exact_mod_cast (n + 1).succ_ne_zero
  have : (i : ℚ) + 1 ≠ 0 := by exact_mod_cast i.succ_ne_zero
  have : (n : ℚ) - i + 1 ≠ 0 := by exact_mod_cast (n - i).succ_ne_zero
  have h₁ : ((i : ℚ) + 1) * (i + 1).centralBinom = 2 * (2 * i + 1) * i.central_binom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ i
  have h₂ :
    ((n : ℚ) - i + 1) * (n - i + 1).centralBinom = 2 * (2 * (n - i) + 1) * (n - i).centralBinom :=
    by exact_mod_cast Nat.succ_mul_centralBinom_succ (n - i)
  simp only [gosper_catalan]
  push_cast
  field_simp
  rw [Nat.succ_sub h]
  linear_combination
    (2 : ℚ) * (n - i).centralBinom * (i + 1 - (n - i)) * (n + 1) * (n + 2) * (n - i + 1) * h₁ -
      2 * i.central_binom * (n + 1) * (n + 2) * (i - (n - i) - 1) * (i + 1) * h₂
#align gosper_trick gosper_trick

private theorem gosper_catalan_sub_eq_central_binom_div (n : ℕ) :
    gosperCatalan (n + 1) (n + 1) - gosperCatalan (n + 1) 0 = Nat.centralBinom (n + 1) / (n + 2) :=
  by
  have : (n : ℚ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have : (n : ℚ) + 1 + 1 ≠ 0 := by exact_mod_cast (n + 1).succ_ne_zero
  have h : (n : ℚ) + 2 ≠ 0 := by exact_mod_cast (n + 1).succ_ne_zero
  simp only [gosper_catalan, Nat.sub_zero, Nat.centralBinom_zero, Nat.sub_self]
  field_simp
  ring
#align gosper_catalan_sub_eq_central_binom_div gosper_catalan_sub_eq_central_binom_div

theorem catalan_eq_centralBinom_div (n : ℕ) : catalan n = n.centralBinom / (n + 1) :=
  by
  suffices (catalan n : ℚ) = Nat.centralBinom n / (n + 1)
    by
    have h := Nat.succ_dvd_centralBinom n
    exact_mod_cast this
  induction' n using Nat.case_strong_induction_on with d hd
  · simp
  · simp_rw [catalan_succ, Nat.cast_sum, Nat.cast_mul]
    trans
      (∑ i : Fin d.succ, Nat.centralBinom i / (i + 1) * (Nat.centralBinom (d - i) / (d - i + 1)) :
        ℚ)
    · refine' sum_congr rfl fun i _ => _
      congr
      · exact_mod_cast hd i i.is_le
      · rw_mod_cast [hd (d - i)]
        push_cast
        rw [Nat.cast_sub i.is_le]
        exact tsub_le_self
    · trans ∑ i : Fin d.succ, gosper_catalan (d + 1) (i + 1) - gosper_catalan (d + 1) i
      · refine' sum_congr rfl fun i _ => _
        rw_mod_cast [gosper_trick i.is_le, mul_div]
      · rw [← sum_range fun i => gosper_catalan (d + 1) (i + 1) - gosper_catalan (d + 1) i,
          sum_range_sub, Nat.succ_eq_add_one]
        exact_mod_cast gosper_catalan_sub_eq_central_binom_div d
#align catalan_eq_central_binom_div catalan_eq_centralBinom_div

theorem succ_mul_catalan_eq_centralBinom (n : ℕ) : (n + 1) * catalan n = n.centralBinom :=
  (Nat.eq_mul_of_div_eq_right n.succ_dvd_centralBinom (catalan_eq_centralBinom_div n).symm).symm
#align succ_mul_catalan_eq_central_binom succ_mul_catalan_eq_centralBinom

theorem catalan_two : catalan 2 = 2 := by
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
#align catalan_two catalan_two

theorem catalan_three : catalan 3 = 5 := by
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
#align catalan_three catalan_three

namespace Tree

open Tree

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given two finsets, find all trees that can be formed with
  left child in `a` and right child in `b` -/
@[reducible]
def pairwiseNode (a b : Finset (Tree Unit)) : Finset (Tree Unit) :=
  (a ×ˢ b).map ⟨fun x => x.1 △ x.2, fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ => fun h => by simpa using h⟩
#align tree.pairwise_node Tree.pairwiseNode

/-- A finset of all trees with `n` nodes. See `mem_trees_of_nodes_eq` -/
def treesOfNumNodesEq : ℕ → Finset (Tree Unit)
  | 0 => {nil}
  | n + 1 =>
    (Finset.Nat.antidiagonal n).attach.bunionᵢ fun ijh =>
      have := Nat.lt_succ_of_le (fst_le ijh.2)
      have := Nat.lt_succ_of_le (snd_le ijh.2)
      pairwiseNode (trees_of_num_nodes_eq ijh.1.1) (trees_of_num_nodes_eq ijh.1.2)
#align tree.trees_of_num_nodes_eq Tree.treesOfNumNodesEq

@[simp]
theorem trees_of_nodes_eq_zero : treesOfNumNodesEq 0 = {nil} := by rw [trees_of_num_nodes_eq]
#align tree.trees_of_nodes_eq_zero Tree.trees_of_nodes_eq_zero

theorem trees_of_nodes_eq_succ (n : ℕ) :
    treesOfNumNodesEq (n + 1) =
      (Nat.antidiagonal n).bunionᵢ fun ij =>
        pairwiseNode (treesOfNumNodesEq ij.1) (treesOfNumNodesEq ij.2) :=
  by
  rw [trees_of_num_nodes_eq]
  ext
  simp
#align tree.trees_of_nodes_eq_succ Tree.trees_of_nodes_eq_succ

@[simp]
theorem mem_trees_of_nodes_eq {x : Tree Unit} {n : ℕ} : x ∈ treesOfNumNodesEq n ↔ x.numNodes = n :=
  by
  induction x using Tree.unitRecOn generalizing n <;> cases n <;>
    simp [trees_of_nodes_eq_succ, Nat.succ_eq_add_one, *]
  trivial
#align tree.mem_trees_of_nodes_eq Tree.mem_trees_of_nodes_eq

theorem mem_trees_of_nodes_eq_numNodes (x : Tree Unit) : x ∈ treesOfNumNodesEq x.numNodes :=
  mem_trees_of_nodes_eq.mpr rfl
#align tree.mem_trees_of_nodes_eq_num_nodes Tree.mem_trees_of_nodes_eq_numNodes

@[simp, norm_cast]
theorem coe_trees_of_nodes_eq (n : ℕ) :
    ↑(treesOfNumNodesEq n) = { x : Tree Unit | x.numNodes = n } :=
  Set.ext (by simp)
#align tree.coe_trees_of_nodes_eq Tree.coe_trees_of_nodes_eq

theorem trees_of_nodes_eq_card_eq_catalan (n : ℕ) : (treesOfNumNodesEq n).card = catalan n :=
  by
  induction' n using Nat.case_strong_induction_on with n ih
  · simp
  rw [trees_of_nodes_eq_succ, card_bUnion, catalan_succ']
  · apply sum_congr rfl
    rintro ⟨i, j⟩ H
    simp [ih _ (fst_le H), ih _ (snd_le H)]
  · simp_rw [disjoint_left]
    rintro ⟨i, j⟩ _ ⟨i', j'⟩ _
    clear * -
    tidy
#align tree.trees_of_nodes_eq_card_eq_catalan Tree.trees_of_nodes_eq_card_eq_catalan

end Tree

