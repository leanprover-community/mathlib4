/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer, Weijie Jiang
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Qify

/-!
# Catalan numbers

The Catalan numbers (http://oeis.org/A000108) are probably the most ubiquitous sequence of integers
in mathematics. They enumerate several important objects like binary trees, Dyck paths, and
triangulations of convex polygons.

## Main definitions

* `catalan n`: the `n`th Catalan number, defined recursively as
  `catalan (n + 1) = ∑ i : Fin n.succ, catalan i * catalan (n - i)`.

## Main results

* `catalan_eq_centralBinom_div`: The explicit formula for the Catalan number using the central
  binomial coefficient, `catalan n = Nat.centralBinom n / (n + 1)`.

* `treesOfNumNodesEq_card_eq_catalan`: The number of binary trees with `n` internal nodes
  is `catalan n`

## Implementation details

The proof of `catalan_eq_centralBinom_div` follows https://math.stackexchange.com/questions/3304415

## TODO

* Prove that the Catalan numbers enumerate many interesting objects.
* Provide the many variants of Catalan numbers, e.g. associated to complex reflection groups,
  Fuss-Catalan, etc.

-/


open Finset

open Finset.antidiagonal (fst_le snd_le)

/-- The recursive definition of the sequence of Catalan numbers:
`catalan (n + 1) = ∑ i : Fin n.succ, catalan i * catalan (n - i)` -/
def catalan : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    ∑ i : Fin n.succ,
      catalan i * catalan (n - i)

@[simp]
theorem catalan_zero : catalan 0 = 1 := by rw [catalan]

theorem catalan_succ (n : ℕ) : catalan (n + 1) = ∑ i : Fin n.succ, catalan i * catalan (n - i) := by
  rw [catalan]

theorem catalan_succ' (n : ℕ) :
    catalan (n + 1) = ∑ ij ∈ antidiagonal n, catalan ij.1 * catalan ij.2 := by
  rw [catalan_succ, Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => catalan x * catalan y) n,
    sum_range]

@[simp]
theorem catalan_one : catalan 1 = 1 := by simp [catalan_succ]

/-- A helper sequence that can be used to prove the equality of the recursive and the explicit
definition using a telescoping sum argument. -/
private def gosperCatalan (n j : ℕ) : ℚ :=
  Nat.centralBinom j * Nat.centralBinom (n - j) * (2 * j - n) / (2 * n * (n + 1))

private theorem gosper_trick {n i : ℕ} (h : i ≤ n) :
    gosperCatalan (n + 1) (i + 1) - gosperCatalan (n + 1) i =
      Nat.centralBinom i / (i + 1) * Nat.centralBinom (n - i) / (n - i + 1) := by
  have l₁ : (i : ℚ) + 1 ≠ 0 := by norm_cast
  have l₂ : (n : ℚ) - i + 1 ≠ 0 := by norm_cast
  have h₁ := (mul_div_cancel_left₀ (↑(Nat.centralBinom (i + 1))) l₁).symm
  have h₂ := (mul_div_cancel_left₀ (↑(Nat.centralBinom (n - i + 1))) l₂).symm
  have h₃ : ((i : ℚ) + 1) * (i + 1).centralBinom = 2 * (2 * i + 1) * i.centralBinom :=
    mod_cast Nat.succ_mul_centralBinom_succ i
  have h₄ :
    ((n : ℚ) - i + 1) * (n - i + 1).centralBinom = 2 * (2 * (n - i) + 1) * (n - i).centralBinom :=
      mod_cast Nat.succ_mul_centralBinom_succ (n - i)
  simp only [gosperCatalan]
  push_cast
  rw [show n + 1 - i = n - i + 1 by rw [Nat.add_comm (n - i) 1, ← (Nat.add_sub_assoc h 1),
    add_comm]]
  rw [h₁, h₂, h₃, h₄]
  field_simp
  ring

private theorem gosper_catalan_sub_eq_central_binom_div (n : ℕ) : gosperCatalan (n + 1) (n + 1) -
    gosperCatalan (n + 1) 0 = Nat.centralBinom (n + 1) / (n + 2) := by
  simp only [gosperCatalan, Nat.sub_zero, Nat.centralBinom_zero, Nat.sub_self]
  simp [field]
  ring

theorem catalan_eq_centralBinom_div (n : ℕ) : catalan n = n.centralBinom / (n + 1) := by
  suffices (catalan n : ℚ) = Nat.centralBinom n / (n + 1) by
    have h := Nat.succ_dvd_centralBinom n
    exact mod_cast this
  induction n using Nat.caseStrongRecOn with
  | zero => simp
  | ind d hd =>
    simp_rw [catalan_succ, Nat.cast_sum, Nat.cast_mul]
    trans (∑ i : Fin d.succ, Nat.centralBinom i / (i + 1) *
                            (Nat.centralBinom (d - i) / (d - i + 1)) : ℚ)
    · congr
      ext1 x
      have m_le_d : x.val ≤ d := by omega
      have d_minus_x_le_d : (d - x.val) ≤ d := tsub_le_self
      rw [hd _ m_le_d, hd _ d_minus_x_le_d]
      norm_cast
    · trans (∑ i : Fin d.succ, (gosperCatalan (d + 1) (i + 1) - gosperCatalan (d + 1) i))
      · refine sum_congr rfl fun i _ => ?_
        rw [gosper_trick i.is_le, mul_div]
      · rw [← sum_range fun i => gosperCatalan (d + 1) (i + 1) - gosperCatalan (d + 1) i,
            sum_range_sub, Nat.succ_eq_add_one]
        rw [gosper_catalan_sub_eq_central_binom_div d]
        norm_cast

theorem succ_mul_catalan_eq_centralBinom (n : ℕ) : (n + 1) * catalan n = n.centralBinom :=
  (Nat.eq_mul_of_div_eq_right n.succ_dvd_centralBinom (catalan_eq_centralBinom_div n).symm).symm

theorem catalan_two : catalan 2 = 2 := by
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

theorem catalan_three : catalan 3 = 5 := by
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

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
    · simp_wf; have := fst_le ijh.2; cutsat
    · simp_wf; have := snd_le ijh.2; cutsat

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

/-!
# Schroder numbers

The Schröder numbers (http://oeis.org/A006318) are a sequence of integers that appear in various
combinatorial contexts.

## Main definitions
* `largeSchroder n`: the `n`th large Schroder number, defined recursively as
  `largeSchroder (n + 1) = largeSchroder n +
    ∑ i : Fin n.succ, largeSchroder i * largeSchroder (n - i)`.
* `smallSchroder n`: the `n`th small Schroder number, defined as
  `smallSchroder n = largeSchroder n / 2` for `n ≠ 1` and `smallSchroder 1 = 1`.
-/

open Nat

/-- The recursive definition of the sequence of the large Schroder numbers :
`largeSchroder (n + 1) = largeSchroder n + `
  `∑ i : Fin n.succ, largeSchroder i * largeSchroder (n - i)` -/
def largeSchroder : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    largeSchroder n +
      ∑ i : Fin n.succ, largeSchroder i * largeSchroder (n - i)

@[simp]
theorem largeSchroder_zero : largeSchroder 0 = 1 := by
  simp [largeSchroder]

@[simp]
theorem largeSchroder_one : largeSchroder 1 = 2 := by
  simp [largeSchroder]

@[simp]
theorem largeSchroder_two : largeSchroder 2 = 6 := by
  simp [largeSchroder]

theorem largeSchroder_succ (n : ℕ) :
  largeSchroder (n + 1) = largeSchroder n +
    ∑ i : Fin n.succ, largeSchroder i * largeSchroder (n - i) := by
  rw [largeSchroder]

theorem largeSchroder_succ' (n : ℕ) :
  largeSchroder (n + 1) = largeSchroder n +
    ∑ ij ∈ antidiagonal n, largeSchroder ij.1 * largeSchroder ij.2 := by
  rw [largeSchroder_succ, Nat.sum_antidiagonal_eq_sum_range_succ
      (fun x y => largeSchroder x * largeSchroder y) n, sum_range]

theorem largeSchroder_succ_range (n : ℕ) :
  largeSchroder (n + 1) = largeSchroder n +
    ∑ i ∈ range (n + 1), largeSchroder i * largeSchroder (n - i) := by
  rw [largeSchroder_succ, sum_range]

/-- The small Schroder number is equal to : `largeSchroder n = 2 * smallSchroder (n + 1), n ≥ 1` -/
def smallSchroder (n : ℕ) : ℚ :=
  match n with
  | 0 => 1
  | 1 => 1
  | n + 1 => largeSchroder n / 2

@[simp]
theorem smallSchroder_zero : smallSchroder 0 = 1 := by
  simp only [smallSchroder]

@[simp]
theorem smallSchroder_one : smallSchroder 1 = 1 := by
  simp only [smallSchroder]

theorem largeSchroder_eq_smallSchroder_succ_mul_two {n : ℕ} (h : 1 ≤ n) :
  largeSchroder n = smallSchroder (n + 1) * 2 := by
  simp only [smallSchroder]
  aesop

theorem smallSchroder_succ_eq_largeSchroder_div_two {n : ℕ} (h : 1 ≤ n) :
  smallSchroder (n + 1) = largeSchroder n / 2 := by
  simp only [smallSchroder]
  aesop

theorem smallSchroder_sum_range (n : ℕ) (hn : 1 < n) :
  smallSchroder (n + 1) =
    3 * smallSchroder n +
      2 * ∑ i ∈ range (n - 2), smallSchroder (i + 2) * smallSchroder (n - 1 - i) := by
  by_cases hn' : n = 1
  · simp [hn']
    aesop
  · have hn : 2 ≤ n := by omega
    obtain h_largeSchroder_succ := largeSchroder_succ_range (n - 1)
    nth_rw 1 [show n - 1 + 1 = n by omega] at h_largeSchroder_succ
    have sum_eq : ∑ i ∈ range (n - 1 + 1), largeSchroder i * largeSchroder (n - 1 - i) =
      2 * largeSchroder (n - 1) + ∑ i ∈ Ico 1 (n - 1),
        largeSchroder i * largeSchroder (n - 1 - i) := by
      rw [sum_range_succ, show n - 1 = n - 2 + 1 by omega, sum_range_succ', sum_Ico_eq_sum_range,
        show n - 2 + 1 = n - 1 by omega, show n - 1 - 1 = n - 2 by omega]
      simp only [largeSchroder_zero, tsub_zero, one_mul, tsub_self, mul_one]
      rw [add_assoc, ← two_mul, add_comm]
      congr 1
      apply sum_congr rfl
      intro x hx
      simp at hx
      rw [add_comm x 1]
    rw [sum_eq] at h_largeSchroder_succ
    have sum_eq' : ∑ i ∈ Ico 1 (n - 1), (largeSchroder i : ℚ) * largeSchroder (n - 1 - i) =
      4 * ∑ i ∈ Ico 1 (n - 1), smallSchroder (i + 1) * smallSchroder (n - i) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x hx
      simp at hx
      rw [largeSchroder_eq_smallSchroder_succ_mul_two (by omega),
        largeSchroder_eq_smallSchroder_succ_mul_two (by omega), show n - 1 - x + 1 = n - x by omega]
      linarith
    qify at h_largeSchroder_succ
    rw [sum_eq', largeSchroder_eq_smallSchroder_succ_mul_two (by omega),
      largeSchroder_eq_smallSchroder_succ_mul_two (by omega), sum_Ico_eq_sum_range,
      ← mul_right_inj' (show (1 / 2 : ℚ) ≠ 0 from by norm_num)] at h_largeSchroder_succ
    have : (1 / 2 : ℚ) * (smallSchroder (n + 1) * 2) = smallSchroder (n + 1) := by ring
    rw [this] at h_largeSchroder_succ
    rw [h_largeSchroder_succ, show n - 1 + 1 = n by omega, show n - 1 - 1 = n - 2 by omega]
    ring_nf
    congr 2
    apply sum_congr rfl
    intro x hx
    simp at hx
    rw [show n - (1 + x) = n - 1 - x by omega]
