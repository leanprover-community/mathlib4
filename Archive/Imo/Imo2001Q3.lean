/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.NormNum.Ineq

/-!
# IMO 2001 Q3

Twenty-one girls and twenty-one boys took part in a mathematical competition. It turned out that

1. each contestant solved at most six problems, and
2. for each pair of a girl and a boy, there was at least one problem that was solved by
both the girl and the boy.

Show that there is a problem that was solved by at least three girls and at least three boys.

# Solution

Note that not all of the problems a girl $g$ solves can be "hard" for boys, in the sense that
at most two boys solved it. If that was true, by condition 1 at most $6 × 2 = 12$ boys solved
some problem $g$, but by condition 2 that property holds for all 21 boys, which is a
contradiction.

Hence there are at most 5 problems $g$ solved that are hard for boys, and the number of girl-boy
pairs who solved some problem in common that was hard for boys is at most $5 × 2 × 21 = 210$.
By the same reasoning this bound holds when "girls" and "boys" are swapped throughout, but there
are $21^2$ girl-boy pairs in all and $21^2 > 210 + 210$, so some girl-boy pairs solved only problems
in common that were not hard for girls or boys. By condition 2 the result follows.
-/

namespace Imo2001Q3

open Finset

/-- The conditions on the problems the girls and boys solved, represented as functions from `Fin 21`
(index in cohort) to the finset of problems they solved (numbered arbitrarily). -/
structure Condition (G B : Fin 21 → Finset ℕ) where
  /-- Every girl solved at most six problems. -/
  G_le_6 (i) : #(G i) ≤ 6
  /-- Every boy solved at most six problems. -/
  B_le_6 (j) : #(B j) ≤ 6
  /-- Every girl-boy pair solved at least one problem in common. -/
  G_inter_B (i j) : ¬Disjoint (G i) (B j)

/-- A problem is easy for a cohort (boys or girls) if at least three of its members solved it. -/
def Easy (F : Fin 21 → Finset ℕ) (p : ℕ) : Prop := 3 ≤ #{i | p ∈ F i}

variable {G B : Fin 21 → Finset ℕ}

open Classical in
/-- Every contestant solved at most five problems that were not easy for the other cohort. -/
lemma card_not_easy_le_five {i : Fin 21} (hG : #(G i) ≤ 6) (hB : ∀ j, ¬Disjoint (G i) (B j)) :
    #{p ∈ G i | ¬Easy B p} ≤ 5 := by
  by_contra! h
  replace h := le_antisymm (card_filter_le ..) (hG.trans h)
  simp_rw [card_filter_eq_iff, Easy, not_le] at h
  suffices 21 ≤ 12 by norm_num at this
  calc
    _ = #{j | ¬Disjoint (G i) (B j)} := by simp [filter_true_of_mem fun j _ ↦ hB j]
    _ = #((G i).biUnion fun p ↦ {j | p ∈ B j}) := by congr 1; ext j; simp [not_disjoint_iff]
    _ ≤ ∑ p ∈ G i, #{j | p ∈ B j} := card_biUnion_le
    _ ≤ ∑ p ∈ G i, 2 := sum_le_sum fun p mp ↦ Nat.le_of_lt_succ (h p mp)
    _ ≤ _ := by rw [sum_const, smul_eq_mul]; omega

open Classical in
/-- There are at most 210 girl-boy pairs who solved some problem in common that was not easy for
a fixed cohort. -/
lemma card_not_easy_le_210 (hG : ∀ i, #(G i) ≤ 6) (hB : ∀ i j, ¬Disjoint (G i) (B j)) :
    #{ij : Fin 21 × Fin 21 | ∃ p, ¬Easy B p ∧ p ∈ G ij.1 ∩ B ij.2} ≤ 210 :=
  calc
    _ = ∑ i, #{j | ∃ p, ¬Easy B p ∧ p ∈ G i ∩ B j} := by
      simp_rw [card_filter, ← univ_product_univ, sum_product]
    _ = ∑ i, #({p ∈ G i | ¬Easy B p}.biUnion fun p ↦ {j | p ∈ B j}) := by
      congr!; ext
      simp_rw [mem_biUnion, mem_inter, mem_filter]
      congr! 2; tauto
    _ ≤ ∑ i, ∑ p ∈ G i with ¬Easy B p, #{j | p ∈ B j} := sum_le_sum fun _ _ ↦ card_biUnion_le
    _ ≤ ∑ i, ∑ p ∈ G i with ¬Easy B p, 2 := by
      gcongr with i _ p mp
      rw [mem_filter, Easy, not_le] at mp
      exact Nat.le_of_lt_succ mp.2
    _ ≤ ∑ i : Fin 21, 5 * 2 := by
      gcongr with i
      rw [sum_const, smul_eq_mul]
      exact mul_le_mul_right' (card_not_easy_le_five (hG _) (hB _)) _
    _ = _ := by norm_num

theorem result (h : Condition G B) : ∃ p, Easy G p ∧ Easy B p := by
  obtain ⟨G_le_6, B_le_6, G_inter_B⟩ := h
  have B_inter_G : ∀ i j, ¬Disjoint (B i) (G j) := fun i j ↦ by
    rw [disjoint_comm]; exact G_inter_B j i
  have cB := card_not_easy_le_210 G_le_6 G_inter_B
  have cG := card_not_easy_le_210 B_le_6 B_inter_G
  rw [← card_map ⟨_, Prod.swap_injective⟩] at cG
  have key := (card_union_le _ _).trans (add_le_add cB cG) |>.trans_lt
    (show _ < #(@univ (Fin 21 × Fin 21) _) by simp)
  obtain ⟨⟨i, j⟩, -, hij⟩ := exists_mem_notMem_of_card_lt_card key
  simp_rw [mem_union, mem_map, mem_filter_univ, Function.Embedding.coeFn_mk, Prod.exists,
    Prod.swap_prod_mk, Prod.mk.injEq, existsAndEq, true_and, and_true, not_or, not_exists,
    not_and', not_not, mem_inter, and_imp] at hij
  obtain ⟨p, pG, pB⟩ := not_disjoint_iff.mp (G_inter_B i j)
  use p, hij.2 _ pB pG, hij.1 _ pG pB

end Imo2001Q3
