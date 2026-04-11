/-
Copyright (c) 2024 Iván Renison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Definition of cycle graphs

This file defines and proves several fact about cycle graphs on `n` vertices and the cycle around
the cycle graph when `n ≥ 3`.

## Main declarations

* `SimpleGraph.cycleGraph n`: the cycle graph over `Fin n`.
* `(SimpleGraph.cycleGraph n).cycle`: the cycle around `cycleGraph (n + 3)` starting at 0.
-/

@[expose] public section

namespace SimpleGraph

open Walk

/-- Cycle graph over `Fin n` -/
def cycleGraph : (n : ℕ) → SimpleGraph (Fin n)
  | 0 | 1 => ⊥
  | _ + 2 => {
    Adj a b := a - b = 1 ∨ b - a = 1
    symm _ _ := Or.symm
    loopless.irrefl _ h := h.elim (by simp) (by simp)
  }

instance : (n : ℕ) → DecidableRel (cycleGraph n).Adj
  | 0 | 1 => fun _ _ => inferInstanceAs (Decidable False)
  | _ + 2 => by unfold cycleGraph; infer_instance

theorem cycleGraph_zero_adj {u v : Fin 0} : ¬(cycleGraph 0).Adj u v := id

theorem cycleGraph_zero_eq_bot : cycleGraph 0 = ⊥ := Subsingleton.elim _ _
theorem cycleGraph_one_eq_bot : cycleGraph 1 = ⊥ := Subsingleton.elim _ _
theorem cycleGraph_zero_eq_top : cycleGraph 0 = ⊤ := Subsingleton.elim _ _
theorem cycleGraph_one_eq_top : cycleGraph 1 = ⊤ := Subsingleton.elim _ _

theorem cycleGraph_two_eq_top : cycleGraph 2 = ⊤ := by
  simp only [SimpleGraph.ext_iff, funext_iff]
  decide

theorem cycleGraph_three_eq_top : cycleGraph 3 = ⊤ := by
  simp only [SimpleGraph.ext_iff, funext_iff]
  decide

theorem cycleGraph_one_adj {u v : Fin 1} : ¬(cycleGraph 1).Adj u v := by
  simp [cycleGraph_one_eq_bot]

theorem cycleGraph_adj {n : ℕ} {u v : Fin (n + 2)} :
    (cycleGraph (n + 2)).Adj u v ↔ u - v = 1 ∨ v - u = 1 := Iff.rfl

theorem cycleGraph_adj' {n : ℕ} {u v : Fin n} :
    (cycleGraph n).Adj u v ↔ (u - v).val = 1 ∨ (v - u).val = 1 := by
  match n with
  | 0 => exact u.elim0
  | 1 => simp [cycleGraph_one_adj]
  | n + 2 => simp [cycleGraph_adj, Fin.ext_iff]

theorem cycleGraph_neighborSet {n : ℕ} {v : Fin (n + 2)} :
    (cycleGraph (n + 2)).neighborSet v = {v - 1, v + 1} := by
  ext w
  simp only [mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [cycleGraph_adj, sub_eq_iff_eq_add', sub_eq_iff_eq_add', eq_sub_iff_add_eq, eq_comm]

theorem cycleGraph_neighborFinset {n : ℕ} {v : Fin (n + 2)} :
    (cycleGraph (n + 2)).neighborFinset v = {v - 1, v + 1} := by
  simp [neighborFinset, cycleGraph_neighborSet]

theorem cycleGraph_degree_two_le {n : ℕ} {v : Fin (n + 2)} :
    (cycleGraph (n + 2)).degree v = Finset.card {v - 1, v + 1} := by
  rw [SimpleGraph.degree, cycleGraph_neighborFinset]

theorem cycleGraph_degree_three_le {n : ℕ} {v : Fin (n + 3)} :
    (cycleGraph (n + 3)).degree v = 2 := by
  rw [cycleGraph_degree_two_le, Finset.card_pair]
  simp only [ne_eq, sub_eq_iff_eq_add, add_assoc v, left_eq_add]
  exact ne_of_beq_false rfl

theorem pathGraph_le_cycleGraph {n : ℕ} : pathGraph n ≤ cycleGraph n := by
  match n with
  | 0 | 1 => simp
  | n + 2 =>
    intro u v h
    rw [pathGraph_adj] at h
    rw [cycleGraph_adj']
    cases h with
    | inl h | inr h =>
      simp [Fin.coe_sub_iff_le.mpr (Nat.lt_of_succ_le h.le).le, Nat.eq_sub_of_add_eq' h]

theorem cycleGraph_preconnected {n : ℕ} : (cycleGraph n).Preconnected :=
  (pathGraph_preconnected n).mono pathGraph_le_cycleGraph

theorem cycleGraph_connected {n : ℕ} : (cycleGraph (n + 1)).Connected :=
  (pathGraph_connected n).mono pathGraph_le_cycleGraph

section cycle

set_option backward.privateInPublic true in
private def cycleGraph.cycleCons (n : ℕ) : ∀ m : Fin (n + 3), (cycleGraph (n + 3)).Walk m 0
  | ⟨0, h⟩ => Walk.nil
  | ⟨m + 1, h⟩ =>
    have hadj : (cycleGraph (n + 3)).Adj ⟨m + 1, h⟩ ⟨m, Nat.lt_of_succ_lt h⟩ := by
      simp [cycleGraph_adj, Fin.ext_iff, Fin.sub_val_of_le]
    Walk.cons hadj (cycleGraph.cycleCons n ⟨m, Nat.lt_of_succ_lt h⟩)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The Eulerian cycle of `cycleGraph (n + 3)` -/
def cycleGraph.cycle (n : ℕ) : (cycleGraph (n + 3)).Walk 0 0 :=
  have hadj : (cycleGraph (n + 3)).Adj 0 (Fin.last (n + 2)) := by
    simp [cycleGraph_adj]
  Walk.cons hadj (cycleGraph.cycleCons n (Fin.last (n + 2)))

@[deprecated (since := "2026-02-15")]
alias cycleGraph_EulerianCircuit := cycleGraph.cycle

private theorem cycleGraph.length_cycle_cons (n : ℕ) :
    ∀ m : Fin (n + 3), (cycleGraph.cycleCons n m).length = m.val
  | ⟨0, h⟩ => by
    unfold cycleGraph.cycleCons
    rfl
  | ⟨m + 1, h⟩ => by
    unfold cycleGraph.cycleCons
    simp only [Walk.length_cons]
    rw [cycleGraph.length_cycle_cons n]

variable {n : ℕ}

@[simp, grind =]
theorem cycleGraph.length_cycle : (cycleGraph.cycle n).length = n + 3 := by
  unfold cycleGraph.cycle
  simp [cycleGraph.length_cycle_cons]

@[deprecated (since := "2026-02-15")]
alias cycleGraph_EulerianCircuit_length := cycleGraph.length_cycle

private theorem cycleGraph.getVert_cycleCons (m : Fin (n + 3)) (i : ℕ) (hi : i ≤ m.val) :
    (cycleGraph.cycleCons n m).getVert i = (m - i) % (n + 3) := by
  obtain ⟨m, hm⟩ := m
  induction i generalizing m
  · simp [Nat.mod_eq_of_lt hm]
  · cases m <;> grind +locals [getVert_cons_succ]

theorem cycleGraph.getVert_cycle {m : ℕ} (hm : m ≤ n + 3) :
    (cycleGraph.cycle n).getVert m = ⟨(n + 3 - m) % (n + 3), Nat.mod_lt _ (by lia)⟩ := by
  cases m
  · simp
  · grind +locals [getVert_cons_succ, cycleGraph.getVert_cycleCons]

theorem cycleGraph.isPath_tail_cycle : (cycleGraph.cycle n).tail.IsPath := by
  refine isPath_iff_injective_get_support _ |>.mpr fun ⟨i, hi⟩ ⟨j, hj⟩ hij ↦ ?_
  rw [support_tail_of_not_nil _ (of_decide_eq_false rfl)] at hi hj
  simp only [List.get_eq_getElem, support_getElem_eq_getVert, getVert_tail] at hij
  grind [← Nat.mod_eq_of_lt, cycleGraph.getVert_cycle]

theorem cycleGraph.isCycle_cycle : (cycleGraph.cycle n).IsCycle :=
  isCycle_iff_isPath_tail_and_le_length.mpr ⟨cycleGraph.isPath_tail_cycle, by simp⟩

end cycle

end SimpleGraph
