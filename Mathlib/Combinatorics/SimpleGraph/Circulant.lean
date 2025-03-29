/-
Copyright (c) 2024 Iván Renison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison, Bhavik Mehta
-/
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Definition of circulant graphs

This file defines and proves several fact about circulant graphs.
A circulant graph over type `G` with jumps `s : Set G` is a graph in which two vertices `u` and `v`
are adjacent if and only if `u - v ∈ s` or `v - u ∈ s`. The elements of `s` are called jumps.

## Main declarations

* `SimpleGraph.circulantGraph s`: the circulant graph over `G` with jumps `s`.
* `SimpleGraph.cycleGraph n`: the cycle graph over `Fin n`.
-/

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
  ext (u v : G)
  simp only [circulantGraph, fromRel_adj, Set.mem_union, Set.mem_neg, neg_sub, and_congr_right_iff,
    iff_self_or]
  intro _ h
  exact Or.symm h

instance [DecidableEq G] [DecidablePred (· ∈ s)] : DecidableRel (circulantGraph s).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem circulantGraph_adj_translate {s : Set G} {u v d : G} :
    (circulantGraph s).Adj (u + d) (v + d) ↔ (circulantGraph s).Adj u v := by simp

/-- Cycle graph over `Fin n` -/
def cycleGraph : (n : ℕ) → SimpleGraph (Fin n)
  | 0 => ⊥
  | _ + 1 => circulantGraph {1}

instance : (n : ℕ) → DecidableRel (cycleGraph n).Adj
  | 0 => fun _ _ => inferInstanceAs (Decidable False)
  | _ + 1 => inferInstanceAs (DecidableRel (circulantGraph _).Adj)

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
  rw [cycleGraph_one_eq_bot]
  exact id

theorem cycleGraph_adj {n : ℕ} {u v : Fin (n + 2)} :
    (cycleGraph (n + 2)).Adj u v ↔ u - v = 1 ∨ v - u = 1 := by
  simp only [cycleGraph, circulantGraph_adj, Set.mem_singleton_iff, and_iff_right_iff_imp]
  intro _ _
  simp_all

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

private def cycleGraph_EulerianCircuit_cons (n : ℕ) :
    ∀ m : Fin (n + 3), (cycleGraph (n + 3)).Walk m 0
  | ⟨0, h⟩ => Walk.nil
  | ⟨m + 1, h⟩ =>
    have hadj : (cycleGraph (n + 3)).Adj ⟨m + 1, h⟩ ⟨m, Nat.lt_of_succ_lt h⟩ := by
      simp [cycleGraph_adj, Fin.ext_iff, Fin.sub_val_of_le]
    Walk.cons hadj (cycleGraph_EulerianCircuit_cons n ⟨m, Nat.lt_of_succ_lt h⟩)

/-- Eulerian trail of `cycleGraph (n + 3)` -/
def cycleGraph_EulerianCircuit (n : ℕ) : (cycleGraph (n + 3)).Walk 0 0 :=
  have hadj : (cycleGraph (n + 3)).Adj 0 (Fin.last (n + 2)) := by
    simp [cycleGraph_adj]
  Walk.cons hadj (cycleGraph_EulerianCircuit_cons n (Fin.last (n + 2)))

private theorem cycleGraph_EulerianCircuit_cons_length (n : ℕ) : ∀ m : Fin (n + 3),
    (cycleGraph_EulerianCircuit_cons n m).length = m.val
  | ⟨0, h⟩ => by
    unfold cycleGraph_EulerianCircuit_cons
    rfl
  | ⟨m + 1, h⟩ => by
    unfold cycleGraph_EulerianCircuit_cons
    simp only [Walk.length_cons]
    rw [cycleGraph_EulerianCircuit_cons_length n]

theorem cycleGraph_EulerianCircuit_length {n : ℕ} :
    (cycleGraph_EulerianCircuit n).length = n + 3 := by
  unfold cycleGraph_EulerianCircuit
  simp [cycleGraph_EulerianCircuit_cons_length]

end SimpleGraph
