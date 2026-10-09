/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Hamiltonian graphs from cyclic permutations

If `σ` is a cycle on a finset `s` and `G.Adj x (σ x)` for every `x`, then the cycle graph on
`#s` vertices embeds in `G`. In particular, if `σ : Perm α` is a cycle, `3 ≤ #α`, and
`G.Adj x (σ x)` for every `x`, then `G` is Hamiltonian.
-/

public section

open Finset Function Equiv Equiv.Perm

namespace SimpleGraph

variable {α : Type*} {G : SimpleGraph α}

/-- If `σ` is a cycle on a finset `s` and each vertex is adjacent to its image under `σ`,
then the cycle graph on `#s` vertices is contained in `G`. -/
theorem cycleGraph_isContained_of_isCycleOn {σ : Perm α} {s : Finset α} (hσ : σ.IsCycleOn s)
    (hadj : ∀ v, G.Adj v (σ v)) : cycleGraph #s ⊑ G := by
  obtain rfl | ⟨v, hv⟩ := s.eq_empty_or_nonempty
  · rw [card_empty]
    exact .of_isEmpty
  refine ⟨⟨fun i ↦ (σ ^ i.1) v, fun {i j} h ↦ ?_⟩,
    fun i j hij ↦ Fin.ext <| hσ.injOn_pow_apply hv i.2 j.2 hij⟩
  wlog hij : i < j generalizing i j
  · exact this h.symm (by grind [SimpleGraph.irrefl]) |>.symm
  rcases cycleGraph_adj'.mp h with h | h
  · obtain ⟨hi, hj⟩ : i.1 = 0 ∧ j.1 = #s - 1 := by grind [Fin.coe_sub_iff_lt]
    rw [hi, hj, adj_comm]
    simpa [← mul_apply, ← pow_succ', Nat.sub_add_cancel (card_pos.mpr ⟨v, hv⟩),
      hσ.pow_card_apply hv] using hadj ((σ ^ (#s - 1)) v)
  · rw [show j.1 = i.1 + 1 by grind [Fin.sub_val_of_le], pow_succ', mul_apply]
    exact hadj _

/-- If a cyclic permutation `σ` of a type with at least 3 elements is such that each vertex is
adjacent to its image under `σ`, then `G` is Hamiltonian. -/
theorem IsHamiltonian.of_perm [Fintype α] [DecidableEq α] {σ : Perm α} (hσ : σ.IsCycle)
    (hadj : ∀ v, G.Adj v (σ v)) (hcard : 3 ≤ Fintype.card α) : G.IsHamiltonian := by
  have h : {x | σ x ≠ x} = ((univ : Finset α) : Set α) := by
    simpa [Set.eq_univ_iff_forall] using fun x ↦ (hadj x).ne'
  simpa using (isHamiltonian_iff_cycleGraph_isContained hcard).mpr
    (cycleGraph_isContained_of_isCycleOn (s := .univ) (h ▸ hσ.isCycleOn) hadj)

end SimpleGraph
