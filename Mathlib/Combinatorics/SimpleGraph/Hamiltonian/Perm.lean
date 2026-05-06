/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Walk.Iterate
public import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Hamiltonian graphs from cyclic permutations

If `σ : Perm α` is a single cycle with full support, `3 ≤ #α`, and `G.Adj x (σ x)` for every
`x`, then `G` is Hamiltonian. The witnessing walk is `Walk.iterate σ … x (#α − 1)` closed by
the edge `s(x, σ x)`.
-/

public section

open Finset Function Equiv Equiv.Perm

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α}

/-- Given a cyclic permutation with full support on at least 3 elements which
sends each vertex to an adjacent one, then the graph is hamiltonian. -/
theorem IsHamiltonian.of_perm {σ : Perm α}
    (hcycle : σ.IsCycle) (hsupport : σ.support = .univ)
    (hadj : ∀ x, G.Adj x (σ x))
    (hcard3 : 3 ≤ Fintype.card α) : G.IsHamiltonian := by
  intro _
  obtain ⟨x, hx_mem⟩ := hcycle.nonempty_support
  have hx : σ x ≠ x := σ.mem_support.mp hx_mem
  have hcycOn : σ.IsCycleOn (Finset.univ : Finset α) :=
    hsupport ▸ σ.coe_support_eq_set_support ▸ hcycle.isCycleOn
  set p : G.Walk (σ x) x := (Walk.iterate (↑σ) hadj (σ x) (Fintype.card α - 1)).copy rfl (by
    change (↑σ : α → α)^[Fintype.card α - 1 + 1] x = x
    rw [Nat.sub_add_cancel (by lia), Equiv.Perm.iterate_eq_pow,
      ← Finset.card_univ, hcycOn.pow_card_apply (Finset.mem_univ x)])
  refine ⟨x, .cons (hadj x) p, Walk.cons_isHamiltonianCycle_iff (hadj x) p |>.mpr ⟨?_, ?_⟩⟩
  · -- p is a Hamiltonian path: visits every vertex exactly once.
    rw [Walk.isHamiltonian_iff_isPath_and_length_eq]
    refine ⟨?_, by simp [p]⟩
    rw [Walk.isPath_def]
    simp only [p, Walk.support_copy, Walk.support_iterate,
      show Fintype.card α - 1 + 1 = Fintype.card α by lia]
    have hsx : σ (σ x) ≠ σ x := σ.injective.ne hx
    have hcard : Fintype.card α = (cycleOf σ (σ x)).support.card := by
      rw [hcycle.cycleOf_eq hsx, hsupport, Finset.card_univ]
    rw [hcard, ← List.range_map_iterate]
    simp only [Equiv.Perm.iterate_eq_pow]
    rw [← σ.toList_eq_range_map_pow]
    exact σ.nodup_toList (σ x)
  · -- The closure edge `s(x, σ x)` is not already used in `p`.
    simp only [p, Walk.edges_copy, Walk.edges_iterate]
    rw [List.mem_map]
    rintro ⟨i, hi, heq⟩
    rw [List.mem_range] at hi
    simp only [Equiv.Perm.iterate_eq_pow, ← mul_apply, ← pow_succ] at heq
    exact hcycOn.sym2_pow_apply_ne (Finset.mem_univ x) (by lia)
      (by rw [Finset.card_univ]; lia) (by rw [Finset.card_univ]; lia) heq

end SimpleGraph
