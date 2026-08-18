/-
Copyright (c) 2026 Nathanael Thompson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathanael Thompson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Algebra.Order.Ring.Rat

/-!
# Simple random walk on a graph

This file produces a transition matrix from a graph. Row `v` of `SimpleGraph.walkMatrix` is the
uniform distribution on the neighbours of `v`, so the matrix describes the Markov chain that
steps from a vertex to a uniformly random neighbour. It is the row-normalised form of
`SimpleGraph.adjMatrix`: dividing row `v` by `G.degree v` turns adjacency counts into transition
probabilities.

A state of the chain is a row vector `V → ℚ`, and one step is `x ᵥ* G.walkMatrix`. Since
`Matrix.rowStochastic` is a `Submonoid`, the `n`-step matrix is `G.walkMatrix ^ n`.

## Main definitions

- `SimpleGraph.walkMatrix`: the transition matrix of the simple random walk.
- `SimpleGraph.degreeDist`: the distribution assigning `v` probability proportional to
  `G.degree v`.

## Main statements

- `SimpleGraph.walkMatrix_mem_rowStochastic`: the transition matrix is row stochastic.
- `SimpleGraph.degreeDist_vecMul_walkMatrix`: the degree distribution is stationary.

## Implementation notes

The walk is only well defined at vertices with at least one neighbour, so the results take a
hypothesis `∀ v, ¬ G.IsIsolated v`.

Every transition probability is of the form `(G.degree v)⁻¹`, so the matrix is valued in `ℚ`.
-/

@[expose] public section

open Finset Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The transition matrix of the simple random walk on `G`: from a vertex `v`, move to a
uniformly random neighbour of `v`. -/
def walkMatrix : Matrix V V ℚ :=
  Matrix.of fun v w => if G.Adj v w then (G.degree v : ℚ)⁻¹ else 0

/-- The degree distribution of `G`: the probability of a vertex `v` is proportional to
`G.degree v`. This is the stationary distribution of the simple random walk. -/
def degreeDist : V → ℚ := fun v => (G.degree v : ℚ) / (2 * #G.edgeFinset)

variable {G}

theorem walkMatrix_apply (v w : V) :
    G.walkMatrix v w = if G.Adj v w then (G.degree v : ℚ)⁻¹ else 0 := rfl

/-- If `G` has no isolated vertices then every degree is nonzero in `ℚ`. -/
theorem degree_ne_zero (hG : ∀ v, ¬ G.IsIsolated v) (v : V) : (G.degree v : ℚ) ≠ 0 := by
  have : G.degree v ≠ 0 := by
    simpa [degree_eq_zero_iff_notMem_support,
           ← mem_support_iff_not_isIsolated] using hG v
  simpa using this

theorem walkMatrix_mem_rowStochastic [DecidableEq V] (hG : ∀ v, ¬ G.IsIsolated v) :
    G.walkMatrix ∈ rowStochastic ℚ V := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun v w => ?_, fun v => ?_⟩
  · rw [walkMatrix_apply]
    split <;> positivity
  · simp only [walkMatrix_apply]
    rw [← sum_filter, ← neighborFinset_eq_filter, sum_const,
        card_neighborFinset_eq_degree, nsmul_eq_mul,
        mul_inv_cancel₀ (degree_ne_zero hG v)]

/-- The degree distribution is stationary for the simple random walk. -/
theorem degreeDist_vecMul_walkMatrix (hG : ∀ v, ¬ G.IsIsolated v) :
    G.degreeDist ᵥ* G.walkMatrix = G.degreeDist := by
  classical
  funext w
  simp only [vecMul, dotProduct, degreeDist, walkMatrix_apply]
  have key : ∀ i, (G.degree i : ℚ) / (2 * #G.edgeFinset) *
      (if G.Adj i w then ((G.degree i : ℚ))⁻¹ else 0)
      = if G.Adj i w then (1 : ℚ) / (2 * #G.edgeFinset) else 0 := by
    intro i
    split
    · field_simp [degree_ne_zero hG i]
    · ring
  rw [Finset.sum_congr rfl (fun i _ => key i), ← sum_filter, sum_const]
  have hcard : #{a | G.Adj a w} = G.degree w := by
    rw [← card_neighborFinset_eq_degree]
    congr 1
    ext a
    simp [mem_neighborFinset, adj_comm]
  rw [hcard, nsmul_eq_mul]
  ring

end SimpleGraph
