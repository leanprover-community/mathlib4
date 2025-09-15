/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Euler characteristic of chain complexes

This file defines the Euler characteristic of a chain complex.

## Main definitions

* `ChainComplex.boundedEulerChar`: The Euler characteristic of a chain complex up to index `n`,
  defined as the alternating sum `∑_{k=0}^{n-1} (-1)^k rank(C_k)` of the ranks of the chain groups.
* `ChainComplex.eulerChar`: The Euler characteristic as an infinite sum over all natural numbers,
  defined for chain complexes that eventually vanish (i.e., have finrank 0 beyond some point).

## Main results

* `ChainComplex.boundedEulerChar_zero`: The bounded Euler characteristic at 0 is 0 (empty sum).
* `ChainComplex.boundedEulerChar_succ`: Recursive formula for the bounded Euler characteristic.
* `ChainComplex.eulerChar_eq_boundedEulerChar`: The Euler characteristic equals the bounded
  Euler characteristic for sufficiently large bounds.

-/

namespace ChainComplex

variable {R : Type*} [Ring R]

/-- The bounded Euler characteristic of a chain complex up to index `n`, defined as the alternating
sum `∑_{k=0}^{n-1} (-1)^k rank(C_k)` of the ranks of the chain groups from index 0 to n-1.
This is most commonly used when the base ring is a field (where rank means dimension)
or a principal ideal domain. -/
noncomputable def boundedEulerChar (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, (-1 : ℤ)^k * Module.finrank R (C.X k)

@[simp]
theorem eulerChar_zero (C : ChainComplex (ModuleCat R) ℕ) :
    boundedEulerChar C 0 = 0 := by
  simp [boundedEulerChar]

theorem eulerChar_succ (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    boundedEulerChar C (n + 1) = boundedEulerChar C n + (-1 : ℤ)^n * Module.finrank R (C.X n) := by
  simp [boundedEulerChar, Finset.sum_range_succ]

/-- The Euler characteristic of a chain complex, defined as an infinite sum.
This is the alternating sum `∑_{k=0}^∞ (-1)^k rank(C_k)` of the ranks of all chain groups.
The sum may not converge in general. -/
noncomputable def eulerChar (C : ChainComplex (ModuleCat R) ℕ) : ℤ :=
  ∑' k : ℕ, (-1 : ℤ)^k * Module.finrank R (C.X k)

/-- If a chain complex eventually vanishes, then the Euler characteristic equals
the bounded Euler characteristic for any n beyond where the complex vanishes. -/
theorem eulerChar_eq_boundedEulerChar (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (hn : ∀ k ≥ n, Module.finrank R (C.X k) = 0) :
    eulerChar C = boundedEulerChar C n := by
  simp only [eulerChar, boundedEulerChar]
  -- The key is that the infinite sum equals the finite sum when all terms beyond n are zero
  have h_zero : ∀ k ∉ Finset.range n, (-1 : ℤ)^k * Module.finrank R (C.X k) = 0 := by
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    have : Module.finrank R (C.X k) = 0 := hn k hk
    simp [this]
  rw [tsum_eq_sum h_zero]

end ChainComplex
