/-
Copyright (c) 2025 Alastair Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Ruben Van de Velde
-/
module

public import Mathlib.NumberTheory.VonMangoldt

/-!
# Chebyshev functions

This file defines the Chebyshev functions `theta` and `psi`.
These give logarithmically weighted sums of primes and prime powers.

## Main definitions

- `Chebyshev.psi` gives the sum of `ArithmeticFunction.vonMangoldt`
- `Chebyshev.theta` gives the sum of `log p` over primes

## Notation

We introduce the scoped notations `θ` and `ψ` for the Chebyshev functions.

## References

Parts of this file were upstreamed from the PrimeNumberTheoremAnd project by Kontorovich et al, https://github.com/alexKontorovich/PrimeNumberTheoremAnd.

## TODOS

- Upstream the results relating `theta` and `psi` to each other and to the prime counting function.
- Prove Chebyshev's estimates.
-/
@[expose] public section

open Nat hiding log
open Finset Real
open ArithmeticFunction hiding log

namespace Chebyshev

/-- The sum of `ArithmeticFunction.vonMangoldt` over integers `n ≤ x`. -/
noncomputable def psi (x : ℝ) : ℝ :=
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n

@[inherit_doc]
scoped notation "ψ" => Chebyshev.psi

/-- The sum of `log p` over primes `p ≤ x`. -/
noncomputable def theta (x : ℝ) : ℝ :=
    ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p

@[inherit_doc]
scoped notation "θ" => Chebyshev.theta

theorem psi_nonneg (x : ℝ) : 0 ≤ ψ x :=
  sum_nonneg fun _ _ ↦ (by simp)

theorem theta_nonneg (x : ℝ) : 0 ≤ θ x := by
  refine sum_nonneg fun n hn ↦ log_nonneg ?_
  simp_all
  linarith

theorem psi_eq_zero_of_lt_two {x : ℝ} (hx : x < 2) : ψ x = 0 := by
  apply sum_eq_zero fun n hn ↦ ?_
  simp only [mem_Ioc] at hn
  convert vonMangoldt_apply_one
  have := lt_of_le_of_lt (le_floor_iff' hn.1.ne.symm |>.mp hn.2) hx
  norm_cast at this
  linarith

theorem theta_eq_zero_of_lt_two {x : ℝ} (hx : x < 2) : θ x = 0 := by
  apply sum_eq_zero fun n hn ↦ ?_
  convert log_one
  simp only [mem_filter, mem_Ioc] at hn
  have := lt_of_le_of_lt (le_floor_iff' hn.1.1.ne.symm |>.mp hn.1.2) hx
  norm_cast at ⊢ this
  linarith

end Chebyshev
