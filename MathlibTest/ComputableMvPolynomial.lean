/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
import Mathlib.Tactic.ComputablePolynomial.MvSparsePoly
import Mathlib.Tactic.ComputablePolynomial.MvReflect

/-!
# Tests for the computable multivariate polynomial tactics

Examples exercising `mv_decide` (ring identities of `MvPolynomial`) and `mv_mem` (ideal
membership). Each is proved **axiom-free**: the `#print axioms` checks below confirm only
`[propext, Classical.choice, Quot.sound]` — in particular no `Lean.ofReduceBool` and no
`native_decide`.
-/

open MvPolynomial

/-! ## `mv_decide` — `MvPolynomial` ring identities by reflection -/

-- Reordering and cancellation (additive):
example : (X 0 + X 1 + X 2 : MvPolynomial (Fin 3) ℤ) = X 2 + X 0 + X 1 := by mv_decide
example : (X 0 + X 1 - X 1 : MvPolynomial (Fin 2) ℤ) = X 0 := by mv_decide

-- Multiplication, with like terms merging to coefficient `2`:
example : ((X 0 + X 1) ^ 2 : MvPolynomial (Fin 2) ℤ) = X 0 ^ 2 + C 2 * (X 0 * X 1) + X 1 ^ 2 := by
  mv_decide

-- Difference of squares — the cross terms cancel to a *zero* coefficient (dropped by the
-- `filter (·.2 ≠ 0)` in `eq_of_core`):
example : ((X 0 + X 1) * (X 0 - X 1) : MvPolynomial (Fin 2) ℤ) = X 0 ^ 2 - X 1 ^ 2 := by mv_decide

-- A factored form equals its expansion:
example : ((X 0 + X 1) ^ 2 * (X 0 - X 1) : MvPolynomial (Fin 2) ℤ)
    = (X 0 + X 1) * (X 0 ^ 2 - X 1 ^ 2) := by mv_decide

-- The trust check: this proof depends only on the standard logical axioms — crucially **not**
-- `Lean.ofReduceBool` (which `native_decide` would add).
theorem sq_expand : ((X 0 + X 1) ^ 2 : MvPolynomial (Fin 2) ℤ)
    = X 0 ^ 2 + C 2 * (X 0 * X 1) + X 1 ^ 2 := by mv_decide
#print axioms sq_expand

-- bare numerals (no `C`) also work, axiom-free:
example : ((X 0 + 1) * (X 0 + 2) : MvPolynomial (Fin 1) ℤ) = X 0 ^ 2 + 3 * X 0 + 2 := by
  mv_decide

/-! ## `mv_mem` — ideal membership, axiom-free -/

-- `x·y + y` is in `⟨x, y⟩` (reduces: `−y·x` then `−1·y` to `0`):
example : (X 0 * X 1 + X 1 : MvPolynomial (Fin 2) ℤ) ∈ Ideal.span {X 0, X 1} := by mv_mem

-- `x² − y ∈ ⟨x, y⟩` (reduces by `x` then by `y`):
theorem mem_demo : (X 0 ^ 2 - X 1 : MvPolynomial (Fin 2) ℤ) ∈ Ideal.span {X 0, X 1} := by mv_mem
#print axioms mem_demo
