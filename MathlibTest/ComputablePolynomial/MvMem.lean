/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
import Mathlib.Tactic.ComputablePolynomial.MvMem

/-!
# Tests for `mv_mem`

Axiom-free ideal membership for `MvPolynomial` via kernel-reducible multidivisor reduction.
-/

open MvPolynomial


-- `x·y + y` is in `⟨x, y⟩` (reduces: `−y·x` then `−1·y` to `0`):
example : (X 0 * X 1 + X 1 : MvPolynomial (Fin 2) ℤ) ∈ Ideal.span {X 0, X 1} := by mv_mem

-- `x² − y ∈ ⟨x, y⟩` (reduces by `x` then by `y`):
theorem mem_demo : (X 0 ^ 2 - X 1 : MvPolynomial (Fin 2) ℤ) ∈ Ideal.span {X 0, X 1} := by mv_mem
/-- info: 'mem_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_demo
