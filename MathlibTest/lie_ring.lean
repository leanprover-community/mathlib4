/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Guo ZiXun
-/
import Mathlib.Tactic.LieAlgebra.Basic
import Mathlib.Tactic.LieAlgebra.LieRingNF

/-! # Tests for tactics related to Lie algebra -/

section

variable {R L : Type*} [LieRing L]

example (a b c : L) : ⁅⁅a, b⁆, c⁆ = ⁅⁅a, c⁆, b⁆ + ⁅a, ⁅b, c⁆⁆ := by lie_ring
example (a b c : L) : ⁅⁅a, b⁆, c⁆ + ⁅⁅b, c⁆, a⁆ + ⁅⁅c, a⁆, b⁆ = 0 := by lie_ring
example (a b c : L) : ⁅a, ⁅b, c⁆⁆ - ⁅b, ⁅a, c⁆⁆ = ⁅⁅a, b⁆, c⁆ := by lie_ring
example (a : L) : ⁅a, a⁆ = 0 := by lie_ring
example (a b : L) : ⁅a, b⁆ = -⁅b, a⁆ := by lie_ring
example (a b c : L) :
    ⁅(2 : ℤ) • a, ⁅-3 • b + c, c⁆⁆ - ⁅b, ⁅-a, 6 • c + a⁆⁆ = ⁅⁅3 • a, -((-2) • -b)⁆, c⁆ := by lie_ring

variable (a b c : L)
/--
info: the term is reduced to 6 • ⁅⁅a, c⁆, ⁅a, ⁅c, b⁆⁆⁆ + (6 • ⁅⁅a, c⁆, ⁅⁅a, b⁆, c⁆⁆ + 0)
-/
#guard_msgs in
#LieReduce ⁅⁅-2 • a, c⁆, ⁅b, ⁅3 • a, c⁆⁆⁆

/-- info: Try this: 6 • ⁅⁅a, b⁆, ⁅⁅a, c⁆, ⁅b, c⁆⁆⁆ + (6 • ⁅⁅a, b⁆, ⁅⁅⁅a, c⁆, c⁆, b⁆⁆ + 0)-/
#guard_msgs in example : (lie_reduce% ⁅⁅2 • a, b⁆, ⁅⁅b, ⁅a, -3 • c⁆⁆, c⁆⁆) = ⁅⁅2 • a, b⁆, ⁅⁅b, ⁅a, -3 • c⁆⁆, c⁆⁆ := by
  lie_ring

/-- info: Try this: -1 • ⁅⁅a, c⁆, ⁅a, ⁅c, b⁆⁆⁆ + (-1 • ⁅⁅a, c⁆, ⁅⁅a, b⁆, c⁆⁆ + 0)-/
#guard_msgs in example : ⁅⁅a, c⁆, ⁅b, ⁅a, c⁆⁆⁆ = lie_reduce% ⁅⁅a, c⁆, ⁅b, ⁅a, c⁆⁆⁆ := by lie_ring

end

-- Add tests that shows what `lie_ring_nf` does
-- Add tests to make sure config works
-- Add tests for lie_algebra

-- section tests

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

example (a b c : L) (r r' : R) : ⁅r • ⁅r • a, r' • b⁆, r' • c⁆
  = (r' * (r * (r' * r))) • ⁅⁅a, b⁆, c⁆ := by
  sorry

-- example (a b c : L) : ⁅⁅a, b⁆, c⁆ = ⁅⁅a, c⁆, b⁆ + ⁅a, ⁅b, c⁆⁆ := by
--   lie_ring_nf

example (a b c : L) : ⁅⁅a, b⁆, c⁆ + ⁅⁅b, c⁆, a⁆ + ⁅⁅c, a⁆, b⁆ = 0 := by
  -- lie_ring_nf
  sorry

example (a b : L) : (2 : ℤ) • a + (2 : ℤ) • b = (2 : ℤ) • (a + b) := by
  -- lie_ring_nf
  sorry

example (a b c : L) : ⁅⁅a, c⁆, ⁅b, ⁅a, c⁆⁆⁆ = 0 := by
  lie_ring_nf (config := {strategy := .raw})
  sorry

example (a b : L) (f : L → L) (g : L → L) (h : f ⁅a, a⁆ = 0) : f (f ⁅b, b⁆) = 0 := by
  lie_ring_nf 
  sorry

-- example (a : L) : ⁅a, a⁆ = 0 := by
--   lie_ring_nf

-- example (a b : L) : ⁅a, b⁆ = -⁅b, a⁆ := by
--   lie_ring_nf
--   -- module

-- end tests
