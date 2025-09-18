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
info: the term is reduced to -6 • ⁅⁅a, b⁆, ⁅⁅a, b⁆, c⁆⁆ + (6 • ⁅⁅⁅a, b⁆, ⁅a, c⁆⁆, b⁆ + (-6 • ⁅⁅⁅a, b⁆, b⁆, ⁅a, c⁆⁆ + 0))
-/
#guard_msgs in
#LieReduce ⁅⁅-2 • a, b⁆, ⁅a, ⁅3 • b, c⁆⁆⁆

/-- info: Try this: 6 • ⁅⁅⁅⁅a, b⁆, ⁅a, c⁆⁆, b⁆, c⁆ +
  (-6 • ⁅⁅⁅⁅a, b⁆, b⁆, ⁅a, c⁆⁆, c⁆ + (-6 • ⁅⁅⁅⁅a, b⁆, c⁆, ⁅a, c⁆⁆, b⁆ + (6 • ⁅⁅⁅⁅a, b⁆, c⁆, b⁆, ⁅a, c⁆⁆ + 0))) -/
#guard_msgs in example : (lie_reduce% ⁅⁅2 • a, b⁆, ⁅⁅b, ⁅a, -3 • c⁆⁆, c⁆⁆) = ⁅⁅2 • a, b⁆, ⁅⁅b, ⁅a, -3 • c⁆⁆, c⁆⁆ := by
  lie_ring

/-- info: Try this: 1 • ⁅⁅a, c⁆, ⁅⁅a, c⁆, b⁆⁆ + (-1 • ⁅⁅⁅a, c⁆, ⁅a, b⁆⁆, c⁆ + (1 • ⁅⁅⁅a, c⁆, c⁆, ⁅a, b⁆⁆ + 0)) -/
#guard_msgs in example :  ⁅⁅a, c⁆, ⁅a, ⁅c, b⁆⁆⁆  = lie_reduce% ⁅⁅a, c⁆, ⁅a, ⁅c, b⁆⁆⁆ := by lie_ring

end

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

example (a b c : L) (r r' : R) : ⁅r • ⁅r • a, r' • b⁆, r' • c⁆
    = (r' * r) • (⁅r • a, ⁅b, r' • c⁆⁆ + ⁅⁅a, r • c⁆, r' • b⁆) := by
  lie_algebra

example (a b c : L) : ⁅⁅a, b⁆, c⁆ = ⁅⁅a, c⁆, b⁆ + ⁅a, ⁅b, c⁆⁆ := by
  lie_ring_nf
  guard_target = ⁅⁅a, b⁆, c⁆ = ⁅⁅a, c⁆, b⁆ + (⁅⁅a, b⁆, c⁆ + -⁅⁅a, c⁆, b⁆)
  abel

example (a b c : L) : ⁅⁅a, b⁆, c⁆ = ⁅⁅a, c⁆, b⁆ + ⁅a, ⁅b, c⁆⁆ := by
  lie_ring_nf (config := {mode := .raw})
  guard_target = (1 : ℤ) • ⁅⁅a, b⁆, c⁆ + 0 = (1 : ℤ) • ⁅⁅a, c⁆, b⁆ + 0 + ((1 : ℤ) • ⁅⁅a, b⁆, c⁆ + (-1 • ⁅⁅a, c⁆, b⁆ + 0))
  abel

example (a b c : L) : ⁅⁅a, b⁆, c⁆ = ⁅⁅a, c⁆, b⁆ + ⁅a, ⁅b, c⁆⁆ := by
  let d := c
  nth_rw 2 [show c = d from rfl]
  guard_target = ⁅⁅a, b⁆, c⁆ = ⁅⁅a, d⁆, b⁆ + ⁅a, ⁅b, c⁆⁆
  -- When `zetaDelta` is set to false (as default), `let` is not unfolded
  lie_ring_nf (config := {zetaDelta := false})
  guard_target = ⁅⁅a, b⁆, c⁆ = ⁅⁅a, d⁆, b⁆ + (⁅⁅a, b⁆, c⁆ + -⁅⁅a, c⁆, b⁆)
  -- When `zetaDelta` is set to true, `let` is unfolded
  lie_ring_nf (config := {zetaDelta := true})
  guard_target = ⁅⁅a, b⁆, c⁆ = ⁅⁅a, c⁆, b⁆ + (⁅⁅a, b⁆, c⁆ + -⁅⁅a, c⁆, b⁆)
  abel

example (a b c : L) : ⁅⁅a, b⁆, c⁆ + ⁅⁅b, c⁆, a⁆ + ⁅⁅c, a⁆, b⁆ = 0 := by
  lie_ring_nf
  guard_target = ⁅⁅a, b⁆, c⁆ + (-⁅⁅a, b⁆, c⁆ + ⁅⁅a, c⁆, b⁆) + -⁅⁅a, c⁆, b⁆ = 0
  abel
