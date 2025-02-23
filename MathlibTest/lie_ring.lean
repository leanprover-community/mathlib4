/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
import Mathlib.Tactic.LieAlgebra.Basic

variable {R L : Type*} [LieRing L]

/--
error: tactic lie_ring failed, expressions are not equal, the left hand side is simplified to 1 • ⁅a, ⁅b, c⁆⁆ +
  (1 • ⁅⁅a, c⁆, b⁆ + 0) but the right hand side is simplified to 1 • a + (1 • ⁅a, ⁅b, c⁆⁆ + (1 • ⁅⁅a, c⁆, b⁆ + 0))
-/
#guard_msgs in
example (a b c : L) : ⁅⁅a, b⁆, c⁆ = ⁅⁅a, c⁆, b⁆ + ⁅a, ⁅b, c⁆⁆ + a := by
  lie_ring
  sorry

example (a b c : L) : ⁅⁅a, b⁆, c⁆ + ⁅⁅b, c⁆, a⁆ + ⁅⁅c, a⁆, b⁆ = 0 := by
  lie_ring

example (a : L) : ⁅a, a⁆ = 0 := by
  lie_ring

example (a b : L) : ⁅a, b⁆ = -⁅b, a⁆ := by
  lie_ring

example (a b c : L) :
    ⁅(2 : ℤ) • a, ⁅-3 • b, c⁆⁆ - ⁅b, ⁅-a, 6 • c⁆⁆ = ⁅⁅3 • a, -((-2) • -b)⁆, c⁆ := by
  lie_ring

example (a : L) : 0 • a = 0 := by
  lie_ring

variable (a b c : L)

/--
info: the term is reduced to -1 • ⁅⁅a, c⁆, ⁅a, ⁅c, b⁆⁆⁆ + (-1 • ⁅⁅a, c⁆, ⁅⁅a, b⁆, c⁆⁆ + 0)
-/
#guard_msgs in
#LieReduce ⁅⁅a, c⁆, ⁅b, ⁅a, c⁆⁆⁆
