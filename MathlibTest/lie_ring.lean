/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Guo ZiXun
-/
import Mathlib.Tactic.LieAlgebra.Basic
import Mathlib.Tactic.LieAlgebra.LieRingNF

/-! # Tests for the lie_ring tactic -/

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
info: the term is reduced to 6 • ⁅⁅a, c⁆, ⁅a, ⁅c, b⁆⁆⁆ + (6 • ⁅⁅a, c⁆, ⁅⁅a, b⁆, c⁆⁆ + 0)
-/
#guard_msgs in
#LieReduce ⁅⁅-2 • a, c⁆, ⁅b, ⁅3 • a, c⁆⁆⁆

/--
info: Try this: 6 • ⁅⁅a, b⁆, ⁅⁅a, c⁆, ⁅b, c⁆⁆⁆ + (6 • ⁅⁅a, b⁆, ⁅⁅⁅a, c⁆, c⁆, b⁆⁆ + 0)
-/
#guard_msgs in
example (a b c : L) :
    (lie_reduce% ⁅⁅2 • a, b⁆, ⁅⁅b, ⁅a, -3 • c⁆⁆, c⁆⁆) = ⁅⁅2 • a, b⁆, ⁅⁅b, ⁅a, -3 • c⁆⁆, c⁆⁆ := by
  lie_ring

example : ⁅⁅a, c⁆, ⁅b, ⁅a, c⁆⁆⁆ = lie_reduce% ⁅⁅a, c⁆, ⁅b, ⁅a, c⁆⁆⁆ := by
  lie_ring

section tests

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

example (a b c : L) (r r' : R) : ⁅r • ⁅r • a, r' • b⁆, r' • c⁆
  = (r' * (r * (r' * r))) • ⁅⁅a, b⁆, c⁆ := by
  lie_algebra

example (a b c : L) : ⁅⁅a, b⁆, c⁆ = ⁅⁅a, c⁆, b⁆ + ⁅a, ⁅b, c⁆⁆ := by
  lie_ring1_nf

example (a b c : L) : ⁅⁅a, b⁆, c⁆ + ⁅⁅b, c⁆, a⁆ + ⁅⁅c, a⁆, b⁆ = 0 := by
  lie_ring1_nf

example (a b : L) : (2 : ℤ) • a + (2 : ℤ) • b = (2 : ℤ) • (a + b) := by
  lie_ring1_nf
  -- sorry

example (a : L) : ⁅a, a⁆ = 0 := by
  lie_ring_nf!

example (a b : L) : ⁅a, b⁆ = -⁅b, a⁆ := by
  lie_ring1_nf
  -- module

example (a b c : L) : ⁅a, ⁅b, c⁆⁆ - ⁅b, ⁅a, c⁆⁆ = ⁅⁅a, b⁆, c⁆ := by
  lie_algebra

example (a : L) : (1 : R) • a + (-1 : R) • a = 0:= by
  module

end tests
