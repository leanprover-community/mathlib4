/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Std.Tactic.GuardExpr
import Mathlib.Tactic.DSimp

example : 1 + 0 = 1 := by
  conv =>
    lhs
    guard_target =ₐ 1 + 0
    dsimp only
    guard_target =ₐ 1 + 0
    dsimp
    guard_target =ₐ 1

example (a : Nat) : 0 + 0 = a - a := by
  conv =>
    lhs
    guard_target =ₐ 0 + 0
    dsimp
    guard_target =ₐ 0
    rw [← Nat.sub_self a]
    guard_target =ₐ a - a
