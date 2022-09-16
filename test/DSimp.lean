/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import Mathlib.Tactic.DSimp

example : (1 + 0) = 1 := by
  conv =>
    lhs
    dsimp

example (a : Nat): (0 + 0) = a - a := by
  conv =>
    lhs
    dsimp
    rw [←Nat.sub_self a]
