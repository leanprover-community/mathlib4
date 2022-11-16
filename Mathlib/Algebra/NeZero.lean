/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/

import Mathlib.Logic.Basic
import Mathlib.Init.ZeroOne
import Mathlib.Init.Algebra.Order

/-!
# `NeZero` typeclass

We create a typeclass `NeZero n` which carries around the fact that `(n : R) ≠ 0`.

## Main declarations

* `NeZero`: `n ≠ 0` as a typeclass.
-/

/-- A type-class version of `n ≠ 0`.  -/
class NeZero {R} [Zero R] (n : R) : Prop where
  /-- The proposition that `n` is not zero. -/
  out : n ≠ 0

theorem NeZero.ne {R} [Zero R] (n : R) [h : NeZero n] : n ≠ 0 :=
  h.out

theorem neZero_iff {R : Type _} [Zero R] {n : R} : NeZero n ↔ n ≠ 0 :=
  ⟨fun h => h.out, NeZero.mk⟩
#align ne_zero_iff neZero_iff

theorem not_neZero {R : Type _} [Zero R] {n : R} : ¬NeZero n ↔ n = 0 := by simp [neZero_iff]
#align not_ne_zero not_neZero

theorem eq_zero_or_neZero {α} [Zero α] (a : α) : a = 0 ∨ NeZero a :=
  (eq_or_ne a 0).imp_right NeZero.mk
#align eq_zero_or_ne_zero eq_zero_or_neZero

namespace NeZero

variable {M : Type _} {x : M}

instance succ : NeZero (n + 1) := ⟨n.succ_ne_zero⟩

theorem of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x := ⟨ne_of_gt h⟩

end NeZero
