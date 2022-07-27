/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Mathlib.Tactic.Use
import Mathlib.Tactic.Basic

example : ∃ x : Nat, x = x := by use 42

example : ∃ x : Nat, ∃ y : Nat, x = y := by use 42, 42

example : ∃ x : String × String, x.1 = x.2 := by use ("a", "a")

example : ∃ x : Nat, x = x := by
  use ?_
  exact 42
  rfl

example (α : Type) : ∃ S : List α, S = S :=
by use ∅

example : ∃ x : Int, x = x :=
by use 42

example : ∃ a b c : Int, a + b + c = 6 :=
by use 1, 2, 3

example : ∃ p : Int × Int, p.1 = 1 :=
by use ⟨1, 42⟩

-- FIXME Failing tests ported from mathlib3

-- example : ∃ (n : Nat) (h : n > 0), n = n :=
-- by
--   use 1
--   -- goal should now be `1 > 0 ∧ 1 = 1`, whereas it would be `∃ (H : 1 > 0), 1 = 1` after existsi 1.
--   guard_target == 1 > 0 ∧ 1 = 1
--   exact ⟨Nat.zero_lt_one, rfl⟩

-- example : Σ x y : Int, (Int × Int) × Int :=
-- by use 1, 2, 3, 4, 5

-- inductive foo
-- | mk : Nat → Bool × Nat → Nat → foo

-- example : foo :=
-- by use 100, true, 4, 3
