/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Mathlib.Tactic.Use
import Mathlib.Tactic.Basic

namespace UseTests

set_option autoImplicit true

example : ∃ x : Nat, x = x := by use 42

-- Since `Eq` is an inductive type, `use` naturally handles it when applying the constructor.
/-- error: too many arguments supplied to `use` -/
#guard_msgs in
example : ∃ x : Nat, x = x := by use 42, rfl

example : ∃ x : Nat, x = x := by use! 42

example (h : 42 = y) : ∃ x : Nat, x = y := by use 42, h

-- `trivial` uses `assumption`
example (h : 42 = y) : ∃ x : Nat, x = y := by use 42

-- Check that `use` inserts a coercion:
/-- info: Try this: Exists.intro (↑n) (Eq.refl ↑n) -/
#guard_msgs (info) in
example (n : Fin 3) : ∃ x : Nat, x = x := show_term by use n

example : ∃ x : Nat, ∃ y : Nat, x = y := by use 42, 42

/--
error: failed to synthesize
  OfNat (Nat × Nat) 42
numerals are polymorphic in Lean, but the numeral `42` cannot be used in a context where the expected type is
  Nat × Nat
due to the absence of the instance above

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example : ∃ p : Nat × Nat, p.1 = p.2 := by use 42; sorry

example : ∃ p : Nat × Nat, p.1 = p.2 := by use! 42, 42

example : ∃ p : Nat × Nat, p.1 = p.2 := by use! (42, 42)

example (r : Nat → Nat → Prop) (h : ∀ x, r x x) :
    ∃ p : Nat × Nat, r p.1 p.2 := by use! 42; use! 42; apply h

example (r : Nat → Nat → Prop) (h : ∀ x, r x x) :
    ∃ p : Nat × Nat, r p.1 p.2 := by use! 42, 42; apply h

example (r : Nat → Nat → Prop) (h : ∀ x, r x x) :
    ∃ p : Nat × Nat, r p.1 p.2 := by use! 42, 42, h _

example : ∃ x : String × String, x.1 = x.2 := by use ("a", "a")

example : ∃ x : String × String, x.1 = x.2 := by use! "a", "a"

-- This example is why `use` always tries applying the constructor before refining.
example : ∃ x : Nat, x = x := by
  use ?_
  exact 42

example (α : Type) : ∃ S : List α, S = S := by use ∅

example : ∃ x : Int, x = x := by use 42

example : ∃ a b c : Int, a + b + c = 6 := by
  use 1, 2, 3
  rfl

example : ∃ p : Int × Int, p.1 = 1 := by use ⟨1, 42⟩

example : ∃ p : Int × Int, p.1 = 1 := by use! 1, 42

example : ∃ n : Int, n * 3 = 3 * 2 := by
  use 2
  rfl

example : Σ _x _y : Int, Int × Int × Int := by
  use 1, 2, 3, 4, 5

example : Σ _x _y : Int, (Int × Int) × Int := by
  use! 1, 2, 3, 4, 5

-- There are two constructors, so applying a constructor fails and it tries to just refine
/--
error: failed to synthesize
  OfNat (Option Nat) 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Option Nat
due to the absence of the instance above

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example : Option Nat := by use 1

/--
error: failed to synthesize
  OfNat (Nat → Nat) 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Nat → Nat
due to the absence of the instance above

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example : Nat → Nat := by use 1

inductive foo
| mk : Nat → Bool × Nat → Nat → foo

example : foo := by
  use 100, ⟨true, 4⟩, 3

example : foo := by
  use! 100, true, 4, 3

/-- info: Try this: foo.mk 100 (true, 4) 3 -/
#guard_msgs in
-- `use` puts placeholders after the current goal
example : foo := show_term by
  use ?x, ⟨?b, 4⟩
  exact (3 : Nat)
  exact (100 : Nat)
  exact true

/-- info: Try this: foo.mk 100 (true, 4) 3 -/
#guard_msgs in
-- `use` puts placeholders after the current goal
example : foo := show_term by
  -- Type ascriptions keep refinement from occurring before applying the constructor
  use! (?x : Nat), (?b : Bool), 4
  exact (3 : Nat)
  exact (100 : Nat)
  exact true

-- `use!` is helpful for auto-flattening quantifiers over subtypes
example : ∃ p : {x : Nat // 0 < x}, 1 < p.1 := by use! 2 <;> decide

inductive Baz : Nat → Nat → Prop
  | cons (x : Nat) : Baz 0 x

example : Baz 0 3 := by use _

example : Baz 0 3 := by use 3

/--
error: argument is not definitionally equal to inferred value
  3
-/
#guard_msgs in
example : Baz 0 3 := by use 4

-- Could not apply constructor due to defeq check
/--
error: type mismatch
  3
has type
  Nat : Type
but is expected to have type
  Baz 1 3 : Prop
-/
#guard_msgs in
example : Baz 1 3 := by use (3 : Nat)

structure DecidableType where
  (α : Type)
  [deq : DecidableEq α]

-- Auto-synthesizes instance
example : DecidableType := by
  use Nat

example (β : Type) [DecidableEq β] : DecidableType := by
  use β

-- Leaves instances as extra goals when synthesis fails
noncomputable
example (β : Type) : DecidableType := by
  use β
  guard_target = DecidableEq β
  apply Classical.typeDecidableEq

-- https://github.com/leanprover-community/mathlib4/issues/5072
example (n : Nat) : Nat := by use n

structure Embedding (α β : Sort _) where
  toFun : α → β
  inj : ∀ x y, toFun x = toFun y → x = y

example (α : Type u) : Embedding α α × Unit := by
  constructor
  -- testing that `use` actually focuses on the main goal
  use id
  · simp
  constructor


-- FIXME Failing tests ported from mathlib3

-- Note(kmill): mathlib3 `use` would try to rewrite any lingering existentials with
-- `exists_prop` to turn them into conjunctions. It did not do this recursively.

set_option linter.style.longLine false in
-- example : ∃ (n : Nat) (h : n > 0), n = n := by
--   use 1
--   -- goal should now be `1 > 0 ∧ 1 = 1`, whereas it would be `∃ (H : 1 > 0), 1 = 1` after existsi 1.
--   guard_target = 1 > 0 ∧ 1 = 1
--   exact ⟨Nat.zero_lt_one, rfl⟩

-- This feature might not be useful anymore since bounded `Exists` already uses a conjunction.
example : ∃ n > 0, n = n :=
by
  use (discharger := skip) 1
  guard_target = 1 > 0 ∧ 1 = 1
  decide

-- The discharger knows about `exists_prop`.
example (h1 : 1 > 0) : ∃ (n : Nat) (_h : n > 0), n = n := by
  use 1

-- Regression test: `use` needs to ensure it does calculations inside the correct local contexts
example : let P : Nat → Prop := fun _x => ∃ _n : Nat, True; P 1 := by
  intro P
  use 1

/--
error: invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)
---
error: unsolved goals
case h
⊢ sorry 1 = 1
-/
#guard_msgs in
example : ∃ f : Nat → Nat, f 1 = 1 := by
  use ·

example : ∃ f : Nat → Nat, f 1 = 1 := by
  use (·)

end UseTests
