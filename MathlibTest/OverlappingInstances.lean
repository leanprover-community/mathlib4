module

import Mathlib.Tactic.Linter.OverlappingInstances

set_option linter.overlappingInstances true

namespace Lean

class SubBar (α : Type) where
  a' : α

class Bar (α : Type) extends SubBar α where
  a : α

class Baz (β : Type) where
  b : β

class Baq (β : Type) where
  b : β

class Foo (α) (β) extends Bar α, Baz β


class Foo' (α) (β) extends Bar α, Baq β

/--
error: unsolved goals
inst✝¹ inst✝ : Add Nat
⊢ [Add Nat] → [Add Nat] → Bool
---
warning: The declaration `Lean.foo` has instance hypotheses which overlap on data-carrying components.

There are 4 instances of `[Add Nat]`.
-/
#guard_msgs in
def foo [Add Nat] [Add Nat] : [Add Nat] → [Add Nat] → Bool := by
  skip


/--
warning: The declaration `Lean.foo'` has instance hypotheses which overlap on data-carrying components.

`[Bar Nat]` is provided by `[Foo Nat Bool]` and `[Foo' Nat String]`.
-/
#guard_msgs in
def foo' [Foo Nat Bool] [Foo' Nat String] : Bool := by
  exact true


/--
warning: The declaration `Lean.foo''` has instance hypotheses which overlap on data-carrying components.

`[Bar Nat]` is provided by `[Foo Nat Bool]` and `[Foo' Nat String]`.

There are 2 instances of `[Foo Nat Bool]`.
-/
#guard_msgs in
def foo'' [Foo Nat Bool] [Foo Nat Bool] [Foo' Nat String] : Bool := true

/--
warning: The declaration `Lean.foo'''` has instance hypotheses which overlap on data-carrying components.

There are 2 instances of `[Foo Nat Bool]`.
-/
#guard_msgs in
def foo''' [Foo Nat Bool] [Foo Nat Bool] : Bool := true

/--
error: Failed to infer type of definition `foo''''`
---
warning: The declaration `Lean.foo''''` has instance hypotheses which overlap on data-carrying components.

There is an instance of `[Bar Nat]` in the local context, but it is also provided by `[Foo Nat Bool]`.

There are 2 instances of `[Foo Nat Bool]`.
-/
#guard_msgs in
def foo'''' [Foo Nat Bool] [Foo Nat Bool] [Bar Nat] := sorry

-- Correct? Might not have `Bar Nat` if we can't provide `α`, but might if we can.
-- Only needs `(usedOnly := true)` in `mkForallFVars` to change behavior.
/--
error: unsolved goals
inst✝¹ : Foo Nat Bool
inst✝ : (α : Type) → Foo' Nat α
⊢ Bool
-/
#guard_msgs in
def fooForall [Foo Nat Bool] [∀ α, Foo' Nat α] : Bool := by
  skip
