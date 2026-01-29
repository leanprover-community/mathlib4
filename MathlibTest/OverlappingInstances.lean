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

class FooBarBaz (α) extends Bar α, Baz α

class FooBarBaz' (α) extends Bar α, Baz α

class FooBarBaq (α) extends Bar α, Baq α

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
warning: The declaration `Lean.foo₁` has instance hypotheses which overlap on data-carrying components.

`[Bar Nat]` is provided by `[FooBarBaq Nat]` and `[FooBarBaz Nat]`.
-/
#guard_msgs in
def foo₁ [FooBarBaz Nat] [FooBarBaq Nat] : Bool := by
  exact true

/--
warning: The declaration `Lean.foo₂` has instance hypotheses which overlap on data-carrying components.

There are 2 instances of `[FooBarBaz Nat]`.

`[Bar Nat]` is provided by `[FooBarBaq Nat]` and `[FooBarBaz Nat]`.
-/
#guard_msgs in
def foo₂ [FooBarBaz Nat] [FooBarBaz Nat] [FooBarBaq Nat] : Bool := true

/--
warning: The declaration `Lean.foo₃` has instance hypotheses which overlap on data-carrying components.

There are 2 instances of `[FooBarBaz Nat]`.
-/
#guard_msgs in
def foo₃ [FooBarBaz Nat] [FooBarBaz Nat] : Bool := true

/--
warning: The declaration `Lean.foo₄` has instance hypotheses which overlap on data-carrying components.

There are 2 instances of `[FooBarBaz Nat]`.

There is an instance of `[Bar Nat]` in the local context, but it is also provided by `[FooBarBaz Nat]`.
-/
#guard_msgs in
def foo₄ [FooBarBaz Nat] [FooBarBaz Nat] [Bar Nat] : Bool := true

-- Note that `[SubBar Nat]` is absent, as `[Bar Nat]` is already reported.
/--
warning: The declaration `Lean.foo₅` has instance hypotheses which overlap on data-carrying components.

`[Baz Nat]` is provided by `[FooBarBaz Nat]` and `[FooBarBaz' Nat]`.

`[Bar Nat]` is provided by `[FooBarBaz Nat]` and `[FooBarBaz' Nat]`.
-/
#guard_msgs in
def foo₅ [FooBarBaz Nat] [FooBarBaz' Nat] : Bool := true
