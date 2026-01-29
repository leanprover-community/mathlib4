module

import Mathlib.Tactic.Linter.OverlappingInstances

set_option linter.overlappingInstances true

namespace Lean

class SubBar (α : Type) where
  a' : α

class Bar (α : Type) extends SubBar α where
  a : α

class Baz (α : Type) where
  b : α

class Baq (α : Type) where
  b : α

class FooBarBaz (α) extends Bar α, Baz α

class FooBarBaz' (α) extends Bar α, Baz α

class FooBarBaq (α) extends Bar α, Baq α

/--
error: unsolved goals
inst✝¹ inst✝ : Add Nat
⊢ [Add Nat] → [Add Nat] → Bool
---
warning: The declaration `foo` has instance hypotheses which conflict on the data they provide. Specifically:

There are 4 instances of `[Add Nat]`.

There should only be a single instance of these data-carrying typeclasses in the local context at a time. Consider choosing different instance hypotheses for the declaration `foo`.
-/
#guard_msgs in
def foo [Add Nat] [Add Nat] : [Add Nat] → [Add Nat] → Bool := by
  skip


/--
warning: The declaration `foo₁` has instance hypotheses which conflict on the data they provide. Specifically:

`[Bar Nat]` is provided by `[FooBarBaq Nat]` and `[FooBarBaz Nat]`.

There should only be a single instance of these data-carrying typeclasses in the local context at a time. Consider choosing different instance hypotheses for the declaration `foo₁`.
-/
#guard_msgs in
def foo₁ [FooBarBaz Nat] [FooBarBaq Nat] : Bool := by
  exact true

/--
warning: The declaration `foo₂` has instance hypotheses which conflict on the data they provide. Specifically:

• There are 2 instances of `[FooBarBaz Nat]`.
• `[Bar Nat]` is provided by `[FooBarBaq Nat]` and `[FooBarBaz Nat]`.

There should only be a single instance of these data-carrying typeclasses in the local context at a time. Consider choosing different instance hypotheses for the declaration `foo₂`.
-/
#guard_msgs in
def foo₂ [FooBarBaz Nat] [FooBarBaz Nat] [FooBarBaq Nat] : Bool := true

/--
warning: The declaration `foo₃` has instance hypotheses which conflict on the data they provide. Specifically:

There are 2 instances of `[FooBarBaz Nat]`.

There should only be a single instance of these data-carrying typeclasses in the local context at a time. Consider choosing different instance hypotheses for the declaration `foo₃`.
-/
#guard_msgs in
def foo₃ [FooBarBaz Nat] [FooBarBaz Nat] : Bool := true

/--
warning: The declaration `foo₄` has instance hypotheses which conflict on the data they provide. Specifically:

• There are 2 instances of `[FooBarBaz Nat]`.
• There is an instance of `[Bar Nat]` in the local context, but it is also provided by `[FooBarBaz Nat]`.

There should only be a single instance of these data-carrying typeclasses in the local context at a time. Consider choosing different instance hypotheses for the declaration `foo₄`.
-/
#guard_msgs in
def foo₄ [FooBarBaz Nat] [FooBarBaz Nat] [Bar Nat] : Bool := true

-- Note that `[SubBar Nat]` is absent, as `[Bar Nat]` is already reported.
/--
warning: The declaration `foo₅` has instance hypotheses which conflict on the data they provide. Specifically:

• `[Baz Nat]` is provided by `[FooBarBaz Nat]` and `[FooBarBaz' Nat]`.
• `[Bar Nat]` is provided by `[FooBarBaz Nat]` and `[FooBarBaz' Nat]`.

There should only be a single instance of these data-carrying typeclasses in the local context at a time. Consider choosing different instance hypotheses for the declaration `foo₅`.
-/
#guard_msgs in
def foo₅ [FooBarBaz Nat] [FooBarBaz' Nat] : Bool := true
