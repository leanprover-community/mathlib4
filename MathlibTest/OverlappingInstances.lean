module

import Mathlib.Tactic.Linter.OverlappingInstances
import Mathlib.Init

namespace Lean

public section

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
warning: Declaration `foo` has overlapping instances:

There are 4 `[Add Nat]` instances.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
def foo [Add Nat] [Add Nat] : [Add Nat] → [Add Nat] → Bool := by
  skip


/--
@ +3:21...+4:12
warning: Declaration `foo₁` has overlapping instances:

`[FooBarBaz Nat]` and `[FooBarBaq Nat]` give different instances of `[SubBar Nat]`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs (positions := true) in
set_option linter.overlappingInstances true in
/-- A docstring! -/
@[expose] public def foo₁ [FooBarBaz Nat] [FooBarBaq Nat] : Bool := by
  exact true

/--
warning: Declaration `foo₂` has overlapping instances:

• There are 2 `[FooBarBaz Nat]` instances.
• `[FooBarBaz Nat]`, `[FooBarBaz Nat]`, and `[FooBarBaq Nat]` give different instances of `[SubBar Nat]`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
def foo₂ [FooBarBaz Nat] [FooBarBaz Nat] [FooBarBaq Nat] : Bool := true

/--
warning: Declaration `foo₃` has overlapping instances:

There are 2 `[FooBarBaz Nat]` instances.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
def foo₃ [FooBarBaz Nat] [FooBarBaz Nat] : Bool := true

/--
warning: Declaration `foo₄` has overlapping instances:

• There are 2 `[FooBarBaz Nat]` instances.
• `[FooBarBaz Nat]`, `[FooBarBaz Nat]`, and `[Bar Nat]` give different instances of `[SubBar Nat]`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
theorem foo₄ [FooBarBaz Nat] [FooBarBaz Nat] [Bar Nat] : True := trivial

/--
warning: Declaration `foo₅` has overlapping instances:

`[FooBarBaz Nat]` and `[FooBarBaz' Nat]` give different instances of `[Baz Nat]` and `[SubBar Nat]`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
lemma foo₅ [FooBarBaz Nat] [FooBarBaz' Nat] : True := trivial

/--
warning: Declaration `foo₆` has overlapping instances:

• `[FooBarBaz Nat]` and `[FooBarBaz' Nat]` give different instances of `[Baz Nat]`.
• `[FooBarBaz Nat]`, `[FooBarBaz' Nat]`, and `[FooBarBaq Nat]` give different instances of `[SubBar Nat]`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
lemma foo₆ [FooBarBaz Nat] [FooBarBaz' Nat] [FooBarBaq Nat] : True := trivial

namespace Foo

/-! Test unresolving name (`foo`, not `Foo.foo` or `_private...foo`) -/

/--
warning: Declaration `foo` has overlapping instances:

There are 2 `[Add Nat]` instances.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
private def foo [Add Nat] [Add Nat] : Bool := true

end Foo

section duplicates

/-! Make sure we warn on duplicate inductive classes and duplicate `Prop` classes. -/

class inductive IndFoo where
| mk₁ (n : Nat) | mk₂ (b : Bool)

/--
warning: Declaration `indFoo` has overlapping instances:

There are 2 `[IndFoo]` instances.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
def indFoo [IndFoo] [IndFoo] : Bool := true

class inductive IndFooProp : Prop where
| mk₁ (n : Nat) | mk₂ (b : Bool)

/--
warning: Declaration `indFooProp` has overlapping instances:

There are 2 `[IndFooProp]` instances.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
def indFooProp [IndFooProp] [IndFooProp] : Bool := true

end duplicates

section instantiateMVars

variable {α : Type*} [Repr α]

/--
warning: Declaration `needsInstantiateMVars` has overlapping instances:

There are 2 `[Repr α]` instances.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
def needsInstantiateMVars [Repr α] : Bool := true

end instantiateMVars

section setOptionIn

set_option linter.overlappingInstances false in
def fooNothing [Add Nat] [Add Nat] : [Add Nat] → [Add Nat] → Bool := true

set_option linter.overlappingInstances false

/--
warning: Declaration `fooSomething` has overlapping instances:

There are 4 `[Add Nat]` instances.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
set_option linter.overlappingInstances true in
def fooSomething [Add Nat] [Add Nat] : [Add Nat] → [Add Nat] → Bool := true

end setOptionIn

namespace universes

/-! Test a projection that goes from `Type*` to `Sort*`. -/

class A (α : Sort u) where

class B (α : Type u) extends A α

/--
warning: Declaration `_example` has overlapping instances:

`[B α]` and `[A α]` give different instances of `[A α]`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
example (α : Type 4) [B α] [A α] : True := trivial

end universes

namespace parameters

/-! Test a projection that changes the instance parameters. -/

class A (α : Type*) where
class A' (α : Type*) extends A α where

instance {α} : A α where

class B (α β : Type*) [A α] where
class B' (α β : Type*) [A' α] extends B α β where

/--
warning: Declaration `_example` has overlapping instances:

`[B α β]` and `[B' α β]` give different instances of `[B α β]`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
example {α β} [B α β] [A' α] [B' α β] : True := trivial

end parameters

/-! Test a `where` clause. -/

/--
warning: Declaration `List.lt'.go` has overlapping instances:

There are 2 `[DecidableEq α]` instances.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
def List.lt' {α} [DecidableEq α] (a b : List α) : Bool :=
  go a b
where
  go [DecidableEq α] (_ _ : List α) : Bool := false

-- Sadly, the linter does not work when the declaration doesn't have a body:

class FooClass (α : Type) [Add α] [Add α] where
