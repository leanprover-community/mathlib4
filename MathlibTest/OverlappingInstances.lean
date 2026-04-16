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
warning: Declaration `foo` has instance hypotheses which provide conflicting versions of the same data. Specifically:

`[Add Nat]`, `[Add Nat]`, `[Add Nat]`, and `[Add Nat]` provide conflicting instances of `Add Nat`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
def foo [Add Nat] [Add Nat] : [Add Nat] → [Add Nat] → Bool := by
  skip


/--
@ +3:68...+4:12
warning: Declaration `foo₁` has instance hypotheses which provide conflicting versions of the same data. Specifically:

`[FooBarBaz Nat]` and `[FooBarBaq Nat]` provide conflicting instances of `SubBar Nat`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs (positions := true) in
set_option linter.overlappingInstances true in
/-- A docstring! -/
@[expose] public def foo₁ [FooBarBaz Nat] [FooBarBaq Nat] : Bool := by
  exact true

/--
warning: Declaration `foo₂` has instance hypotheses which provide conflicting versions of the same data. Specifically:

• `[FooBarBaz Nat]` and `[FooBarBaz Nat]` provide conflicting instances of `Baz Nat`.
• `[FooBarBaz Nat]`, `[FooBarBaz Nat]`, and `[FooBarBaq Nat]` provide conflicting instances of `SubBar Nat`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
def foo₂ [FooBarBaz Nat] [FooBarBaz Nat] [FooBarBaq Nat] : Bool := true

/--
warning: Declaration `foo₃` has instance hypotheses which provide conflicting versions of the same data. Specifically:

• `[FooBarBaz Nat]` and `[FooBarBaz Nat]` provide conflicting instances of `Baz Nat`.
• `[FooBarBaz Nat]` and `[FooBarBaz Nat]` provide conflicting instances of `SubBar Nat`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
def foo₃ [FooBarBaz Nat] [FooBarBaz Nat] : Bool := true

/--
warning: Declaration `foo₄` has instance hypotheses which provide conflicting versions of the same data. Specifically:

• `[FooBarBaz Nat]` and `[FooBarBaz Nat]` provide conflicting instances of `Baz Nat`.
• `[FooBarBaz Nat]`, `[FooBarBaz Nat]`, and `[Bar Nat]` provide conflicting instances of `SubBar Nat`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
theorem foo₄ [FooBarBaz Nat] [FooBarBaz Nat] [Bar Nat] : True := trivial

-- Note that `[SubBar Nat]` is absent, as `[Bar Nat]` is already reported.
/--
warning: Declaration `foo₅` has instance hypotheses which provide conflicting versions of the same data. Specifically:

• `[FooBarBaz Nat]` and `[FooBarBaz' Nat]` provide conflicting instances of `Baz Nat`.
• `[FooBarBaz Nat]` and `[FooBarBaz' Nat]` provide conflicting instances of `SubBar Nat`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
lemma foo₅ [FooBarBaz Nat] [FooBarBaz' Nat] : True := trivial

namespace Foo

/-! Test unresolving name (`foo`, not `Foo.foo` or `_private...foo`) -/

/--
warning: Declaration `foo` has instance hypotheses which provide conflicting versions of the same data. Specifically:

`[Add Nat]` and `[Add Nat]` provide conflicting instances of `Add Nat`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
private def foo [Add Nat] [Add Nat] : Bool := true

end Foo

section classInductive

/-! Make sure we warn on duplicate inductive data-carrying inductive classes, even though these do
not have and cannot be structure projections. -/

class inductive IndFoo where
| mk₁ (n : Nat) | mk₂ (b : Bool)

/--
warning: Declaration `indFoo` has instance hypotheses which provide conflicting versions of the same data. Specifically:

`[IndFoo]` and `[IndFoo]` provide conflicting instances of `IndFoo`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
def indFoo [IndFoo] [IndFoo] : Bool := true

class inductive IndFooProp : Prop where
| mk₁ (n : Nat) | mk₂ (b : Bool)

-- We also warn when there are duplicate `Prop` clases
/--
warning: Declaration `indFooProp` has instance hypotheses which provide conflicting versions of the same data. Specifically:

`[IndFooProp]` and `[IndFooProp]` provide conflicting instances of `IndFooProp`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
def indFooProp [IndFooProp] [IndFooProp] : Bool := true

end classInductive

section instantiateMVars

variable {α : Type*} [Repr α]

/--
warning: Declaration `needsInstantiateMVars` has instance hypotheses which provide conflicting versions of the same data. Specifically:

`[Repr α]` and `[Repr α]` provide conflicting instances of `Repr α`.

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
warning: Declaration `fooSomething` has instance hypotheses which provide conflicting versions of the same data. Specifically:

`[Add Nat]`, `[Add Nat]`, `[Add Nat]`, and `[Add Nat]` provide conflicting instances of `Add Nat`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
set_option linter.overlappingInstances true in
def fooSomething [Add Nat] [Add Nat] : [Add Nat] → [Add Nat] → Bool := true

end setOptionIn

namespace universes

class A (α : Sort u) where

class B (α : Type u) extends A α

/--
warning: Declaration `_example` has instance hypotheses which provide conflicting versions of the same data. Specifically:

`[B α]` and `[A α]` provide conflicting instances of `A α`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
example (α : Type 4) [B α] [A α] : True := trivial

end universes

namespace parameters

class A (α : Type*) where
class A' (α : Type*) extends A α where

instance {α} : A α where

class B (α β : Type*) [A α] where
class B' (α β : Type*) [A' α] extends B α β where

/--
warning: Declaration `_example` has instance hypotheses which provide conflicting versions of the same data. Specifically:

`[B α β]` and `[B' α β]` provide conflicting instances of `B α β`.

Consider choosing different instance hypotheses.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
example {α β} [B α β] [A' α] [B' α β] : True := trivial

end parameters
