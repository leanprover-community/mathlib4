module

import Mathlib.Tactic.Linter.OverlappingInstances
import Mathlib.Init

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
warning: Overlapping instance parameters in `foo`:

⚠️ There are 4 `[Add Nat]` instances; one is sufficient.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
def foo [Add Nat] [Add Nat] : [Add Nat] → [Add Nat] → Bool := by
  skip

/--
@ +3:21...+4:12
warning: Overlapping instance parameters in `foo₁`:

⚠️ `[FooBarBaz Nat]` and `[FooBarBaq Nat]` can be used to infer conflicting versions of `[SubBar Nat]`.

When a data-carrying type class has multiple potential instances coming from different instance parameters, then these potential instances are incompatible. This is an example of an "instance diamond", which leads to unexpected unification failures.

Delete or combine some of your instance parameters to avoid this.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs (positions := true) in
set_option linter.overlappingInstances true in
/-- A docstring! -/
@[expose] public def foo₁ [FooBarBaz Nat] [FooBarBaq Nat] : Bool := by
  exact true

/--
warning: Overlapping instance parameters in `foo₂`:

⚠️ There are 2 `[FooBarBaz Nat]` instances; one is sufficient.
⚠️ `[FooBarBaz
   Nat]`, `[FooBarBaz Nat]`, and `[FooBarBaq Nat]` can be used to infer conflicting versions of `[SubBar Nat]`.
💡️ Of these, `[FooBarBaz Nat]` and `[FooBarBaz Nat]` may be removed.

When a data-carrying type class has multiple potential instances coming from different instance parameters, then these potential instances are incompatible. This is an example of an "instance diamond", which leads to unexpected unification failures.

Delete or combine some of your instance parameters to avoid this.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
def foo₂ [FooBarBaz Nat] [FooBarBaz Nat] [FooBarBaq Nat] : Bool := true

/--
warning: Overlapping instance parameters in `foo₃`:

⚠️ There are 2 `[FooBarBaz Nat]` instances; one is sufficient.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
def foo₃ [FooBarBaz Nat] [FooBarBaz Nat] : Bool := true

/--
warning: Overlapping instance parameters in `foo₄`:

⚠️ There are 2 `[FooBarBaz Nat]` instances; one is sufficient.
⚠️ `[FooBarBaz Nat]`, `[FooBarBaz Nat]`, and `[Bar Nat]` can be used to infer conflicting versions of `[SubBar Nat]`.
💡️ Of these, `[FooBarBaz Nat]`, `[FooBarBaz Nat]`, and `[Bar Nat]` may be removed.

When a data-carrying type class has multiple potential instances coming from different instance parameters, then these potential instances are incompatible. This is an example of an "instance diamond", which leads to unexpected unification failures.

Delete or combine some of your instance parameters to avoid this.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
theorem foo₄ [FooBarBaz Nat] [FooBarBaz Nat] [Bar Nat] : True := trivial

/--
warning: Overlapping instance parameters in `foo₅`:

⚠️ `[FooBarBaz Nat]` and `[FooBarBaz' Nat]` can be used to infer conflicting versions of `[Baz Nat]` and `[SubBar Nat]`.

When a data-carrying type class has multiple potential instances coming from different instance parameters, then these potential instances are incompatible. This is an example of an "instance diamond", which leads to unexpected unification failures.

Delete or combine some of your instance parameters to avoid this.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
lemma foo₅ [FooBarBaz Nat] [FooBarBaz' Nat] : True := trivial

/--
warning: Overlapping instance parameters in `foo₆`:

⚠️ `[FooBarBaz Nat]` and `[FooBarBaz' Nat]` can be used to infer conflicting versions of `[Baz Nat]`.
⚠️ `[FooBarBaz
   Nat]`, `[FooBarBaz' Nat]`, and `[FooBarBaq Nat]` can be used to infer conflicting versions of `[SubBar Nat]`.

When a data-carrying type class has multiple potential instances coming from different instance parameters, then these potential instances are incompatible. This is an example of an "instance diamond", which leads to unexpected unification failures.

Delete or combine some of your instance parameters to avoid this.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
lemma foo₆ [FooBarBaz Nat] [FooBarBaz' Nat] [FooBarBaq Nat] : True := trivial

namespace Foo

/-! Test unresolving name (`foo`, not `Foo.foo` or `_private...foo`) -/

/--
warning: Overlapping instance parameters in `foo`:

⚠️ There are 2 `[Add Nat]` instances; one is sufficient.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
private def foo [Add Nat] [Add Nat] : Bool := true

end Foo

namespace prop

class IsFoo : Prop

class IsBar : Prop extends IsFoo

class IsBaz : Prop extends IsBar

/--
warning: Overlapping instance parameters in `_example`:

⚠️ `[IsBar]` and `[IsBaz]` each imply `[IsFoo]`.
💡️ Of these, `[IsBar]` may be removed.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
example [IsBar] [IsBaz] : True := trivial

class Bar : Type extends IsFoo
class Baz : Type extends IsFoo
class Baz1 : Type extends Baz
class Baz2 : Type extends Baz

/--
warning: Overlapping instance parameters in `_example`:

⚠️ `[IsFoo]` and `[Bar]` each imply `[IsFoo]`.
💡️ Of these, `[IsFoo]` may be removed.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
example [IsFoo] [Bar] : True := trivial

example [IsBar] [Bar] : True := trivial

example [Bar] [Baz] : True := trivial

/--
warning: Overlapping instance parameters in `_example`:

⚠️ There are 2 `[Baz]` instances; one is sufficient.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
example [Baz] [Baz] : True := trivial

/--
warning: Overlapping instance parameters in `_example`:

⚠️ `[Baz]` and `[Baz1]` can be used to infer conflicting versions of `[Baz]`.
💡️ Of these, `[Baz]` may be removed.

When a data-carrying type class has multiple potential instances coming from different instance parameters, then these potential instances are incompatible. This is an example of an "instance diamond", which leads to unexpected unification failures.

Delete or combine some of your instance parameters to avoid this.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
example [Baz] [Baz1] : True := trivial

/--
warning: Overlapping instance parameters in `_example`:

⚠️ `[Baz1]` and `[Baz2]` can be used to infer conflicting versions of `[Baz]`.

When a data-carrying type class has multiple potential instances coming from different instance parameters, then these potential instances are incompatible. This is an example of an "instance diamond", which leads to unexpected unification failures.

Delete or combine some of your instance parameters to avoid this.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
example [Baz1] [Baz2] : True := trivial

end prop

section duplicates

/-! Make sure we warn on duplicate inductive classes and duplicate `Prop` classes. -/

class inductive IndFoo where
| mk₁ (n : Nat) | mk₂ (b : Bool)

/--
warning: Overlapping instance parameters in `indFoo`:

⚠️ There are 2 `[IndFoo]` instances; one is sufficient.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
def indFoo [IndFoo] [IndFoo] : Bool := true

class inductive IndFooProp : Prop where
| mk₁ (n : Nat) | mk₂ (b : Bool)

/--
warning: Overlapping instance parameters in `indFooProp`:

⚠️ There are 2 `[IndFooProp]` instances; one is sufficient.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
def indFooProp [IndFooProp] [IndFooProp] : Bool := true

end duplicates

section instantiateMVars

variable {α : Type*} [Repr α]

/--
warning: Overlapping instance parameters in `needsInstantiateMVars`:

⚠️ There are 2 `[Repr α]` instances; one is sufficient.

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
warning: Overlapping instance parameters in `fooSomething`:

⚠️ There are 4 `[Add Nat]` instances; one is sufficient.

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
warning: Overlapping instance parameters in `_example`:

⚠️ `[B α]` and `[A α]` can be used to infer conflicting versions of `[A α]`.
💡️ Of these, `[A α]` may be removed.

When a data-carrying type class has multiple potential instances coming from different instance parameters, then these potential instances are incompatible. This is an example of an "instance diamond", which leads to unexpected unification failures.

Delete or combine some of your instance parameters to avoid this.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
example (α : Type 4) [B α] [A α] : True := trivial

end universes

namespace parameters

/-! Test a projection that changes the instance parameters. (This needs `eraseInstances`) -/

class A (α : Type*) where
class A' (α : Type*) extends A α where

class B (α β : Type*) [A α] where
class B' (α β : Type*) [A' α] extends B α β where

instance {α} : A α where

/--
warning: Overlapping instance parameters in `_example`:

⚠️ `[B α β]` and `[B' α β]` can be used to infer conflicting versions of `[B α β]`.
💡️ Of these, `[B α β]` may be removed.

When a data-carrying type class has multiple potential instances coming from different instance parameters, then these potential instances are incompatible. This is an example of an "instance diamond", which leads to unexpected unification failures.

Delete or combine some of your instance parameters to avoid this.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
example {α β} [B α β] [A' α] [B' α β] : True := trivial

end parameters

/-! Test a `where` clause. -/

/--
warning: Overlapping instance parameters in `List.lt'.go`:

⚠️ There are 2 `[DecidableEq α]` instances; one is sufficient.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
def List.lt' {α} [DecidableEq α] (a b : List α) : Bool :=
  go a b
where
  go [DecidableEq α] (_ _ : List α) : Bool := false

-- Sadly, the linter does not work when the declaration doesn't have a body:

class FooClass (α : Type) [Add α] [Add α] where

/-! Test classes that extend a non-class -/

structure NotAClass where
class IsAClass1 extends NotAClass
class IsAClass1' extends NotAClass
class IsAClass2 extends IsAClass1

example [IsAClass1] [IsAClass1'] : True := trivial

/--
warning: Overlapping instance parameters in `_example`:

⚠️ `[IsAClass1]` and `[IsAClass2]` can be used to infer conflicting versions of `[IsAClass1]`.
💡️ Of these, `[IsAClass1]` may be removed.

When a data-carrying type class has multiple potential instances coming from different instance parameters, then these potential instances are incompatible. This is an example of an "instance diamond", which leads to unexpected unification failures.

Delete or combine some of your instance parameters to avoid this.

Note: This linter can be disabled with `set_option linter.overlappingInstances false`
-/
#guard_msgs in
example [IsAClass1] [IsAClass2] : True := trivial
