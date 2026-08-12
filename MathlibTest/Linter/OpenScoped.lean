import Mathlib.Tactic.Linter.OpenScoped

/-!
# Tests for the `openScoped` linter

The fixtures mirror the shape that mathlib uses: `scoped[Foo]` puts the parser of the notation
in the root namespace `Foo`, while the declarations that a file names live in a namespace
`Bar.Foo`. One `open Foo` inside `namespace Bar` opens both.
-/

namespace Absolute

/-- A notation whose parser lives in the root namespace `Absolute`. -/
scoped notation "!!!" => 37

end Absolute

namespace OpenScopedTest.Absolute

/-- A declaration that a scope can name through `open Absolute`. -/
def bar : Nat := 4

/-- A structure for the dot-notation test. -/
structure Wrap where
  /-- The wrapped value. -/
  val : Nat

/-- A declaration whose field the dot-notation test projects. -/
def wrapped : Wrap := ⟨5⟩

end OpenScopedTest.Absolute

-- The linter is off here, so this `open` is not tracked and reports no verdict of its own.
open OpenScopedTest

set_option linter.openScoped true

-- The scope uses `Absolute` only through its scoped notation: the linter suggests `open scoped`.
section
open Absolute

example : Nat := !!!

/--
warning: namespace 'Absolute' is used only through scoped declarations: consider 'open scoped Absolute'

Note: This linter can be disabled with `set_option linter.openScoped false`
-/
#guard_msgs in
end

-- The scope resolves `bar` through `OpenScopedTest.Absolute`, which the written name `Absolute`
-- denotes as well: the linter stays silent.
section
open Absolute

example : Nat := !!!
example : Nat := bar

#guard_msgs in
end

-- The scope resolves `wrapped` and projects a field of it. The composed name
-- `OpenScopedTest.Absolute.wrapped.val` does not exist, so the guard needs the prefix.
section
open Absolute

example : Nat := !!!
example : Nat := wrapped.val

#guard_msgs in
end

-- `open scoped` is not tracked, so the linter stays silent.
section
open scoped Absolute

example : Nat := !!!

#guard_msgs in
end
