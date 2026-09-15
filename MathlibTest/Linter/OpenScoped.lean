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

/-- A declaration for the tests of the selective `open` forms. -/
def foo : Nat := 1

end Absolute

namespace Second

/-- A second scoped notation, for the tests with two namespaces. -/
scoped notation "???" => 41

/-- A declaration that a scope can name through `open Second`. -/
def something : Nat := 7

/-- A declaration of `Second` alone, which no alias of another namespace shares. -/
def onlySecond : Nat := 9

end Second

namespace OpenScopedTest.Absolute

/-- A declaration that a scope can name through `open Absolute`. -/
def bar : Nat := 4

/-- A structure for the dot-notation test. -/
structure Wrap where
  /-- The wrapped value. -/
  val : Nat

/-- A declaration whose field the dot-notation test projects. -/
def wrapped : Wrap := ⟨5⟩

/-- A notation whose expansion names `bar`, and whose use writes no identifier. -/
scoped notation "%%%" => bar

-- An alias, so that the guard sees a name that is no declaration of the namespace.
export Second (something)

end OpenScopedTest.Absolute

-- The linter is off here, so this `open` is not tracked and reports no verdict of its own.
open OpenScopedTest

set_option linter.openScoped true

/-! ## The suggestion -/

-- The scope uses `Absolute` only through its scoped notation.
section
open Absolute

example : Nat := !!!

/--
warning: namespace 'Absolute' is used only through scoped declarations: consider 'open scoped Absolute'

Note: This linter can be disabled with `set_option linter.openScoped false`
-/
#guard_msgs in
end

-- A `namespace` closes a scope in the same way as a `section`.
namespace Wrapper
open Absolute

example : Nat := !!!

/--
warning: namespace 'Absolute' is used only through scoped declarations: consider 'open scoped Absolute'

Note: This linter can be disabled with `set_option linter.openScoped false`
-/
#guard_msgs in
end Wrapper

-- One command, two namespaces, both used only through their scoped notation: one verdict each.
section
open Absolute Second

example : Nat := !!!
example : Nat := ???

/--
warning: namespace 'Absolute' is used only through scoped declarations: consider 'open scoped Absolute'

Note: This linter can be disabled with `set_option linter.openScoped false`
---
warning: namespace 'Second' is used only through scoped declarations: consider 'open scoped Second'

Note: This linter can be disabled with `set_option linter.openScoped false`
-/
#guard_msgs in
end

-- One command, two namespaces, one of them resolved: the linter reports the other one only.
section
open Second Absolute

example : Nat := !!!
example : Nat := onlySecond

/--
warning: namespace 'Absolute' is used only through scoped declarations: consider 'open scoped Absolute'

Note: This linter can be disabled with `set_option linter.openScoped false`
-/
#guard_msgs in
end

-- Each scope level gets its own verdict, at the `end` that closes it.
section
open Absolute

example : Nat := !!!

section
open Second

example : Nat := ???

/--
warning: namespace 'Second' is used only through scoped declarations: consider 'open scoped Second'

Note: This linter can be disabled with `set_option linter.openScoped false`
-/
#guard_msgs in
end

/--
warning: namespace 'Absolute' is used only through scoped declarations: consider 'open scoped Absolute'

Note: This linter can be disabled with `set_option linter.openScoped false`
-/
#guard_msgs in
end

/-! ## Evidence of name resolution -/

-- The scope resolves `bar` through `OpenScopedTest.Absolute`, which the written name `Absolute`
-- denotes as well.
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

-- The guard also accepts an alias of the namespace.
section
open Absolute

example : Nat := !!!
example : Nat := something

#guard_msgs in
end

-- The use of `%%%` writes no identifier, and its expansion names `bar`. The declaration that the
-- command adds carries that constant, which is the third source of evidence.
section
open Absolute

def usesExpansion : Nat := %%%

#guard_msgs in
end

/-! ## Commands that the linter does not track -/

-- `open scoped` activates the scoped declarations already.
section
open scoped Absolute

example : Nat := !!!

#guard_msgs in
end

-- A multi-component namespace.
section
open OpenScopedTest.Absolute

example : Nat := %%%

#guard_msgs in
end

-- The `open ... in` form, which applies to one command.
section

open Absolute in
example : Nat := !!!

#guard_msgs in
end

-- The selective form. The `open scoped` line activates the notation, so that a tracked entry
-- for `Second` would have its evidence and the test would see a verdict.
section
open scoped Second
open Second (onlySecond)

example : Nat := ???

#guard_msgs in
end

-- The hiding form.
section
open scoped Second
open Second hiding onlySecond

example : Nat := ???

#guard_msgs in
end

-- The renaming form.
section
open scoped Second
open Second renaming onlySecond → renamed

example : Nat := ???

#guard_msgs in
end

-- A scope with no use of the namespace at all: the linter reports one verdict only, and it
-- never suggests the removal of an `open`.
section
open Absolute

example : Nat := 0

#guard_msgs in
end

-- The option gates the tracking, so an `open` that runs with the linter off gets no verdict.
section
set_option linter.openScoped false
open Absolute

example : Nat := !!!

set_option linter.openScoped true

#guard_msgs in
end

/-! ## The report at the end of the file -/

-- An `open` that no `end` closes gets its verdict at the terminal command.
open Absolute

example : Nat := !!!

/--
warning: using 'exit' to interrupt Lean
---
warning: namespace 'Absolute' is used only through scoped declarations: consider 'open scoped Absolute'

Note: This linter can be disabled with `set_option linter.openScoped false`
-/
#guard_msgs in
#exit

-- `#exit` under `#guard_msgs` does not stop the file, and the linter reports again at the real
-- end of the file. The option gates the report, so this keeps the test output empty.
set_option linter.openScoped false
