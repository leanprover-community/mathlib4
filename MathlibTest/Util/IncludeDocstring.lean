module

public import Mathlib.Util.IncludeDocstring

/-! # Verso code to include one docstring in another

This module defines the `insertDocstringOf` command: into a verso doc-string, writing
`{insertDocstringOf foo}` inside a verso doc-string inserts the doc-string of
declaration `foo` in the current environment, as a separate paragraph.
If `foo` does not exist or has no doc-string, it throws an error.

This can be used, for example, in custom elaborators to provide custom notation.
-/

open Lean Doc Elab Command

set_option doc.verso true

/-- Let's have the doc-string of {name}`Nat`:

{insertDocstringOf Nat}

And now further content. -/
def foo : Nat := 1

/-- error: Unknown constant `nonExistent` -/
#guard_msgs in
/-- {insertDocstringOf nonExistent} -/
def foo' : Nat := 0

/-- Another definition with a doc-string, whose name even references itself: {name}`bar` -/
def bar : Nat := 2

/-- {insertDocstringOf bar} -/
example : foo = 1 := by simp [foo]

/-- {insertDocstringOf bar}
and

{insertDocstringOf foo}
-/
theorem aux : bar = 2 := by simp [bar]

-- TODO: why is this a parsing error? can this be fixed?
/-- error: unexpected newline; expected '![', '$$', '$', '*', '[', '[^', '_', '`' or '{' -/
#guard_msgs in
/-- {insertDocstringOf bar}
and
{insertDocstringOf foo}
-/
theorem aux' : bar = 2 := by simp [bar]
