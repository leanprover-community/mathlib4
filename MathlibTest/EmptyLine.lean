import Mathlib.Tactic.Linter.EmptyLine

set_option linter.style.emptyLine true

/-!
-/

/-!

-/

/--
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
note: this linter can be disabled with `set_option linter.style.emptyLine false`
---
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
note: this linter can be disabled with `set_option linter.style.emptyLine false`
---
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
note: this linter can be disabled with `set_option linter.style.emptyLine false`
-/
#guard_msgs in
example : True := by
  refine ?_

  refine ?_

  refine ?_


  trivial

/--
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
note: this linter can be disabled with `set_option linter.style.emptyLine false`
-/
#guard_msgs in
/-- This is a doc-string.

Here it should be allowed to have empty lines.
-/
example : True :=

  trivial

/--
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
note: this linter can be disabled with `set_option linter.style.emptyLine false`
---
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
note: this linter can be disabled with `set_option linter.style.emptyLine false`
---
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
note: this linter can be disabled with `set_option linter.style.emptyLine false`
-/
#guard_msgs in
run_cmd
  let _ ← `(/--
hello

my name

is
-/ abbrev D := 0)
  let _ ←

`(/-- hello -/ abbrev D := 0)
  let _ ← `(/-- hello -/ abbrev D := 0)
  let _ ← `(/--
hello

also

my

name

is
-/ abbrev

D

:= 0)


section TrailingComments

-- A comment here: the empy line before this should be ignored.

-- As well as mutual blocks

mutual

example := 0

end

end TrailingComments

/--
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
note: this linter can be disabled with `set_option linter.style.emptyLine false`
-/
#guard_msgs in
/--
An

empty line.
-/
structure WithAString

 where
  str : String := "I have

                  embedded empty lines, but that is ok!"
