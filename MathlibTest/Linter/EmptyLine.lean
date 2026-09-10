module
import Mathlib.Tactic.Linter.EmptyLine

set_option linter.style.emptyLine true

/-!
-/

/-!

-/

/--
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
Context:
              ↓
  ⏎  refine ?_⏎⏎  apply ?_⏎⏎

Note: This linter can be disabled with `set_option linter.style.emptyLine false`
---
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
Context:
             ↓
  ⏎  apply ?_⏎⏎  refine ?_⏎⏎

Note: This linter can be disabled with `set_option linter.style.emptyLine false`
---
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
Context:
              ↓
  ⏎  refine ?_⏎⏎⏎⏎

Note: This linter can be disabled with `set_option linter.style.emptyLine false`
-/
#guard_msgs in
example : True := by
  refine ?_

  apply ?_

  refine ?_


  trivial

/--
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
Context:
                    ↓
  ⏎example : True :=⏎⏎  trivial⏎⏎

Note: This linter can be disabled with `set_option linter.style.emptyLine false`
-/
#guard_msgs in
/-- This is a doc-string.

Here it should be allowed to have empty lines.
-/
example : True :=

  trivial

/--
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
Context:
            ↓
  ⏎  let _ ←⏎⏎`(/-- hello -/ abbrev D := 0)⏎⏎

Note: This linter can be disabled with `set_option linter.style.emptyLine false`
---
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
Context:
     ↓
  ⏎--⏎⏎D⏎⏎

Note: This linter can be disabled with `set_option linter.style.emptyLine false`
---
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
Context:
    ↓
  ⏎D⏎⏎:= 0)⏎⏎

Note: This linter can be disabled with `set_option linter.style.emptyLine false`
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
--

D

:= 0)


section TrailingComments

-- A comment here: the empty line before this should be ignored.

-- As well as mutual blocks

mutual

example := 0

end

end TrailingComments

/--
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
Context:
                        ↓
  ⏎structure WithAString⏎⏎ where⏎⏎

Note: This linter can be disabled with `set_option linter.style.emptyLine false`
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

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : True := by  -- The following empty line is not reported, since the command is noisy.

  stop
  sorry

/--
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
Context:
                       ↓
  ⏎example : True := by⏎⏎  -- Here I start⏎⏎

Note: This linter can be disabled with `set_option linter.style.emptyLine false`
---
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
Context:
           ↓
  ⏎  --stop⏎⏎  trivial⏎⏎

Note: This linter can be disabled with `set_option linter.style.emptyLine false`
-/
#guard_msgs in
example : True := by

  -- Here I start

  /-

  -/

  --stop

  trivial -- also a comment

  -- with a line break

-- Check that `where` fields allow empty lines.
structure F where

  a : Unit → Unit

  b : Unit

  c : Unit

-- Check that `where` fields allow empty lines.
def F₀ : F where

  a _ := by
    exact ()

  b := ()

  c := ()

--
