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

note: this linter can be disabled with `set_option linter.style.emptyLine false`
---
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
Context:

             ↓
  ⏎  apply ?_⏎⏎  refine ?_⏎⏎

note: this linter can be disabled with `set_option linter.style.emptyLine false`
---
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
Context:

              ↓
  ⏎  refine ?_⏎⏎⏎⏎

note: this linter can be disabled with `set_option linter.style.emptyLine false`
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
Context:

            ↓
  ⏎  let _ ←⏎⏎`(/-- hello -/ abbrev D := 0)⏎⏎

note: this linter can be disabled with `set_option linter.style.emptyLine false`
---
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
Context:

     ↓
  ⏎--⏎⏎D⏎⏎

note: this linter can be disabled with `set_option linter.style.emptyLine false`
---
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
Context:

    ↓
  ⏎D⏎⏎:= 0)⏎⏎

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
--

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
Context:

                        ↓
  ⏎structure WithAString⏎⏎ where⏎⏎

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

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example : True := by  -- The following empty line is not reported, since the command is noisy.

  stop
  sorry

open Lean Elab Command in
elab "ff " cmd:command : command => do
  elabCommand cmd
  let trails := cmd.raw.filterMap fun s =>
    if let some str := s.getTrailing?
    then
      let strim := str.trim
      if (strim.splitOn "\n\n").length != 1 then
        some strim.getRange
      else none
    else none
  let trails : Std.HashSet String.Range := .ofArray trails
  --dbg_trace trails.fold (init := #[]) (fun acc r => acc.push s!"({r.1}, {r.2})")
  for r in trails do
    logInfoAt (.ofRange r) "Start!"
    logInfoAt (.ofRange ⟨r.2, r.2⟩) "End!"
  --logInfo m!"{cmd}"

/--
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
Context:

                       ↓
  ⏎example : True := by⏎⏎-- Here I start⏎⏎

note: this linter can be disabled with `set_option linter.style.emptyLine false`
---
warning: Please, write a comment here or remove this line, but do not place empty lines within commands!
Context:

         ↓
  ⏎--stop⏎⏎trivial⏎⏎

note: this linter can be disabled with `set_option linter.style.emptyLine false`
-/
#guard_msgs in
example : True := by

-- Here I start

/-

-/

--stop

trivial -- also a comment

-- with a line break
