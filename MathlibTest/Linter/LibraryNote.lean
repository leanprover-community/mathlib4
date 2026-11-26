module

import Mathlib.Tactic.Linter.LibraryNote
public import Batteries.Util.LibraryNote

set_option Elab.inServer true

/--
@ +2:21...34
warning: Could not find `LibraryNote.A_silly_thing` in the environment.
-/
#guard_msgs (positions := true) in
example : True := trivial
-- See library note [A silly thing]

public section

library_note «A silly thing»
/-- You may be amused by this silly thing. -/

example : Nat := 1.1.1.1.1.1.1
-- See library note [A silly thing]
