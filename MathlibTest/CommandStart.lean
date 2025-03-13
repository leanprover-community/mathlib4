import Aesop.Frontend.Attribute
import Mathlib.Tactic.Linter.CommandStart

section tests
open Mathlib.Linter Style.CommandStart

set_option linter.hashCommand false
#guard
  let s := "abcdeacd"
  findString s "a" == ("", "abcdeacd")

#guard
  let s := "abcdeacd"
  findString s "b" == ("a", "bcdeacd")

#guard
  let s := "abcdeacd"
  findString s "ab" == ("", "abcdeacd")

#guard
  let s := "abcdeacd"
  findString s "ac" == ("abcde", "acd")

#guard
  let s := "text /- /-- -/"
  let pattern := "/--"
  findString s pattern == ("text /- ", "/-- -/")

#guard findString "/-- ≫|/ a" "|/" == ("/-- ≫", "|/ a")

#guard trimComments "- /-/\ncontinuing on -/\n and more text" false ==
                    "-\n and more text"
#guard trimComments "text /- I am a comment -/ more text" false ==
                    "text more text"
#guard trimComments  "text /- I am a comment -/   more text" false ==
                    "text   more text"
#guard trimComments "text -- /- I am a comment -/   more text" false ==
                    "text"
#guard trimComments  "text /- comment /- nested -/-/" false == -- comment nesting is not implemented
                      "text-/"
#guard trimComments "text /-- doc-string -/" false ==
                    "text /-- doc-string -/"

end tests

-- The notation `0::[]` disables the linter
variable  (h : 0::[] = [])

/--
warning: 'section' starts on column 1, but all commands should start at the beginning of the line.
note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
 section

/--
warning: Current syntax:  'mple  '
Expected syntax: 'mple : Tru'

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example  : True := trivial

/--
warning: Current syntax:  'le (a: Nat'
Expected syntax: 'le (a : Na'

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
variable (a: Nat)

/--
warning: unused variable `a`
note: this linter can be disabled with `set_option linter.unusedVariables false`
---
warning: Current syntax:  'le (a: Nat'
Expected syntax: 'le (a : Na'

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example (a: Nat) : True := trivial

/--
warning: Current syntax:  'le {a: Nat'
Expected syntax: 'le {a : Na'

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {a: Nat} : a = a := rfl

/--
warning: Current syntax:  ' {a :Nat} '
Expected syntax: ' {a : Nat}'

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {a :Nat} : a = a := rfl

/--
warning: Current syntax:  'mple  {a :'
Expected syntax: 'mple {a : '

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example  {a :Nat} : a = a := rfl

/--
warning: unused variable `b`
note: this linter can be disabled with `set_option linter.unusedVariables false`
---
warning: Current syntax:  ' Nat}{b : '
Expected syntax: ' Nat} {b :'

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {a : Nat}{b : Nat} : a = a := rfl

/--
warning: Current syntax:  'Nat}  '
Expected syntax: 'Nat} : a ='

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {a : Nat}  : a = a := rfl

/--
warning: Current syntax:  'alpha   ] '
Expected syntax: 'alpha] {a '

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {alpha} [Neg alpha   ] {a : Nat} : a = a := rfl

namespace List

variable {α β : Type} (r : α → α → Prop) (s : β → β → Prop)

-- The two infix are needed.  They "hide" a `quotPrecheck`
local infixl:50 " ≼ " => r
-- The two infix are needed.  They "hide" a `quotPrecheck`
local infixl:50 " ≼ " => s

/--
warning: The `commandStart` linter had some parsing issues: feel free to silence it and report this error!
note: this linter can be disabled with `set_option linter.style.commandStart.verbose false`
-/
#guard_msgs in
set_option linter.style.commandStart.verbose true in
example {a : α} (_ : a ≼ a) : 0 = 0 := rfl

end List

-- Test that the space between `aesop` and `(rule_sets ...)` is not linted.
@[aesop (rule_sets := [builtin]) safe apply] example : True := trivial

-- Test that `Prop` and `Type` that are not escaped with `«...»` do not cause problems.
def Prop.Hello := 0
def Type.Hello := 0

/--
warning: Current syntax:  'mple  '
Expected syntax: 'mple : Tru'

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
/-- Check that doc/strings do not get removed as comments. -/
example  : True := trivial
