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


-- embedded comments do not cause problems!
#guard_msgs in
open Nat in -- hi
example : True := trivial

-- embedded comments do not cause problems!
#guard_msgs in
open Nat in
 -- hi
example : True := trivial

-- embedded comments do not cause problems!
#guard_msgs in
open Nat in
  -- hi
example : True := trivial

structure X where
  /-- A doc -/
  x : Nat

open Nat in /- hi -/
example : True := trivial

-- The notation `0::[]` disables the linter
variable (h : 0::[] = [])

/--
warning: 'section' starts on column 1, but all commands should start at the beginning of the line.
note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
 section

/-
#eval
  let s := "example        f   g"
  let t := "example fg"
  Mathlib.Linter.parallelScan s t


#eval
  let s := "example  :   True :=trivial"
  let t := "example : True :=
    trivial"
  Mathlib.Linter.parallelScan s t
-/


/--
warning: extra space

Current syntax:  'mple    : Tr'
Expected syntax: 'mple : Tru'

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example    : True := trivial

/--
warning: extra space

Current syntax:  'mple      /-dα'
Expected syntax: 'ple  /-dαα'

note: this linter can be disabled with `set_option linter.style.commandStart false`
---
warning: extra space

Current syntax:  'κκ-/     :  T'
Expected syntax: 'κκ-/ : Tru'

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example      /-dαακdαακdαακκ-/     :  True :=trivial

/-- A doc string -/
-- comment
example : True := trivial

/--
warning: extra space

Current syntax:  'mple  :  T'
Expected syntax: 'mple : Tru'

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example  :  True :=trivial

/--
warning: missing space

Current syntax:  'le (a: Nat'
Expected syntax: 'le (a : Na'

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
variable (a: Nat)

/--
warning: missing space

Current syntax:  'e (_a: Nat'
Expected syntax: 'e (_a : Na'

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example (_a: Nat) : True := trivial

/--
warning: missing space

Current syntax:  'le {a: Nat'
Expected syntax: 'le {a : Na'

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {a: Nat} : a = a := rfl

/-
#eval
  let l := "hac d"
  let m := "h  acd"
  Mathlib.Linter.parallelScan l m
-/

set_option linter.style.commandStart.verbose true in
/--
a
b
c
d -/
example (_a : Nat) (_b : Int) : True := trivial

/--
warning: missing space

Current syntax:  ' {a :Nat} '
Expected syntax: ' {a : Nat}'

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {a :Nat} : a = a := rfl

/--
warning: extra space

Current syntax:  'mple  {a :'
Expected syntax: 'mple {a : '

note: this linter can be disabled with `set_option linter.style.commandStart false`
---
warning: missing space

Current syntax:  ' {a :Nat} '
Expected syntax: ' {a : Nat}'

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example  {a :Nat} : a = a := rfl

/--
warning: unused variable `b`
note: this linter can be disabled with `set_option linter.unusedVariables false`
---
warning: missing space

Current syntax:  ' Nat}{b : '
Expected syntax: ' Nat} {b :'

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {a : Nat}{b : Nat} : a = a := rfl

/--
warning: extra space

Current syntax:  'Nat}  : a '
Expected syntax: 'Nat} : a ='

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {a : Nat}  : a = a := rfl

/--
warning: extra space

Current syntax:  'alpha   ] {a'
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
warning: extra space

Current syntax:  'mple  : Tr'
Expected syntax: 'mple : Tru'

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
/-- Check that doc/strings do not get removed as comments. -/
example  : True := trivial
