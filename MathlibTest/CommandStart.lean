import Aesop.Frontend.Attribute
import Mathlib.Tactic.Linter.CommandStart

set_option linter.style.commandStart true

-- Strings are ignored by the linter.
variable (a : String := "  ")

run_cmd
  for _ in [0] do
    let _ ← `(
      end)

def Card : Type → Nat := fun _ => 0

/-- Symbols for use by all kinds of grammars. -/
inductive Symbol (T N : Type)
  /-- Terminal symbols (of the same type as the language) -/
  | terminal (t : T) : Symbol T N
  /-- Nonterminal symbols (must not be present when the word being generated is finalized) -/
  | nonterminal (n : N) : Symbol T N
deriving
  DecidableEq, Repr

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
warning: This part of the code
  'example    : True'

should be written as
  'example : True'

Notice the extra space in the source code.

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example    : True := trivial

/-- A doc string -/
-- comment
example : True := trivial

/--
warning: This part of the code
  'example  :  True'

should be written as
  'example : True'

Notice the extra space in the source code.

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example  :  True :=trivial

/--
warning: This part of the code
  '(a: Nat)'

should be written as
  '(a : Nat)'

Notice the missing space in the source code.

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
variable (a: Nat)

/--
warning: This part of the code
  '(_a: Nat)'

should be written as
  '(_a : Nat)'

Notice the missing space in the source code.

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example (_a: Nat) : True := trivial

/--
warning: This part of the code
  '{a: Nat}'

should be written as
  '{a : Nat}'

Notice the missing space in the source code.

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
warning: This part of the code
  ':Nat}'

should be written as
  ': Nat}'

Notice the missing space in the source code.

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {a :Nat} : a = a := rfl

/--
warning: This part of the code
  'example  {a :Nat}'

should be written as
  'example {a :'

Notice the extra space in the source code.

note: this linter can be disabled with `set_option linter.style.commandStart false`
---
warning: This part of the code
  ':Nat}'

should be written as
  ': Nat}'

Notice the missing space in the source code.

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example  {a :Nat} : a = a := rfl

/--
warning: unused variable `b`
note: this linter can be disabled with `set_option linter.unusedVariables false`
---
warning: This part of the code
  'Nat}{b :'

should be written as
  'Nat} {b :'

Notice the missing space in the source code.

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {a : Nat}{b : Nat} : a = a := rfl

/--
warning: This part of the code
  'Nat}  : a'

should be written as
  'Nat} : a ='

Notice the extra space in the source code.

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
example {a : Nat}  : a = a := rfl

/--
warning: This part of the code
  'alpha   ] {a'

should be written as
  'alpha] {a'

Notice the extra space in the source code.

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
warning: This part of the code
  'example  : True'

should be written as
  'example : True'

Notice the extra space in the source code.

note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
/-- Check that doc/strings do not get removed as comments. -/
example  : True := trivial
