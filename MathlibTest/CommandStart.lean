import Aesop.Frontend.Attribute
import Mathlib.Tactic.Linter.CommandStart

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

set_option linter.style.commandStart.verbose true in
example {a : α} (_ : a ≼ a) : 0 = 0 := rfl

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
