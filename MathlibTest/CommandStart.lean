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
