import Mathlib.Tactic.Linter.PedanticLinter

set_option linter.pedantic false

/--
info: "a   a"
---
warning: source context
'al "    a '
'al " a a\n'
pretty-printed context
note: this linter can be disabled with `set_option linter.pedantic false`
-/
#guard_msgs in
set_option linter.pedantic true in
#eval "    a   a\n       "    |>.trim

/--
warning: source context
'rd ¬   fa'
'rd ¬false'
pretty-printed context
note: this linter can be disabled with `set_option linter.pedantic false`
-/
#guard_msgs in
set_option linter.pedantic true in
#guard ¬   false

/--
warning: source context
'le {a: Nat'
'le {a : Na'
pretty-printed context
note: this linter can be disabled with `set_option linter.pedantic false`
-/
#guard_msgs in
set_option linter.pedantic true in
variable {a: Nat}

/--
warning: source context
' {a :Nat}'
' {a : Nat}'
pretty-printed context
note: this linter can be disabled with `set_option linter.pedantic false`
-/
#guard_msgs in
set_option linter.pedantic true in
variable {a :Nat}

/--
info: (fun x x_1 => x + x_1) 0 1 : Nat
---
warning: source context
'k (·+·) '
'k (· + ·'
pretty-printed context
note: this linter can be disabled with `set_option linter.pedantic false`
-/
#guard_msgs in
set_option linter.pedantic true in
#check (·+·) 0 1

#guard_msgs in
set_option linter.pedantic true in
-- check that trailing comments do not trigger the linter
example : 0 = 0 := by
  rw [] -- this goal is closed by the `rfl` implied by `rw`
