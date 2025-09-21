import Mathlib.Tactic.Linter.PPRoundtrip

/--
info: "a   a"
---
warning: source context
'al "    a '
'al " a a\n'
pretty-printed context

Note: This linter can be disabled with `set_option linter.ppRoundtrip false`
-/
#guard_msgs in
set_option linter.ppRoundtrip true in
#eval "    a   a\n       "    |>.trim

/--
warning: source context
'rd ¬   fa'
'rd ¬false'
pretty-printed context

Note: This linter can be disabled with `set_option linter.ppRoundtrip false`
-/
#guard_msgs in
set_option linter.ppRoundtrip true in
#guard ¬   false

/--
warning: source context
'le {a: Nat'
'le {a : Na'
pretty-printed context

Note: This linter can be disabled with `set_option linter.ppRoundtrip false`
-/
#guard_msgs in
set_option linter.ppRoundtrip true in
variable {a: Nat}

/--
warning: source context
' {a :Nat}'
' {a : Nat}'
pretty-printed context

Note: This linter can be disabled with `set_option linter.ppRoundtrip false`
-/
#guard_msgs in
set_option linter.ppRoundtrip true in
variable {a :Nat}

/--
info: (fun x1 x2 => x1 + x2) 0 1 : Nat
---
warning: source context
'k (·+·) '
'k (· + ·'
pretty-printed context

Note: This linter can be disabled with `set_option linter.ppRoundtrip false`
-/
#guard_msgs in
set_option linter.ppRoundtrip true in
#check (·+·) 0 1

#guard_msgs in
set_option linter.ppRoundtrip true in
-- check that trailing comments do not trigger the linter
example : 0 = 0 := by
  rw [] -- this goal is closed by the `rfl` implied by `rw`
