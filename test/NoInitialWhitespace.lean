import Mathlib.Tactic.Linter.Lint

/--
warning: '#guard true' starts on column 2.
Please, do not leave any whitespace before this command!
note: this linter can be disabled with `set_option linter.noInitialWhitespace false`
-/
#guard_msgs in
  #guard true

#guard_msgs in #guard true

/--
warning: '#guard true' starts on column 17.
Please, do not leave any whitespace before this command!
note: this linter can be disabled with `set_option linter.noInitialWhitespace false`
-/
  #guard_msgs in #guard true

/--
warning: '#guard true' starts on column 17.
Please, do not leave any whitespace before this command!
note: this linter can be disabled with `set_option linter.noInitialWhitespace false`
---
error: ❌ Docstring on `#guard_msgs` does not match generated message:

warning: '#guard true' starts on column 17.
Please, do not leave any whitespace before this command!
note: this linter can be disabled with `set_option linter.noInitialWhitespace false`
-/
#guard_msgs in
  #guard_msgs in #guard true

/--
warning: '#guard true' starts on column 2.
Please, do not leave any whitespace before this command!
note: this linter can be disabled with `set_option linter.noInitialWhitespace false`
-/
#guard_msgs in
set_option linter.noInitialWhitespace true in
  #guard true
