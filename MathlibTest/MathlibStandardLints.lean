import Mathlib.Tactic.Linter.HashCommandLinter

-- No complaints if the default linters are not enabled.
/--
-/
#guard_msgs in
#guard true

set_option linter.mathlibStandard true

/--
warning: `#`-commands, such as '#guard', are not allowed in 'Mathlib'
note: this linter can be disabled with `set_option linter.hashCommand false`
-/
#guard_msgs in
#guard true

-- Explicitly overriding a linter should silence it
set_option linter.hashCommand false in
#guard_msgs in
#guard true
