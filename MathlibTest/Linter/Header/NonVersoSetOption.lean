import Mathlib.Tactic.Linter.Header

set_option linter.style.header true

/--
warning: The module doc-string for a file should be the first command after the imports
and any necessary `set_option` commands.
Please, add a module doc-string (`/-! ... -/`) before `set_option linter.omit true`.

Hint: Type `m(odule docstring) + [tab]` to insert a template via snippet.

Note: This linter can be disabled with `set_option linter.style.header false`
-/
#guard_msgs in
set_option linter.omit true -- Random linter option defined in core Lean

/-! # Module doc ... -/
