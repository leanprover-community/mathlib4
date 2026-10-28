/-
Copyright (c) 2026 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import Mathlib.Tactic.Linter.Header

set_option linter.style.header true

set_option doc.verso.module true

set_option doc.verso true

set_option doc.verso false

-- A comment

set_option doc.verso true

set_option doc.verso.suggestions true

/- Test that the module header linter correctly complains about missing headers,
even if we have a lot of `set_option`s above. -/

/--
warning: The module doc-string for a file should be the first command after the imports
and any necessary `set_option` commands.
Please, add a module doc-string (`/-! ... -/`) before `def foo :=
  37`.

Hint: Type `m(odule docstring) + [tab]` to insert a template via snippet.

Note: This linter can be disabled with `set_option linter.style.header false`
-/
#guard_msgs in
set_option linter.style.header true in
set_option doc.verso true in

def foo := 37
