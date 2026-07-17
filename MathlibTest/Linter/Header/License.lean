/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/

import Mathlib.Tactic.Linter.Header

/- Test that the expected copyright license line is configurable via `linter.style.header.license`
(default: the Apache LICENSE line). We deliberately omit a module doc-string: the linter only checks
the copyright for a command in the header region (before any module doc-string), so the first
command below both triggers the copyright check and the incidental "missing module doc-string"
warning. Setting a custom expected license flags this file's own (Apache default) second line. -/

/--
warning: * 'Released under Apache 2.0 license as described in the file LICENSE.':
Second copyright line should be "Released under the Custom License."


Note: This linter can be disabled with `set_option linter.style.header false`
---
warning: The module doc-string for a file should be the first command after the imports.
Please, add a module doc-string before `def foo : Nat :=
  37`.

Note: This linter can be disabled with `set_option linter.style.header false`
-/
#guard_msgs in
set_option linter.style.header.license "Released under the Custom License." in
set_option linter.style.header true in
def foo : Nat := 37
