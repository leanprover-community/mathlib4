/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
import Mathlib.Tactic.Linter.MinImports
import Mathlib.Data.Int.Notation

/--
warning: The module doc-string for a file should be the first command after the imports.
Please, add a module doc-string before `/-!# Tests for the header payload consumers
-/
`.

Note: This linter can be disabled with `set_option linter.style.header false`
-/
#guard_msgs in
set_option linter.style.header true in

/-!
# Tests for the header payload consumers
-/

/-! The `header` linter stores the parsed module header in its state. The `minImports` linter
reads the parsed header for its end-of-file report. The command above enables the `header`
linter on the module doc-string, so the linter runs its checks and stores the payload. The
`#exit` command below then triggers the end-of-file report of the `minImports` linter, which
positions the "unneeded import" warning with the payload. -/

set_option linter.minImports.increases false

/-- info: Counting imports from here. -/
#guard_msgs in
#import_bumps

/--
warning: Imports increased to
[Mathlib.Data.Int.Notation]

New imports: [Mathlib.Data.Int.Notation]


Note: This linter can be disabled with `set_option linter.minImports false`
-/
#guard_msgs in
#guard (0 : ℤ) = 0

/--
warning: using 'exit' to interrupt Lean
---
warning: unneeded import 'Mathlib.Tactic.Linter.MinImports'
-/
#guard_msgs in
#exit

set_option linter.minImports false
