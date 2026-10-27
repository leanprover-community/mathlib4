module

import Mathlib.Init

set_option linter.style.numericProjection true

open Lean

variable (foo : Rat)

/--
warning: Numeric projections are disallowed.

  [apply] Instead, use `.den`.

To exempt terms of type `Rat`, add `@[allow_numeric_proj]` at the declaration site of `Rat`.

Note: This linter can be disabled with `set_option linter.style.numericProjection false`
-/
#guard_msgs in
example := foo.2
