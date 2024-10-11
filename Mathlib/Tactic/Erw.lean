/-
Copyright (c) 2024 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import Mathlib.Tactic.TryThis

/-!
# Extension to the `erw` tactic

This file adds a macro rule to the `erw` tactic that first tries to run the `rw` tactic at the
faster `reducible` transparency, and adds a suggestion if that also succeeds.

Note that `rw` succeeding is not the same as `rw` and `erw` doing exactly the same rewrite: they may
have operated on different subterms. Since the suggested `rw` may not be an exact replacement, we
display a hint explaining what to do if this happens.
-/

/-- If we call `erw`, first try running regular `rw` and warn if that succeds. -/
macro_rules
  | `(tactic| erw $s $(loc)?) =>
    `(tactic|
      try_this rw $(.none)? $s $(loc)?;
      trace "Hint: `rw` succeeded here, but may have performed a different rewrite than `erw` would.
If `erw` really is needed, try preceding this line with a `rw` to get rid of the other occurrences,
or use `conv` to specify exactly which subterm to rewrite.")
