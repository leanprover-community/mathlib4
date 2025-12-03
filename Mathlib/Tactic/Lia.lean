/-
Copyright (c) 2024 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib contributors
-/
module

public import Mathlib.Init

/-!
# `lia` tactic

This file defines `lia` as an alias for `cutsat`, a linear integer arithmetic tactic.
-/

public meta section

/-- `lia` is an alias for the `cutsat` tactic, which solves linear integer arithmetic goals. -/
syntax (name := tacticLia) "lia" : tactic
macro_rules | `(tactic| lia) => `(tactic| cutsat)

end
