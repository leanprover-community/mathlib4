/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Mathlib.Init
import Aesop

/-!
# Category Theory Rule Set

This module defines the `CategoryTheory` Aesop rule set which is used by the
`aesop_cat` tactic. Aesop rule sets only become visible once the file in which
they're declared is imported, so we must put this declaration into its own file.
-/

declare_aesop_rule_sets [CategoryTheory]

/-- Option to control whether the category theory library should use `grind` or `aesop`
in the `cat_disch` tactic, which is widely used as an autoparameter. -/
register_option mathlib.tactic.category.grind : Bool := {
  defValue := false
  descr := "The category theory library should use `grind` instead of `aesop`."
}

/-- Log a message whenever the category theory discharger uses `grind`. -/
register_option mathlib.tactic.category.log_grind : Bool := {
  defValue := false
  descr := "Log a message whenever the category theory discharger uses `grind`."
}

/-- Log a message whenever the category theory discharger uses `aesop`. -/
register_option mathlib.tactic.category.log_aesop : Bool := {
  defValue := false
  descr := "Log a message whenever the category theory discharger uses `aesop`."
}
