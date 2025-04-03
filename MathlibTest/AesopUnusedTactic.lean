/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop
import MathlibLinters.UnusedTactic

set_option linter.unusedTactic true

/-
The unused tactic linter should not consider tactics unused if they appear in
Aesop's `add_aesop_rules` command...
-/
add_aesop_rules safe (by simp)

/-
... or in an `add` clause.
-/
example : True := by
  aesop (add safe (by simp))
