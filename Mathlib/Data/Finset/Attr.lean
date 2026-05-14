/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public meta import Aesop.Frontend.Extension
import Aesop.Frontend.Basic
import Aesop.Frontend.Command
import Mathlib.Init

/-!
# Aesop rule set for finsets

This file defines `finsetNonempty`, an aesop rule set to prove that a given finset is nonempty.
-/

public section

-- `finsetNonempty` rules try to prove that a given finset is nonempty,
-- for use in positivity extensions.
declare_aesop_rule_sets [finsetNonempty] (default := true)
