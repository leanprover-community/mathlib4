/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Aesop
import Qq

/-!
# Aesop rule set for finsets

This file defines `finsetNonempty`, an aesop rule set to prove that a given finset is nonempty.
-/

-- `finsetNonempty` rules try to prove that a given finset is nonempty,
-- for use in positivity extensions.
declare_aesop_rule_sets [finsetNonempty] (default := true)

open Qq Lean Meta
