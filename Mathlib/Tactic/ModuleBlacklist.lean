/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Tactic.ModuleBlacklist.Core

/-!

## A blacklist for modules whose theorems are implementation details

We blacklist `Init.Omega`, `Init.Grind` and `Mathlib.Tactic`.

-/

blacklist_dir Init.Omega Init.Grind Mathlib.Tactic
