/-
Copyright (c) 2023 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth
-/
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr.Core

/-! # Setup for the `gcongr` tactic

The core implementation of the `gcongr` ("generalized congruence") tactic is in the file
`Tactic.GCongr.Core`.  In this file we set it up for use across the library by tagging a minimal
set of lemmas with the attribute `@[gcongr]` and by listing `positivity` as a first-pass
discharger for side goals (`gcongr_discharger`). -/

macro_rules | `(tactic| gcongr_discharger) => `(tactic| positivity)

/-! # ≤, / -/

attribute [gcongr]
  Nat.div_le_div_left -- ff / tt
  Nat.div_le_div_right -- tt / ff
