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

set_option autoImplicit true

macro_rules | `(tactic| gcongr_discharger) => `(tactic| positivity)

/-! # ≤, / -/

protected theorem Nat.div_le_div {a b c d : ℕ} (h1 : a ≤ b) (h2 : d ≤ c) (h3 : d ≠ 0) :
    a / c ≤ b / d :=
  calc a / c ≤ b / c := Nat.div_le_div_right h1
    _ ≤ b / d := Nat.div_le_div_left h2 (Nat.pos_of_ne_zero h3)

attribute [gcongr]
  Nat.div_le_div -- tt / tt
  Nat.div_le_div_left -- ff / tt
  Nat.div_le_div_right -- tt / ff
