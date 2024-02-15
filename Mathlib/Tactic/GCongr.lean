/-
Copyright (c) 2023 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth
-/
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.GCongr.Core

/-! # Setup for the `gcongr` tactic

The core implementation of the `gcongr` ("generalized congruence") tactic is in the file
`Tactic.GCongr.Core`. In this file we set it up for use across the library by listing
`positivity` as a first-pass discharger for side goals (`gcongr_discharger`). -/

macro_rules | `(tactic| gcongr_discharger) => `(tactic| positivity)
