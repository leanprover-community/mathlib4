/-
Copyright (c) 2023 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth
-/
import Mathlib.Tactic.GCongr.CoreAttrs
import Mathlib.Tactic.Hint

/-! # Setup for the `gcongr` tactic

The core implementation of the `gcongr` ("generalized congruence") tactic is in the file
`Tactic.GCongr.Core`. -/

/-!
We register `gcongr` with the `hint` tactic.
-/

register_hint gcongr
