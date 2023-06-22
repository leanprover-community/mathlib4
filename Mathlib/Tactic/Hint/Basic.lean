/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Tactic.Hint.Core

/-!
# Tactics for `hint`
-/

add_hint_tactic rfl

add_hint_tactic decide

add_hint_tactic assumption

-- tidy does something better here: it suggests the actual "intros X Y f" string.
-- perhaps add a wrapper?
add_hint_tactic intro
