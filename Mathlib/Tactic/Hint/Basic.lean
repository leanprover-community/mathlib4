/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Tactic.Hint.Core
import Mathlib.Tactic.InferParam
import Mathlib.Tactic.Constructor
import Mathlib.Tactic.SolveByElim

/-!
# Tactics for `hint`
-/

add_hint_tactic rfl

add_hint_tactic decide

add_hint_tactic assumption

-- tidy does something better here: it suggests the actual "intros X Y f" string.
-- perhaps add a wrapper?
add_hint_tactic intro

add_hint_tactic infer_param

add_hint_tactic dsimp at *

add_hint_tactic simp at *

-- TODO hook up to squeeze_simp?
add_hint_tactic fconstructor

add_hint_tactic injections

add_hint_tactic solve_by_elim

-- Porting note: TODO port this
-- add_hint_tactic unfold_aux
