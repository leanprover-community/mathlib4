/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Hint

@[expose] public section

/-!
We register `linarith` with the `hint` tactic.
-/

register_hint (priority := 100) linarith
