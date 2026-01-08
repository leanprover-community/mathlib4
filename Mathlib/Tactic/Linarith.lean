/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public meta import Mathlib.Tactic.Hint
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum

/-!
We register `linarith` with the `hint` tactic.
-/

public meta section

register_hint 100 linarith
