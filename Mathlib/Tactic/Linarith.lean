/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public meta import Mathlib.Tactic.Linarith.Frontend
public meta import Mathlib.Tactic.NormNum
public meta import Mathlib.Tactic.Hint

public meta section

/-!
We register `linarith` with the `hint` tactic.
-/

register_hint (priority := 100) linarith
