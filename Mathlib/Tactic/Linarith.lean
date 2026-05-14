/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module -- shake: keep-all

public meta import Mathlib.Tactic.Hint
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive

/-!
We register `linarith` with the `hint` tactic.
-/

public meta section

register_hint 100 linarith
