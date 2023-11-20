/-
Copyright (c) Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Aesop
import Mathlib.Tactic.Relation.Rfl
import Std.Tactic.Ext

/-!
# Configuration of `aesop` for Mathlib.

We add `intro` as an unsafe rule (so it can be backtracked if it doesn't work out).
Adding `intro` has the effect of allowing looking inside default transparency definitions for
lambdas.

We add Mathlib's version of `rfl`.
-/

open Lean Elab Tactic in
def Aesop.intro : TacticM Unit := do evalTactic (← `(tactic| intro))

-- We turn on `intro` inside `aesop` as an unsafe rule,
-- so we can attempt introductions through default reducibility definitions.
attribute [aesop unsafe tactic] Aesop.intro

-- We turn on the mathlib version of `rfl` inside `aesop`.
attribute [aesop safe tactic] Mathlib.Tactic.rflTac
