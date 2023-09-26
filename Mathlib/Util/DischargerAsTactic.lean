/-
Copyright (c) 2023 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Std.Tactic.Exact

/-!
## Dischargers for `simp` to tactics

This file defines a wrapper for `Simp.Discharger`s as regular tactics, that allows them to be
used via the tactic frontend of `simp` via `simp (discharger := wrapSimpDischarger my_discharger)`.
-/

open Lean Meta Elab Tactic

/-- Wrap an simp discharger (a function `Expr → SimpM (Option Expr)`) as a tactic,
so that it can be passed as an argument to `simp (discharger := foo)`.
This is inverse to `mkDischargeWrapper`. -/
def wrapSimpDischarger (dis : Simp.Discharge) : TacticM Unit := do
  let eS : Lean.Meta.Simp.State := {}
  let eC : Lean.Meta.Simp.Context := {}
  let (some a, _) ← liftM <| StateRefT'.run (ReaderT.run (dis <| ← getMainTarget) eC) eS | failure
  (← getMainGoal).assignIfDefeq a
