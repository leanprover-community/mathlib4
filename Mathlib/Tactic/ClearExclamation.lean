/-
Copyright (c) 2022 Joshua Clune. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joshua Clune
-/
import Lean.Elab.Tactic.ElabTerm

/-! # `clear!` tactic -/

namespace Mathlib.Tactic
open Lean Meta Elab.Tactic

/-- A variant of `clear` which clears not only the given hypotheses but also any other hypotheses
    depending on them -/
elab (name := clear!) "clear!" hs:(ppSpace colGt ident)* : tactic => do
  let fvarIds ← getFVarIds hs
  liftMetaTactic1 fun goal ↦ do
    goal.tryClearMany <| (← collectForwardDeps (fvarIds.map .fvar) true).map (·.fvarId!)
