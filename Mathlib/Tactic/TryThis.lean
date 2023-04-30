/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Tactic.TryThis

/-!
# Additions to "Try this" support

This file could be upstreamed to `Std`.
-/

open Lean Elab Elab.Tactic PrettyPrinter Meta Std.Tactic.TryThis

/-- Add a suggestion for `have : t := e`. (TODO: this depends on code action support) -/
def addHaveSuggestion (origTac : Syntax) (t? : Option Expr) (e : Expr) :
    TermElabM Unit := do
  let estx ← delabToRefinableSyntax e
  let prop ← isProp (← inferType e)
  let tac ← if let some t := t? then
    let tstx ← delabToRefinableSyntax t
    if prop then
      `(tactic| have : $tstx := $estx)
    else
      `(tactic| let this : $tstx := $estx)
  else
    if prop then
      `(tactic| have := $estx)
    else
      `(tactic| let this := $estx)
  addSuggestion origTac tac
