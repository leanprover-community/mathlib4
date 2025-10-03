/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Init
import Lean.Elab.Term

/-!
# Additions to `Lean.Elab.Term`
-/

namespace Lean.Elab.Term

/-- Fully elaborates the term `patt`, allowing typeclass inference failure,
but while setting `errToSorry` to false.
Typeclass failures result in plain metavariables.
Instantiates all assigned metavariables. -/
def elabPattern (patt : Term) (expectedType? : Option Expr) : TermElabM Expr := do
  withTheReader Term.Context ({ · with ignoreTCFailures := true, errToSorry := false }) <|
    withSynthesizeLight do
      let t ← elabTerm patt expectedType?
      synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
      instantiateMVars t

open Meta

/-- Try to infer the universe of an expression `e` -/
def _root_.Lean.Expr.getUniverse (e : Expr) : TermElabM (Level) := do
    if let .sort (.succ u) ← inferType e >>= instantiateMVars then
      return u
    else
      throwError m!"Could not find universe of {e}."

end Lean.Elab.Term
