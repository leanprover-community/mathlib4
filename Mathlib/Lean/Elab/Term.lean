/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean.Elab

/-!
# Additions to `Lean.Elab.Term`
-/

namespace Lean.Elab.Term

/-- Fully elaborates the term `patt`, allowing typeclass inference failure.
Failures result in plain metavariables.
Instantiates all assigned metavariables. -/
def elabPattern (patt : Term) (expectedType? : Option Expr) : TermElabM Expr := do
  withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) <|
    withSynthesizeLight do
      let t ← elabTerm patt expectedType?
      synthesizeSyntheticMVars (mayPostpone := false) (ignoreStuckTC := true)
      instantiateMVars t
