/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Thomas R. Murrills
-/
import Lean.Elab

/-!
# Additions to `Lean.Elab.Term`
-/

namespace Lean.Elab.Term

set_option autoImplicit true

/-- Fully elaborates the term `patt`, allowing typeclass inference failure,
but while setting `errToSorry` to false.
Typeclass failures result in plain metavariables.
Instantiates all assigned metavariables. -/
def elabPattern (patt : Term) (expectedType? : Option Expr) : TermElabM Expr := do
  withTheReader Term.Context ({ · with ignoreTCFailures := true, errToSorry := false }) <|
    withSynthesizeLight do
      let t ← elabTerm patt expectedType?
      synthesizeSyntheticMVars (mayPostpone := false) (ignoreStuckTC := true)
      instantiateMVars t

/-- Given a combinator `f {α} : TermElabM α → TermElabM α` and a way to run `m` in `TermElabM`,
turn `f` into a combinator of type `m α → m α`. -/
@[inline] def mapTermElabM [MonadControlT TermElabM m] [Monad m]
    (f : forall {α}, TermElabM α → TermElabM α) {α} (x : m α) : m α :=
  controlAt TermElabM fun runInBase => f <| runInBase x

@[inline] private def withoutModifyingStateImp (restoreInfo : Bool) (x : TermElabM α) :
    TermElabM α := do
  let s ← saveState
  try
    withSaveInfoContextUnless restoreInfo x
  finally
    s.restore restoreInfo
where
  withSaveInfoContextUnless : Bool → TermElabM α → TermElabM α
  | true  => fun x => x
  | false => withSaveInfoContext

/-- A "safe" version of `withoutModifyingState` for monads in which we're running `TermElabM` (e.g.
`TermElabM`, `TacticM`). If `restoreInfo := false` (the default), we wrap the execution in
`withSaveInfoContext`. If `restoreInfo := true`, we restore the infotrees to their values before
execution.

Note that `withoutModifyingState` does not restore the infotrees to their values before the monad
execution. However, `MVarId`s can be introduced to the infotree, which now might be unknown. For
this reason, we either need to save the context before restoring the rest of the state or restore
the infotree state as well. -/
def withoutModifyingState [MonadControlT TermElabM m] [Monad m] (x : m α)
    (restoreInfo := false) : m α :=
  mapTermElabM (withoutModifyingStateImp restoreInfo) x
