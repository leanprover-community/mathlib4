import Lean.Elab.Tactic.Basic

namespace Lean.Elab
open Meta

namespace Tactic

@[inline] private def TacticM.runCore (x : TacticM α) (ctx : Context) (s : State) : TermElabM (α × State) :=
  x ctx |>.run s

@[inline] private def TacticM.runCore' (x : TacticM α) (ctx : Context) (s : State) : TermElabM α :=
  Prod.fst <$> x.runCore ctx s

/-- A variant of core's `Lean.Elab.Tactic.run` which captures the return value of the tactic. -/
-- TODO We could replace the version in core with a wrapper around this.
def run' (mvarId : MVarId) (x : TacticM α) : TermElabM (Option α × List MVarId) :=
  mvarId.withContext do
   let pendingMVarsSaved := (← get).pendingMVars
   modify fun s => { s with pendingMVars := [] }
   let aux : TacticM (Option α × List MVarId) :=
     /- Important: the following `try` does not backtrack the state.
        This is intentional because we don't want to backtrack the error messages when we catch the "abort internal exception"
        We must define `run` here because we define `MonadExcept` instance for `TacticM` -/
     try
       return ⟨← x, ← getUnsolvedGoals⟩
     catch ex =>
       if isAbortTacticException ex then
         return ⟨none, ← getUnsolvedGoals⟩
       else
         throw ex
   try
     aux.runCore' { elaborator := .anonymous } { goals := [mvarId] }
   finally
     modify fun s => { s with pendingMVars := pendingMVarsSaved }
