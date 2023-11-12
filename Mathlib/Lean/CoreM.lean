/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Thomas R. Murrills
-/
import Lean
import Mathlib.Tactic.ToExpr

/-!
# Additional functions using `CoreM` state.
-/

set_option autoImplicit true

open Lean Core

/--
Run a `CoreM α` in a fresh `Environment` with specified `modules : List Name` imported.
-/
def CoreM.withImportModules (modules : Array Name) (run : CoreM α)
    (searchPath : Option SearchPath := none) (options : Options := {})
    (trustLevel : UInt32 := 0) (fileName := "") :
    IO α := unsafe do
  if let some sp := searchPath then searchPathRef.set sp
  Lean.withImportModules (modules.map (Import.mk · false)) options trustLevel fun env =>
    let ctx := {fileName, options, fileMap := default}
    let state := {env}
    Prod.fst <$> (CoreM.toIO · ctx state) do
      run

/--
Evaluates `k`, and returns the result along with an indicator of whether new errors were
produced during its execution.

Note that `hasNewErrors` only counts the number of errors present in `(← Core.getMessageLog).msgs`
before and after `k`; if `k` has the ability to e.g. reset the `CoreM` state,
`hasNewErrors` may not behave as expected.
-/
def hasNewErrors [Monad m] [MonadOptions m] [MonadLiftT CoreM m] (k : m α) : m (α × Bool) := do
  let warningAsError := warningAsError.get (← getOptions)
  let isError : MessageSeverity → Bool
  | .error => true
  | .warning => warningAsError
  | _ => false
  let getNumErrors :=
    return (← Core.getMessageLog).msgs.filter (fun msg => isError msg.severity) |>.size
  let numErrors ← getNumErrors
  let val ← k
  let numErrors' ← getNumErrors
  return (val, numErrors < numErrors')
