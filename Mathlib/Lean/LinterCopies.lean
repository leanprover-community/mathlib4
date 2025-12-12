module

public meta import Lean
public import Mathlib.Tactic.Linter.UnusedInstancesInTypeCopy
import all Mathlib.Tactic.Linter.UnusedInstancesInTypeCopy


open Lean Meta Elab Term Command

-- TODO: run on all command syntax, not just decls. Do nonlocally.

open Mathlib.Linter.UnusedInstancesInType

meta section

local instance : Insert Name NameSet where
  insert := fun n s => s.insert n

def runCopies : Linter where run stx := do
  if stx.isOfKind ``Parser.Command.eoi then
    let opts := (← getOptions).setBool `profiler true
    let consts := (← getEnv).constants.map₁
    let badRecs : NameSet := {`IO.Promise.casesOn, `IO.Promise.recOn, `IO.Promise.rec}
    profileitM Exception "control" opts do
      for (n,_) in consts do
        liftTermElabM do unless n.isInternalDetail || badRecs.contains n do pure ()
    profileitM Exception "bench" opts do
      for (n,cinfo) in consts do
        unless n.isInternalDetail || badRecs.contains n do
          cinfo.toConstantVal.onUnusedInstancesInTypeWhere isDecidableVariant
            fun _ _ => pure ()

initialize addLinter runCopies
