/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean
import Mathlib.Lean.Expr.Basic

/-!
#  The "dependentTypeclass" linter

The "dependentTypeclass" linter emits a warning when there is a dependency among typeclass
assumptions.
-/

open Lean Elab Command

namespace Mathlib.Linter

/-- The "dependentTypeclass" linter emits a warning when there is a dependency among typeclass
assumptions.
 -/
register_option linter.dependentTypeclass : Bool := {
  defValue := true
  descr := "enable the dependentTypeclass linter"
}
def getBinders : Expr → Array String
  | .lam na type body bi =>
    let (l, r) := bi.brackets
    (getBinders body).push (s!"{l} {na} : {type}{r}")
  | .forallE na type body bi =>
    let (l, r) := bi.brackets
    (getBinders body).push (s!"{l} {na} : {type}{r}")
  | _ => default

/-- `getMinInstsFor d varDecls` takes as input a `bracketedBinder` `d` and an array of `varDecls`
of ``bracketedBinder`.
It assumes that `d` represents a typeclass assumption and it tries to synthesize an instance of
`d` from `varDecls` using `inferInstance` or `sorry`.
If `inferInstance` is successful, then it returns the `Expr`ession representing a proof of
`d` using `varDecls`.
Otherwise it returns `none`.
-/
def getMinInstsFor (d : TSyntax ``Lean.Parser.Term.bracketedBinder)
  (varDecls : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) :
      CommandElabM (Option Expr) := do
  let sc ← getScope
  let newName ← liftCoreM <| mkFreshUserName `hello
  let stxId ← `(declId| $(mkIdent newName))
  let tac ← `(tacticSeq| first | infer_instance | sorry)
  let defInst ← `(command| def $stxId : $(⟨d.raw[2]⟩) := by $tac)
  let noDvar := varDecls.filter (· != d)
  let decl := ←
    withScope (fun s => { s with varDecls := noDvar }) <|
      try
        elabCommand defInst
        if let some decl := (← getEnv).find? (sc.currNamespace ++ newName) then
          if let some val := decl.value? then
            if !(val.hasSorry) then
              return some val
            else return none
          else return none
        else return none
      catch _ => return none
  return decl

/-- `dependentTypeclassRef` is a counter to collect all the already-known-to-be-superfluous
typeclass assumptions. -/
initialize dependentTypeclassRef : IO.Ref (Array Syntax) ← IO.mkRef {}

namespace DependentTypeclass

/-- Gets the value of the `linter.dependentTypeclass` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.dependentTypeclass o

open PrettyPrinter in
@[inherit_doc Mathlib.Linter.linter.dependentTypeclass]
def dependentTypeclassLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    -- we first find `variable`s that could be inside an `in`
    if let some stx := stx.find? (·.isOfKind ``Lean.Parser.Command.variable) then
      -- and then we extract the actual "variables" in `variable <vars*>`
      match stx with
        | `(variable $vars*) =>
          let s ← get
          let sc ← getScope
          -- we add the "current" variables to the ones in scope, since otherwise the linter
          -- would "miss", as they are already outside of scope when the linter runs
          let varDecls := sc.varDecls ++ vars
          let insts := varDecls.filter (·.raw.isOfKind ``Lean.Parser.Term.instBinder)
          if insts.size ≤ 1 then return else
          let mut msgs := #[]
          for d in insts do
            if (← dependentTypeclassRef.get).contains d then continue
            let noDvar := varDecls.filter (· != d)
            let decl ← getMinInstsFor d noDvar
            if let some decl := decl then
              dependentTypeclassRef.modify (·.push d)
              let preString := (← liftTermElabM (ppExpr decl)).pretty
              let fmtStr := (preString.replace "fun " "").replace " => inferInstance" ""
              msgs := msgs.push (d, fmtStr)
          set s
          for (d, fmtStr) in msgs do
            Linter.logLint linter.dependentTypeclass d m!"Typeclass '{d}' follows from '{fmtStr}'"
            let binderPos := d.raw.getPos?
            let varsPos := stx.getPos?
            if binderPos.getD default < varsPos.getD default then
              logInfo m!"The assumptions '{fmtStr}' imply the earlier assumption '{d}'"
        | _=> return

initialize addLinter dependentTypeclassLinter

end DependentTypeclass

end Mathlib.Linter
