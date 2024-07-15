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
open PrettyPrinter
def getMinInstsFor (d : TSyntax ``Lean.Parser.Term.bracketedBinder)
  (varDecls : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) :
      CommandElabM (Option Expr) := do
  --let s ← get
  let sc ← getScope
  let newName ← liftCoreM <| mkFreshUserName `hello
  let stxId ← `(declId| $(mkIdent newName))
  let tac ← `(tacticSeq| first | infer_instance | sorry)
  let defInst ← `(command| def $stxId : $(⟨d.raw[2]⟩) := by $tac)
  --dbg_trace defInst
  let noDvar := varDecls.filter (· != d)
  --let decl := ←
  let decl := ←
    withScope (fun s => { s with varDecls := noDvar }) <|
      try
        elabCommand defInst
        --if !(← get).messages.hasErrors then
        --else
        if let some decl := (← getEnv).find? (sc.currNamespace ++ newName) then
          if let some val := decl.value? then
            if !(val.hasSorry) then
              --elabCommand (← `(#print $(⟨mkIdent (sc.currNamespace ++ newName)⟩)))
              --let sig ← addMessageContext <| MessageData.signature (sc.currNamespace ++ newName)
              --logInfo sig
              return some val
            else return none
          else return none
        else return none
      catch _ => return none
  --set s
  return decl

/-- `dependentTypeclassRef` is a counter to collect all the already-known-to-be-superfluous
typeclass assumptions. -/
initialize dependentTypeclassRef : IO.Ref (Array Syntax) ← IO.mkRef {}

namespace DependentTypeclass

/-- Gets the value of the `linter.dependentTypeclass` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.dependentTypeclass o

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
          --let mut implied := #[]
          --let mut msgs := #[]
          let mut msgs1 := #[]
          for d in insts do
            if (← dependentTypeclassRef.get).contains d then continue
            let noDvar := varDecls.filter (· != d)
            let decl ← getMinInstsFor d noDvar
            --set s
            --logInfo m!"fmfmf: {f!"{decl.getD default}".pretty}"
            --dbg_trace "{getBinders (decl.getD default)}\n"
            --dbg_trace "just computed: {decl}"
            --let newName ← liftCoreM <| mkFreshUserName `hello
            --let stxId ← `(declId| $(mkIdent newName))
            --let instLemma ←
            --  `(instance (priority := 1) $stxId : $(⟨d.raw[2]⟩) := $(mkIdent `inferInstance))
            ----dbg_trace instLemma
            --let decl := ←
            --  try
            --    withScope (fun s => { s with varDecls := noDvar }) <| elabCommand instLemma
            --    --if !(← get).messages.hasErrors then
            --    --  set s
            --    --else
            --    if let some decl := (← getEnv).find? (sc.currNamespace ++ newName) then
            --      if let some val := decl.value? then
            --        if !(val.hasSorry) then
            --          return some val
            --        else return none
            --      else return none
            --    else return none
            --  catch _ => return none
            if let some decl := decl then
              dependentTypeclassRef.modify fun r => r.push d
              --implied := implied.push (d, insts.filter (· != d))

              --Linter.logLint linter.dependentTypeclass d
              --  m!"Typeclass '{d}' follows from '{((← liftTermElabM do ppExpr decl).pretty.replace "fun " "[").replace " => inferInstance" "]"}'"
              let fmtStr :=
                ((← liftTermElabM (ppExpr decl)).pretty.replace "fun " "").replace " => inferInstance" ""
              msgs1 := msgs1.push (d, m!"Typeclass '{d}' follows from '{fmtStr}'")
            --msgs1 := msgs1.push m!"here '{d}': {getBinders (decl.getD default)}"
--                elabCommand (← `(#print $(mkIdent newName)))
--                if (← get).messages.hasErrors then
--                  set s
--                else
--                  dbg_trace decl.isSome
                  --dependentTypeclassRef.modify fun r => r.push d
                  --implied := implied.push (d, insts.filter (· != d))
            --msgs := msgs ++ (← get).messages.unreported.toArray
            --set s
            -- we remove "all" `d`s, to deal better with the variable update
            -- `variable (α : Type) [Add α] variable {α} [Add α]`
            --let noDvar := varDecls.filter (· != d)
--            withScope (fun s => { s with varDecls := noDvar }) <|
--              elabCommand (← `(command| #synth $(⟨d.raw[2]⟩)))
--            if (← get).messages.hasErrors then
--              set s
--            else
--              dependentTypeclassRef.modify fun r => r.push d
--              implied := implied.push (d, insts.filter (· != d))
              --set s
            --set s
          set s
          for (d, msg) in msgs1 do
            Linter.logLint linter.dependentTypeclass d msg
          --for (d, ctx) in implied do
          --  Linter.logLint linter.dependentTypeclass d m!"Typeclass '{d}' is implied by {ctx}"
          --logInfo m!"messages1: {msgs1}"
          --logInfo m!"messages: {← msgs.mapM (·.toString)}"
        | _=> return

initialize addLinter dependentTypeclassLinter

end DependentTypeclass

end Mathlib.Linter
