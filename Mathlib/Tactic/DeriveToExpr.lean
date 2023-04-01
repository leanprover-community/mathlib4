/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean

/-!
# A `ToExpr` derive handler

This module defines a `ToExpr` derive handler for inductive types. It supports mutually inductive
types as well.

It is originally based on the `Repr` derived handler from Lean 4 itself.

This has a universe level limitation: it assumes all level variables are for `Type` (see
where `levelOne` is used in this file).

-/

namespace Mathlib.Deriving.ToExpr

open Lean Elab Lean.Parser.Term
open Meta Command Deriving

def mkToExprHeader (indVal : InductiveVal) : TermElabM Header := do
  let header ← mkHeader ``ToExpr 1 indVal
  return header

def mkToExprBody (header : Header) (indVal : InductiveVal) (auxFunName : Name) :
    TermElabM Term := do
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)
where
  mkAlts : TermElabM (Array (TSyntax ``matchAlt)) := do
    let mut alts := #[]
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let alt ← forallTelescopeReducing ctorInfo.type fun xs _ => do
        let mut patterns := #[]
        -- add `_` pattern for indices
        for _ in [:indVal.numIndices] do
          patterns := patterns.push (← `(_))
        let mut ctorArgs := #[]
        let mut rhsArgs : Array Term := #[]
        let mkArg (x : Expr) (a : Term) : TermElabM Term := do
          if (← inferType x).isAppOf indVal.name then
            `($(mkIdent auxFunName) $a)
          else if ← Meta.isType x then
            `(toTypeExpr $a)
          else
            `(toExpr $a)
        -- add `_` pattern for inductive parameters, which are inaccessible
        for i in [:ctorInfo.numParams] do
          let a := mkIdent header.argNames[i]!
          ctorArgs := ctorArgs.push (← `(_))
          rhsArgs := rhsArgs.push <| ← mkArg xs[i]! a
        for i in [:ctorInfo.numFields] do
          let a := mkIdent (← mkFreshUserName `a)
          ctorArgs := ctorArgs.push a
          rhsArgs := rhsArgs.push <| ← mkArg xs[ctorInfo.numParams + i]! a
        patterns := patterns.push (← `(@$(mkIdent ctorName):ident $ctorArgs:term*))
        let levels ← indVal.levelParams.toArray.mapM (fun _ => `(levelOne))
        let rhs : Term ←
          `(mkAppN (Expr.const $(quote ctorInfo.name) [$levels,*]) #[$rhsArgs,*])
        `(matchAltExpr| | $[$patterns:term],* => $rhs)
      alts := alts.push alt
    return alts

def mkToTypeExpr (argNames : Array Name) (indVal : InductiveVal) : TermElabM Term := do
  let levels ← indVal.levelParams.toArray.mapM (fun _ => `(levelOne))
  forallTelescopeReducing indVal.type fun xs _ => do
    let mut args : Array Term := #[]
    for i in [:xs.size] do
      let x := xs[i]!
      let a := mkIdent argNames[i]!
      if ← Meta.isType x then
        args := args.push <| ← `(toTypeExpr $a)
      else
        args := args.push <| ← `(toExpr $a)
    `(mkAppN (Expr.const $(quote indVal.name) [$levels,*]) #[$args,*])

def mkLocalInstanceLetDecls (ctx : Deriving.Context) (argNames : Array Name) :
    TermElabM (Array (TSyntax ``Parser.Term.letDecl)) := do
  let mut letDecls := #[]
  for i in [:ctx.typeInfos.size] do
    let indVal       := ctx.typeInfos[i]!
    let auxFunName   := ctx.auxFunNames[i]!
    let currArgNames ← mkInductArgNames indVal
    let numParams    := indVal.numParams
    let currIndices  := currArgNames[numParams:]
    let binders      ← mkImplicitBinders currIndices
    let argNamesNew  := argNames[:numParams] ++ currIndices
    let indType      ← mkInductiveApp indVal argNamesNew
    let instName     ← mkFreshUserName `localinst
    let toTypeExpr   ← mkToTypeExpr argNames indVal
    let letDecl      ← `(Parser.Term.letDecl| $(mkIdent instName):ident $binders:implicitBinder* :
                            ToExpr $indType :=
                          { toExpr := $(mkIdent auxFunName), toTypeExpr := $toTypeExpr })
    letDecls := letDecls.push letDecl
  return letDecls

def mkAuxFunction (ctx : Deriving.Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal     := ctx.typeInfos[i]!
  let header     ← mkToExprHeader indVal
  let mut body   ← mkToExprBody header indVal auxFunName
  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx header.argNames
    body ← mkLet letDecls body
  let binders    := header.binders
  if ctx.usePartial then
    `(private partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Expr :=
        $body:term)
  else
    `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Expr :=
        $body:term)

def mkMutualBlock (ctx : Deriving.Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual $auxDefs:command* end)

open TSyntax.Compat in
def mkInstanceCmds (ctx : Deriving.Context) (typeNames : Array Name) : TermElabM (Array Command) := do
  let mut instances := #[]
  for i in [:ctx.typeInfos.size] do
    let indVal       := ctx.typeInfos[i]!
    if typeNames.contains indVal.name then
      let auxFunName   := ctx.auxFunNames[i]!
      let argNames     ← mkInductArgNames indVal
      let binders      ← mkImplicitBinders argNames
      let binders      := binders ++ (← mkInstImplicitBinders ``ToExpr indVal argNames)
      let indType      ← mkInductiveApp indVal argNames
      let toTypeExpr   ← mkToTypeExpr argNames indVal
      let instCmd ← `(instance $binders:implicitBinder* : ToExpr $indType where
                        toExpr := $(mkIdent auxFunName)
                        toTypeExpr := $toTypeExpr)
      instances := instances.push instCmd
  return instances

def mkToExprInstanceCmds (declNames : Array Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext "toExpr" declNames[0]!
  let cmds := #[← mkMutualBlock ctx]
     ++ (← mkInstanceCmds ctx declNames)
  trace[Elab.Deriving.toExpr] "\n{cmds}"
  return cmds

#check ToExpr

def mkToExprInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    let cmds ← liftTermElabM <| mkToExprInstanceCmds declNames
    cmds.forM elabCommand
    return true
  else
    return false

initialize
  registerDerivingHandler `Lean.ToExpr mkToExprInstanceHandler
  registerTraceClass `Elab.Deriving.toExpr

end Mathlib.Deriving.ToExpr
