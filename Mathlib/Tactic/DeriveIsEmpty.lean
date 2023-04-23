/-
Copyright (c) 2023 Tiancheng "Timothy" Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Gu
-/
import Lean
import Mathlib.Logic.IsEmpty

/-!
# A `IsEmpty` derive handler

This module defines an `IsEmpty` derive handler for inductive types. It supports mutually inductive
types as well.

For this handler to work, _every_ constructor must have at least one field whose type is:
 - The same type as that being constructed,
 - Another type in the same `mutual` block, or
 - A type that is already `IsEmpty`.

Note that we do not try to add hypotheses for inductive parameters.

A few examples of what this handler can do:
```
inductive Nomatch
  deriving IsEmpty

inductive SelfLoop
  | intro : Nat → SelfLoop → SelfLoop
  deriving IsEmpty

mutual
inductive MutualA
  | introA : MutualB → MutualA
inductive MutualB
  | introB : MutualA → MutualB
end
deriving instance IsEmpty for MutualA, MutualB
```

To get debugging information, run `set_option trace.Elab.Deriving.isEmpty true`.

Implementation note: this derive handler was originally modeled after the `Hashable` derive
handler.
-/

namespace Mathlib.Deriving.IsEmpty
open Lean Elab Command Meta

section no_inst
open TSyntax.Compat

/--
Same as `Lean.Elab.Deriving.mkInstanceCmds`, except it doesn't add instance binders by default.
-/
private def mkInstanceCmds (ctx : Deriving.Context) (className : Name) (typeNames : Array Name)
    (useAnonCtor := true) (addInstBinders := false) : TermElabM (Array Command) := do
  let mut instances := #[]
  for i in [:ctx.typeInfos.size] do
    let indVal       := ctx.typeInfos[i]!
    if typeNames.contains indVal.name then
      let auxFunName   := ctx.auxFunNames[i]!
      let argNames     ← Deriving.mkInductArgNames indVal
      let mut binders  ← Deriving.mkImplicitBinders argNames
      if addInstBinders then
        binders        := binders ++ (← Deriving.mkInstImplicitBinders className indVal argNames)
      let indType      ← Deriving.mkInductiveApp indVal argNames
      let type         ← `($(mkIdent className) $indType)
      let val          ← if useAnonCtor then
                           `(⟨$(mkIdent auxFunName)⟩)
                         else pure <| mkIdent auxFunName
      let instCmd      ← `(instance $binders:implicitBinder* : $type := $val)
      instances := instances.push instCmd
  return instances

/-- Same as `Lean.Elab.Deriving.mkHeader`, except it doesn't add instance binders by default. -/
private def mkHeader (className : Name) (arity : Nat) (indVal : InductiveVal)
    (addInstBinders := false) : TermElabM Deriving.Header := do
  let argNames      ← Deriving.mkInductArgNames indVal
  let mut binders   ← Deriving.mkImplicitBinders argNames
  let targetType    ← Deriving.mkInductiveApp indVal argNames
  let mut targetNames := #[]
  for _ in [:arity] do
    targetNames := targetNames.push (← mkFreshUserName `x)
  if addInstBinders then
    binders := binders ++ (← Deriving.mkInstImplicitBinders className indVal argNames)
  binders := binders ++ (← targetNames.mapM fun targetName =>
    `(Deriving.explicitBinderF| ($(mkIdent targetName) : $targetType)))
  return {
    binders     := binders
    argNames    := argNames
    targetNames := targetNames
    targetType  := targetType
  }
end no_inst

private def mkMatch (ctx : Deriving.Context) (header : Deriving.Header) (indVal : InductiveVal) :
    TermElabM Term := do
  let discrs ← Deriving.mkDiscrs header indVal
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)
where

  /-- Check if we can recursively call ourselves. -/
  mkAltUsingRec (ctorInfo : ConstructorVal) (xs : Array Expr) :
      TermElabM (Option (Term × Array Term)) := do
    let allIndVals := indVal.all.toArray
    let mut ctorArgs := #[]
    let mut rhs := none
    for i in [:ctorInfo.numFields] do
      if let some _ := rhs then
        ctorArgs := ctorArgs.push (← `(_))
      else
        let x := xs[indVal.numParams + i]!
        let xTy ← inferType x
        if let .const declName _ := (← whnf xTy).getAppFn then
          if let some x := allIndVals.findIdx? (· == declName) then
            let a := mkIdent (← mkFreshUserName `a)
            ctorArgs := ctorArgs.push a
            rhs ← `($(mkIdent ctx.auxFunNames[x]!) $a)
            trace[Elab.Deriving.isEmpty] "{ctorInfo.name}: Using recursive call for field {i}"
          else
            ctorArgs := ctorArgs.push (← `(_))
        else
          ctorArgs := ctorArgs.push (← `(_))
    return rhs.map (·, ctorArgs)

  /-- Check if one of the constructor's fields is already `IsEmpty`. -/
  mkAltUsingIsEmpty (ctorInfo : ConstructorVal) (xs : Array Expr) :
      TermElabM (Option (Term × Array Term)) := do
    let mut ctorArgs := #[]
    let mut out := none
    for i in [:ctorInfo.numFields] do
      if let some _ := out then
        ctorArgs := ctorArgs.push (← `(_))
      else
        let x := xs[indVal.numParams + i]!
        let xTy ← inferType x
        let instType ← mkAppM ``IsEmpty #[xTy]
        match ← trySynthInstance instType with
        | LOption.some _ =>
          trace[Elab.Deriving.isEmpty] "{ctorInfo.name}: Found instance {instType}"
          let a := mkIdent (← mkFreshUserName `a)
          ctorArgs := ctorArgs.push a
          out := some (← `(IsEmpty.false $a))
        | _ =>
          trace[Elab.Deriving.isEmpty] "{ctorInfo.name}: Could not find instance {instType}"
          ctorArgs := ctorArgs.push (← `(_))
    return out.map (·, ctorArgs)

  mkAlt (ctorName : Name) : TermElabM (TSyntax ``Parser.Term.matchAlt) := do
    let ctorInfo ← getConstInfoCtor ctorName
    forallTelescopeReducing ctorInfo.type fun xs _ => do
      match (← mkAltUsingRec ctorInfo xs) <|> (← mkAltUsingIsEmpty ctorInfo xs) with
      | some (rhs, ctorArgsFields) =>
        let mut patterns := #[]
        -- add `_` pattern for indices
        for _ in [:indVal.numIndices] do
          patterns := patterns.push (← `(_))
        let mut ctorArgs := #[]
        -- add `_` for inductive parameters; they are inaccessible
        for _ in [:indVal.numParams] do
          ctorArgs := ctorArgs.push (← `(_))
        -- add fields
        ctorArgs := ctorArgs ++ ctorArgsFields
        patterns := patterns.push (← `(@$(mkCIdent ctorName):ident $ctorArgs:term*))
        `(Parser.Term.matchAltExpr| | $[$patterns:term],* => $rhs:term)
      | none => throwError "Don't know how to derive IsEmpty for constructor {ctorName}"

  mkAlts : TermElabM (TSyntaxArray ``Parser.Term.matchAlt) := do
    let mut alts := #[]
    for ctorName in indVal.ctors do
      let alt ← mkAlt ctorName
      alts := alts.push alt
    return alts

private def mkFuncs (ctx : Deriving.Context) : TermElabM Command := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    let auxDef ← mkAuxFunction i
    auxDefs := auxDefs.push auxDef
  `(mutual $auxDefs:command* end)
where
  mkAuxFunction (i : Nat) : TermElabM Command := do
    let auxFunName    := ctx.auxFunNames[i]!
    let indVal        := ctx.typeInfos[i]!
    let header        ←  mkHeader ``IsEmpty 1 indVal
    let body          ←  mkMatch ctx header indVal
    let binders       := header.binders
    `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : False := $body:term)

private def mkIsEmptyInstanceCmds (declNames : Array Name) : TermElabM (Array Command) := do
  let ctx ← Deriving.mkContext "isEmpty" declNames[0]!
  let cmds := #[← mkFuncs ctx] ++ (← mkInstanceCmds ctx ``IsEmpty declNames)
  trace[Elab.Deriving.isEmpty] "\n{cmds}"
  return cmds

def mkIsEmptyHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    let cmds ← liftTermElabM <| mkIsEmptyInstanceCmds declNames
    cmds.forM elabCommand
    return true
  else
    return false

initialize
  registerDerivingHandler ``IsEmpty mkIsEmptyHandler
  registerTraceClass `Elab.Deriving.isEmpty

end Mathlib.Deriving.IsEmpty
