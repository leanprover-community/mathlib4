/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import Lean

open Lean Meta Elab Term Parser.Term

/-
This adds support for structure instance spread syntax.

```lean
instance : Foo α where
  __ := instSomething -- include fields from `instSomething`

example : Foo α := {
  __ := instSomething -- include fields from `instSomething`
}
```
-/
namespace Lean.Term.Elab

@[termElab structInst]
def elabSpread : TermElab
  | `({ $[$src? with]? $[$fields $[,]?]* $[: $ty?]? }), expectedType => do
    let mut spreads := #[]
    let mut newFieldNames : Std.HashSet Name := {}
    let mut newFields : Array Syntax := {}

    for field in fields do
      match field with
        | `(structInstField| $name:ident := $arg) =>
          if name.getId.eraseMacroScopes == `__ then do
            spreads := spreads.push <|<- withRef arg do withFreshMacroScope do
              let arg ← elabTerm arg none
              let argType ← whnf (← inferType arg)
              let argTypeC ← getStructureName argType
              let stxMVar ← `(?spread)
              assignExprMVar (← elabTerm stxMVar argType).mvarId! arg
              (argTypeC, field, stxMVar)
          else
            newFields := newFields.push field
            newFieldNames := newFieldNames.insert name.getId.eraseMacroScopes
        | `(structInstFieldAbbrev| $name:ident) =>
          newFields := newFields.push field
          newFieldNames := newFieldNames.insert name.getId.eraseMacroScopes
        | _ =>
          throwUnsupportedSyntax

    if spreads.isEmpty then throwUnsupportedSyntax

    if expectedType.isNone then
      throwError "expected type required for `__ := ...` syntax"

    let expectedStructName ← getStructureName expectedType.get!
    let expectedFields ← getStructureFieldsFlattened (← getEnv) expectedStructName
      (includeSubobjectFields := false)

    for (spreadType, spreadField, spread) in spreads do
      let mut used := false
      for field in ← getStructureFieldsFlattened (← getEnv) spreadType
                        (includeSubobjectFields := false) do
        if newFieldNames.contains field then continue
        if !expectedFields.contains field then continue
        newFieldNames := newFieldNames.insert field
        newFields := newFields.push <|<-
          `(structInstField| $(mkCIdent field):ident := ($spread).$(mkCIdent field):ident)
        used := true
      if !used then withRef spreadField do throwError "no fields used from spread"

    let stx' ← `({ $[$src? with]? $[$newFields]* $[: $ty?]? })
    elabTerm stx' expectedType

  | _, _ => throwUnsupportedSyntax

  where
    getStructureName (ty : Expr) : TermElabM Name := do
      if ty.getAppFn.isConst then
        let tyC ← ty.getAppFn.constName!
        if isStructureLike (← getEnv) tyC then
          return tyC
      throwError "expected structure type, but got{indentExpr ty}"
