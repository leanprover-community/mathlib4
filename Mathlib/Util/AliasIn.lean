/-
Copyright (c) 2025 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public meta import Mathlib.Lean.Expr.Basic

/-! ## The `@[alias_in]` attribute -/

public meta section

/-- Adds an alias of this declaration in a different namespace.
Example:
```
@[alias_in Foo.Bar] def A.B.C.d := ...
```
behaves like
```
alias A.Foo.Bar.d := A.B.C.d
```
We replace the rightmost/innermost namespaces, but always leave the final part of the name intact.
By default, `alias_in` assumes that we want to replace the same number of namespaces from the
original name as given in the new namespace. You can override this by adding a number at the end
```
@[alias_in Foo.Bar 3] def A.B.C.d := ...
```
behaves like
```
alias Foo.Bar.d := A.B.C.d
```
-/
syntax (name := aliasIn) "alias_in" ppSpace ident (ppSpace num)? : attr

open Lean Meta Elab Command
@[inherit_doc aliasIn]
initialize registerBuiltinAttribute {
    name := `aliasIn
    descr := "create alias in another namespace"
    applicationTime := .afterCompilation
    add := fun
    | src, stx@`(attr| alias_in%$tk $nm $[$num]?), _ => do
      let newNamespace := nm.getId.components
      let num := num.map (·.1.isNatLit?.get!) |>.getD newNamespace.length
      let srcId := mkIdent src
      let components := src.components
      if components.length ≤ num then
        throwError m!"{src} has only {components.length - 1} namespaces, cannot remove {num}. \n\
        Use `@[alias_in {nm} {components.length - 1}]` instead."
      let tgtName := .fromComponents <|
        components.take (components.length - 1 - num) ++ newNamespace ++ [components.getLast!]
      let tgtId := mkIdent tgtName
      liftCommandElabM <| elabCommand <| ← `(command| alias $tgtId := $srcId)
      -- add mouse-over text
      pushInfoLeaf <| .ofTermInfo {
        elaborator := .anonymous, lctx := {}, expectedType? := none, isBinder := true,
        stx := nm, expr := ← mkConstWithLevelParams tgtName }
    | _, _, _ => throwUnsupportedSyntax }
