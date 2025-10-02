/-
Copyright (c) 2025 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Lean.Expr.Basic

/-! ## The `@[alias_in]` attribute -/

/-- Adds an alias of this declaration in a different namespace.
Example:
```
@[alias_in Foo.Bar] def A.B.C.d := ...
```
behaves like
```
alias Foo.Bar.C.d := A.B.C.d
```
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
      let tgtName := .fromComponents <| newNamespace ++ src.components.drop num
      let tgtId := mkIdent tgtName
      liftCommandElabM <| elabCommand <| ← `(command| alias $tgtId := $srcId)
      -- add mouse-over text
      pushInfoLeaf <| .ofTermInfo {
        elaborator := .anonymous, lctx := {}, expectedType? := none, isBinder := true,
        stx := nm, expr := ← mkConstWithLevelParams tgtName }
    | _, _, _ => throwUnsupportedSyntax }
