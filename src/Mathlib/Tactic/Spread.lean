/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import Lean

open Lean Parser.Term Macro

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

macro_rules
| `({ $[$srcs,* with]? $[$fields $[,]?]* $[: $ty?]? }) => do
    let mut spreads := #[]
    let mut newFields := #[]

    for field in fields do
      match field with
        | `(structInstField| $name:ident := $arg) =>
          if name.getId.eraseMacroScopes == `__ then do
            spreads := spreads.push arg
          else
            newFields := newFields.push field
        | `(structInstFieldAbbrev| $name:ident) =>
          newFields := newFields.push field
        | _ =>
          throwUnsupported

    if spreads.isEmpty then throwUnsupported

    let srcs := (srcs.map (·.1)).getD #[] ++ spreads
    `({ $srcs,* with $[$newFields,]* $[: $ty?]? })
