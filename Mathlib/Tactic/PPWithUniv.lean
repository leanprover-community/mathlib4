/-
Copyright (c) 2023 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean

/-!
# Command to pretty-print universe level parameters by default

This module contains the `pp_with_univ` command, which enables pretty-printing
of universe parameters for the specified definition.  This is helpful for definitions like
`Ordinal`, where the universe levels are both relevant and not deducible from the arguments.
-/

namespace Mathlib.PPWithUniv

open Lean PrettyPrinter Delaborator SubExpr Elab Command

/--
Delaborator that prints the current application with universe parameters on the head symbol,
unless `pp.universes` is explicitly set to `false`.
-/
def delabWithUniv : Delab :=
  whenPPOption (·.get pp.universes.name true) <|
  let enablePPUnivOnHead subExpr :=
    let expr := subExpr.expr
    let expr := mkAppN (expr.getAppFn.setOption pp.universes.name true) expr.getAppArgs
    { subExpr with expr }
  withTheReader SubExpr enablePPUnivOnHead <|
    delabAppImplicit <|> delabAppExplicit

/--
`pp_with_univ Ordinal` instructs the pretty-printer to
print `Ordinal.{u}` with universe parameters by default
(unless `pp.universes` is explicitly set to `false`).
-/
elab "pp_with_univ " id:ident : command => do
  let id ← resolveGlobalConstNoOverloadWithInfo id
  elabCommand <| ← `(@[delab $(mkIdent <| `app ++ id)] def delab := delabWithUniv)
