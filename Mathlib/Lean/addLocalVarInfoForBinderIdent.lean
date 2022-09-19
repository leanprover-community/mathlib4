/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import Mathlib.Lean.SourceInfo

namespace Lean

namespace Expr

open Lean.Elab.Term

/-- A hack to work around the linter complaining that a variable named `_` is unused. -/
def addLocalVarInfoForBinderIdent (fvar : Expr) : TSyntax ``binderIdent → TermElabM Unit
| `(binderIdent| $n:ident) =>
  Elab.Term.addLocalVarInfo n fvar
| tk => do
  let stx := mkNode ``Parser.Term.hole #[Syntax.atom (SourceInfo.fromRef' tk false) "_"] -- HACK
  Elab.Term.addLocalVarInfo stx fvar
