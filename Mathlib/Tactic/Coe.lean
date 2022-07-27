/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean

open Lean Elab Term Meta

/-!
Define a `(↑)` notation for coercions equivalent to the eta-reduction of `(↑ ·)`.
-/

namespace Lean.Elab.Term.CoeImpl

elab "(" "↑" ")" : term <= expectedType => do
  let expectedType ← instantiateMVars expectedType
  let Expr.forallE _ a b .. := expectedType | do
    tryPostpone
    throwError "(↑) must have a function type, not{indentExpr expectedType}"
  if b.hasLooseBVars then
    tryPostpone
    throwError "(↑) must have a non-dependent function type, not{indentExpr expectedType}"
  if a.hasExprMVar then tryPostpone
  if b.hasExprMVar then tryPostpone
  let f ← withLocalDeclD `x a fun x => do
    mkLambdaFVars #[x] (← mkCoe b a x)
  return f.etaExpanded?.getD f
