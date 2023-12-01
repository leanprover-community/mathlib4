/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean

/-! `beta%` term elaborator

The `beta% f x1 ... xn` term elaborator elaborates the expression
`f x1 ... xn` and then does one level of beta reduction.
That is, if `f` is a lambda then it will substitute its arguments.

The purpose of this is to support substitutions in notations such as
`∀ i, beta% p i` so that `p i` gets beta reduced when `p` is a lambda.
-/

namespace Mathlib.Util.TermBeta

open Lean Elab Term

/-- `beta% t` elaborates `t` and then if the result is in the form
`f x1 ... xn` where `f` is a (nested) lambda expression,
it will substitute all of its arguments by beta reduction.
This does not recursively do beta reduction, nor will it do
beta reduction of subexpressions.

In particular, `t` is elaborated, its metavariables are instantiated,
and then `Lean.Expr.headBeta` is applied. -/
syntax (name := betaStx) "beta% " term : term

@[term_elab betaStx, inherit_doc betaStx]
def elabBeta : TermElab := fun stx expectedType? =>
  match stx with
  | `(beta% $t) => do
    let e ← elabTerm t expectedType?
    return (← instantiateMVars e).headBeta
  | _ => throwUnsupportedSyntax
