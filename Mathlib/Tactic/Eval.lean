/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import Qq.Macro

/-!
# The `eval%` term elaborator

This file provides the `eval% x` term elaborator, which evaluates the constant `x` at compile-time
in the interpreter, and interpolates it into the expression.
-/


open Qq Lean Elab Term

namespace Mathlib.Meta

/--
`eval% x` evaluates the term `x : X` in the interpreter, and then injects the resulting expression.

As an example:
```lean
example : 2^10 = eval% 2^10 := by
  -- goal is `2^10 = 1024`
  sorry
```
This only works if a `Lean.ToExpr X` instance is available.

Tip: you can use `show_term eval% x` to see the value of `eval% x`.
-/
syntax (name := eval_expr) "eval% " term : term

@[term_elab eval_expr, inherit_doc eval_expr]
unsafe def elabEvalExpr : Lean.Elab.Term.TermElab
| `(term| eval% $stx) => fun exp => do
  let e ← Lean.Elab.Term.elabTermAndSynthesize stx exp
  let e ← instantiateMVars e
  let ee ← Meta.mkAppM ``Lean.toExpr #[e]
  Lean.Meta.evalExpr Expr q(Expr) ee (safety := .unsafe)
| _ => fun _ => Elab.throwUnsupportedSyntax

end Mathlib.Meta
