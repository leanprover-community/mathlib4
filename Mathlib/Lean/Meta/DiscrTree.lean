/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Meta.DiscrTree
import Std.Lean.Meta.DiscrTree
import Mathlib.Lean.Expr.Traverse

/-!
# Additions to `Lean.Meta.DiscrTree`
-/

set_option autoImplicit true

namespace Lean.Meta.DiscrTree

/--
Find keys which match the expression, or some subexpression.

Note that repeated subexpressions will be visited each time they appear,
making this operation potentially very expensive.
It would be good to solve this problem!

Implementation: we reverse the results from `getMatch`,
so that we return lemmas matching larger subexpressions first,
and amongst those we return more specific lemmas first.
-/
partial def getSubexpressionMatches (d : DiscrTree α) (e : Expr) (config : WhnfCoreConfig) :
    MetaM (Array α) := do
  match e with
  | .bvar _ => return #[]
  | .forallE _ _ _ _ => forallTelescope e (fun args body => do
      args.foldlM (fun acc arg => do
          pure <| acc ++ (← d.getSubexpressionMatches (← inferType arg) config))
        (← d.getSubexpressionMatches body config).reverse)
  | .lam _ _ _ _
  | .letE _ _ _ _ _ => lambdaLetTelescope e (fun args body => do
      args.foldlM (fun acc arg => do
          pure <| acc ++ (← d.getSubexpressionMatches (← inferType arg) config))
        (← d.getSubexpressionMatches body config).reverse)
  | _ =>
    e.foldlM (fun a f => do
      pure <| a ++ (← d.getSubexpressionMatches f config)) (← d.getMatch e config).reverse

end Lean.Meta.DiscrTree
