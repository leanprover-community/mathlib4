/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn
-/
import Mathlib.Tactic.Core
import Mathlib.Lean.Expr

/-!
# Transport multiplicative to additive

This file defines an attribute `toAdditive` that can be used to
automatically transport theorems and definitions (but not inductive
types and structures) from a multiplicative theory to an additive theory.

Currently this is a no-op implementation.

-/

open Lean Meta Elab Command Expr

namespace ToAdditive

syntax (name := toAdditiveIgnoreArgs) "toAdditiveIgnoreArgs" num* : attr
syntax (name := toAdditiveRelevantArg) "toAdditiveRelevantArg" num : attr
syntax (name := toAdditiveReorder) "toAdditiveReorder" num* : attr
syntax (name := toAdditive) "toAdditive" (ppSpace ident)? (ppSpace str)? : attr
syntax (name := toAdditive!) "toAdditive!" (ppSpace ident)? (ppSpace str)? : attr
syntax (name := toAdditive?) "toAdditive?" (ppSpace ident)? (ppSpace str)? : attr
syntax (name := toAdditive!?) "toAdditive!?" (ppSpace ident)? (ppSpace str)? : attr

/--
`e.applyReplacementFun f test` applies `f` to each identifier
(inductive type, defined function etc) in an expression, unless
* The identifier occurs in an application with first argument `arg`; and
* `test arg` is false.
However, if `f` is in the dictionary `relevant`, then the argument `relevant.find f`
is tested, instead of the first argument.

Reorder contains the information about what arguments to reorder:
e.g. `g x₁ x₂ x₃ ... xₙ` becomes `g x₂ x₁ x₃ ... xₙ` if `reorder.find g = some [1]`.
We assume that all functions where we want to reorder arguments are fully applied.
This can be done by applying `expr.eta_expand` first.
-/
partial def applyReplacementFun (f : Name → Name) (test : Expr → Bool)
  (relevant : NameMap ℕ) (reorder : NameMap $ List ℕ) : Expr → Expr :=
replaceRec λ e =>
  match e with
    | const n ls _ => some (#[], λ es =>
      mkConst (f n) $
      -- if the first two arguments are reordered, we also reorder the first two universe parameters
      if ((reorder.find? n).getD []).contains 1 then (ls.get! 1)::ls.head!::ls.drop 2 else ls)
    | app g x _ =>
      let f := g.getAppFn
      let nm? := f.constName?
      match nm? with
      | none => none
      | some nm =>
        let nArgs := g.getAppNumArgs
        if ((reorder.find? nm).getD []).contains nArgs && ((g.getAppArgs.get? 0).map test).getD true then
        -- interchange the last two arguments of `g x`
        some (#[g.appFn!, x, g.appArg!], λ es => mkApp es[1] es[2])
        else if nArgs == (relevant.find? nm).getD 0 && f.isConst && !test x then
        -- do not modify `f`, but do modify the arguments of `f`
        some (g.getAppArgs.append #[x], λ es => mkAppN f es) else
        none
    | _ => none

end ToAdditive
