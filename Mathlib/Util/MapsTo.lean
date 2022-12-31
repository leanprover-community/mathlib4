/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean
import Std.Tactic.OpenPrivate
import Std.Tactic.Lint

/-!
# `fun x ↦ 42` syntax for functions
-/

namespace Mathlib.Util.MapsTo

open Lean Parser Term
open PrettyPrinter Delaborator SubExpr

/-- `fun x ↦ t` is the function mapping `x` to `t`  -/
syntax:max "fun " ppGroup(many1(ppSpace funBinder) optType " ↦") ppSpace term : term
macro_rules
  | `(fun $[$binders:funBinder]* $[: $ty]? ↦ $body) =>
    `(fun $[$binders:funBinder]* $[: $ty]? => $body)

open private delabBinders from Lean.PrettyPrinter.Delaborator.Builtins

open TSyntax.Compat in
/-- Delaborator for lambdas producing the mathlib `fun x ↦ t` syntax. -/
-- Copied from the core function with the same name..
-- TODO: Temporarily disabled, since it conflicts with pretty-printing of Exists.
-- @[delab lam]
def delabLam : Delab :=
  delabBinders fun curNames stxBody ↦ do
    let e ← getExpr
    let stxT ← withBindingDomain delab
    let ppTypes ← getPPOption getPPFunBinderTypes
    let usedDownstream := curNames.any (fun n ↦ hasIdent n.getId stxBody)
    let defaultCase (_ : Unit) : Delab := do
      if ppTypes then
        let stxCurNames ←
          if curNames.size > 1 then
            `($(curNames.get! 0) $(curNames.eraseIdx 0)*)
          else
            pure $ curNames.get! 0;
        `(funBinder| ($stxCurNames : $stxT))
      else
        pure curNames.back  -- here `curNames.size == 1`
    let group ← match e.binderInfo, ppTypes with
      | BinderInfo.default,        _      => defaultCase ()
      | BinderInfo.implicit,       true   => `(funBinder| {$curNames* : $stxT})
      | BinderInfo.implicit,       false  => `(funBinder| {$curNames*})
      | BinderInfo.strictImplicit, true   => `(funBinder| ⦃$curNames* : $stxT⦄)
      | BinderInfo.strictImplicit, false  => `(funBinder| ⦃$curNames*⦄)
      | BinderInfo.instImplicit,   _     =>
        if usedDownstream then `(funBinder| [$curNames.back : $stxT])  -- here `curNames.size == 1`
        else  `(funBinder| [$stxT])
    match stxBody with
    | `(fun $[$binderGroups:funBinder]* ↦ $stxBody) => `(fun $group $[$binderGroups]* ↦ $stxBody)
    | _                                 => `(fun $group ↦ $stxBody)
