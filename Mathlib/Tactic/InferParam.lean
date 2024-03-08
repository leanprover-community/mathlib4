/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Mario Carneiro
-/
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Replace

/-!
# Infer an optional parameter

In this file we define a tactic `infer_param` that closes a goal with default value by using
this default value.
-/

namespace Mathlib.Tactic

open Lean Elab Tactic Meta

/-- Close a goal of the form `optParam α a` or `autoParam α stx` by using `a`. -/
elab (name := inferOptParam) "infer_param" : tactic => do
  let tgt ← getMainTarget
  if let some val := tgt.getOptParamDefault? then
    liftMetaTactic fun goal => do goal.assign val; pure []
  else if let some (.const tacticDecl ..) := tgt.getAutoParamTactic? then
    match evalSyntaxConstant (← getEnv) (← getOptions) tacticDecl with
    | .error err => throwError err
    | Except.ok tacticSyntax =>
      liftMetaTactic1 fun goal => do
        goal.replaceTargetDefEq (← goal.getType).consumeTypeAnnotations
      evalTactic tacticSyntax
  else throwError
    "`infer_param` only solves goals of the form `optParam _ _` or `autoParam _ _`, not {tgt}"
