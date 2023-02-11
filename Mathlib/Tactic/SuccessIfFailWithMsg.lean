/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Sébastien Gouëzel, Scott Morrison, Thomas Murrills
-/
import Lean

/-!
# Success If Fail With Message

This file implements a tactic that succeeds only if its argument fails with a specified message.

It's mostly useful in tests, where we want to make sure that tactics fail in certain ways under
circumstances.
-/

open Lean Elab Meta Tactic Syntax

namespace Mathlib.Tactic

/-- `success_if_fail_with_msg msg tacs` runs `tacs` and succeeds only if they fail with the message
`msg`.

`msg` can be any term that evaluates to an explicit `String`. -/
syntax (name := successIfFailWithMsg) "success_if_fail_with_msg " term:max tacticSeq : tactic

/- Note that we don't use the following in our definition of `success_if_fail_with_msg`, because we
want to check for definitional equality to the Expr specified by the syntax `$msg:term` there
instead. We also can provide more descriptive error messages in the elaboration case. -/

/-- Evaluates `tacs` and succeeds only if `tacs` both fails and throws an error equal (as a string)
to `msg`. -/
def successIfFailWithMessage (msg : String) (tacs : TacticM Unit) : TacticM Unit :=
  Term.withoutErrToSorry <| withoutRecover do
    let err ← try tacs; pure none
      catch err => pure (some (← err.toMessageData.toString))
    if let some err := err then
      unless msg == err do
        throwError "tactic failed, but got different error message:\n\n{err}"
    else
      throwError "tactic succeeded"

elab_rules : tactic
| `(tactic| success_if_fail_with_msg $msg:term $tacs:tacticSeq) =>
  Term.withoutErrToSorry <| withoutRecover do
    let err ← try evalTactic tacs; pure none
      catch err => pure (some (← err.toMessageData.toString))
    if let some err := err then
      if let some msg := isStrLit? msg then
        unless msg == err do
          throwError "tactic '{tacs}' failed, but got different error message:\n\n{err}"
      else
        let msg ← elabTermEnsuringType msg (Expr.const ``String [])
        unless ← withNewMCtxDepth <| withTransparency .all <| isDefEq msg (mkStrLit err) do
          throwError "tactic '{tacs}' failed, but got different error message:\n\n{err}"
    else
      throwError "tactic succeeded"
