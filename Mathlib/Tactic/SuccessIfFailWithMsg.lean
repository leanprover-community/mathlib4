/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Sébastien Gouëzel, Kim Morrison, Thomas Murrills
-/
import Lean.Elab.Eval
import Lean.Elab.Tactic.BuiltinTactic
import Mathlib.Init
import Lean.Meta.Tactic.TryThis

/-!
# Success If Fail With Message

This file implements a tactic that succeeds only if its argument fails with a specified message.

It's mostly useful in tests, where we want to make sure that tactics fail in certain ways under
circumstances.
-/

open Lean Meta Elab Tactic

namespace Mathlib.Tactic

/-- `success_if_fail_with_msg msg tacs` runs `tacs` and succeeds only if they fail with the message
`msg`.

`msg` can be any term that evaluates to an explicit `String`. -/
syntax (name := successIfFailWithMsg) "success_if_fail_with_msg " term:max tacticSeq : tactic

/-- Evaluates `tacs` and succeeds only if `tacs` both fails and throws an error equal (as a string)
to `msg`. -/
def successIfFailWithMessage {s α : Type} {m : Type → Type} [Monad m] [MonadLiftT BaseIO m]
    [MonadLiftT MetaM m] [MonadBacktrack s m] [MonadError m] (msg : String) (tacs : m α)
    (msgref : Option Syntax := none) (ref : Option Syntax := none) : m Unit := do
  let s ← saveState
  let err ←
    try _ ← tacs; pure none
    catch err => pure (some (← err.toMessageData.toString))
  restoreState s
  if let some err := err then
    unless msg.trim == err.trim do
      if let .some msgref := msgref then
        let suggestion : TryThis.Suggestion :=
          { suggestion := s!"\"{err.trim}\""
            toCodeActionTitle? := .some (fun _ => "Update with tactic error message")}
        TryThis.addSuggestion msgref suggestion (header := "Update with tactic error message: ")

      if let some ref := ref then
        throwErrorAt ref "tactic '{ref}' failed, but got different error message:\n\n{err}"
      else
        throwError "tactic failed, but got different error message:\n\n{err}"
  else
    if let some ref := ref then
      throwErrorAt ref "tactic '{ref}' succeeded, but was expected to fail"
    else
      throwError "tactic succeeded, but was expected to fail"

elab_rules : tactic
| `(tactic| success_if_fail_with_msg $msg:term $tacs:tacticSeq) =>
  Term.withoutErrToSorry <| withoutRecover do
    let msg' ← unsafe Term.evalTerm String (.const ``String []) msg
    successIfFailWithMessage msg' (evalTacticSeq tacs) msg tacs

end Mathlib.Tactic
