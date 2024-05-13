/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lean.Elab.Command
import Lean.Linter.Util

/-!
## The `ge_or_gt` linter

A linter for checking whether a declaration contains a `≥` or `>` in an illegal position:
`≤` or `<` should be used instead. This is bad because it makes rewrites apply in fewer contexts.

This check excludes, in particular, comments, a `≥` or `>` symbol in custom notation
and predicate binders like `∃ i ≥ 1`.
Unlike in mathlib3, this checks hypotheses, definitions and conclusions as well as proofs. -/

open Lean Elab Command

namespace Mathlib.Linter.ge_or_gt

/-- Whether a syntax element is a "greater" or "greater than" sign.
(This excludes, in particular, comments, a `≥` or `>` symbol as part of custom or local notation
 and predicate binders like `∃ i ≥ 1`.) -/
def is_ge_or_gt : Syntax → Bool
  | `($_ ≥ $_) => true
  | `($_ > $_) => true
  | _ => false

/-- The `ge_or_gt` linter emits a warning if a declaration contains `≥` or `>`
  in illegal places. -/
register_option linter.geOrGt : Bool := {
  defValue := true
  descr := "enable the `ge_or_gt` linter"
}

-- xxx: this feels like repetitive boilerplate; is there a way to abstract this?
/-- Gets the value of the `linter.geOrGt` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.geOrGt o

/-- docstring here -/
def getOrGtLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    match stx.findStack? (fun _ ↦ true) is_ge_or_gt with
    | some ((head, _n)::_chain) =>
      -- remaining case is "(· ≥ ·)" or for >...
      -- can I use Stack.matches?
      --if Stack.matches _chain [SyntaxNode.]
      -- XXX: exclude remaining case
        Linter.logLint linter.geOrGt head m!"'≥ or > is used in an illegal position\n\
        please change the statement to use ≤ or < instead"
    | _ => return

initialize addLinter getOrGtLinter

end Mathlib.Linter.ge_or_gt
