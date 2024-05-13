/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lean.Elab.Command
import Lean.Linter.Util

/-!
## The `ge_or_gt` linter

A linter for checking whether a declaration contains `≥` or `>`.

TODO currently only in the conclusion? xxx compare with mathlib3!
-/

open Lean Elab Command

namespace Mathlib.Linter.ge_or_gt

def contains_illegal_ge_gt : Syntax → Bool
  -- TODO: fill in!
  | _stx => true

/-- The `ge_or_gt` linter emits a warning if a declaration contains `≥` or `>`
  in illegal places. -/
register_option linter.geOrGt : Bool := {
  defValue := true
  descr := "enable the `ge_or_gt` linter"
}

-- xxx: should this be moved to a different place?
/-- Gets the value of the `linter.geOrGt` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.geOrGt o

/-- docstring here -/
def getOrGtLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    -- content here
    match contains_illegal_ge_gt stx with
      | false => return
      | true => return
    -- | none => return
    -- | some (thm, _id) =>
    -- Linter.logLint linter.geOrGt thm m!"'theorem' requires a doc-string. \
    --                                           Either add one to '{id}' or use 'lemma' instead."
    --   logInfoAt thm ""

initialize addLinter getOrGtLinter

end Mathlib.Linter.ge_or_gt
