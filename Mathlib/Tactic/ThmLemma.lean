/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
-- once the replacement is done, uncomment the next import and restore the `logLint` below
--import Lean.Linter.Util

/-!
#  The `theorem` vs `lemma` linter

The usage of `theorem` in `Mathlib` comes with the expectation that the result is "more important"
than a `lemma`.
This linter is a step in the direction of enforcing this expectation: if a `theorem`
does not have a doc-string, then the linter raises a warning.
-/

open Lean Elab Command

namespace Mathlib.ThmLemma

/-- `thmNoDoc cmd` checks whether the `cmd` is a `theorem` with no doc-string.
If that is the case, then it returns two syntax nodes: the one for `theorem` and the one
for the name of the theorem.
Otherwise, it returns none.
-/
def thmNoDoc : Syntax → Option (Syntax × Syntax)
  | .node _ ``Lean.Parser.Command.declaration #[
    -- the inner `#[]` detects the absence of a doc-string
    .node _ ``Lean.Parser.Command.declModifiers #[.node _ `null #[], _, _, _, _, _],
    .node _ ``Lean.Parser.Command.theorem #[
      thm@(.atom _ "theorem"),
      .node _ ``Lean.Parser.Command.declId #[id, _],
      _,
      _]
    ] => some (thm, id)
  | _ => none

/-- The `theorem` vs `lemma` linter emits a warning on a `theorem` without a doc-string. -/
register_option linter.ThmLemma : Bool := {
  defValue := true
  descr := "enable the `theorem` vs `lemma` linter"
}

/-- Gets the value of the `linter.ThmLemma` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.ThmLemma o

/-- The main implementation of the `theorem` vs `lemma` linter. -/
def thmLemmaLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    match thmNoDoc stx with
    | none => return
    | some (thm, _id) =>
      logInfoAt thm ""
--      Linter.logLint linter.ThmLemma thm m!"'theorem' requires a doc-string. \
--                                             Either add one to '{id}' or use 'lemma' instead."

initialize addLinter thmLemmaLinter
