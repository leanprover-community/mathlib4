/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean
import Lean.Elab.Command
import Lean.Linter.Util

/-!
The "deprecateNoSince" linter emits a warning when there is a `deprecated`
without `(since := "YYYY-MM-DD")`.
-/
open Lean Elab Command

namespace Mathlib.Linter

/-- The "deprecateNoSince" linter emits a warning when there is a `deprecated`
without `(since := "YYYY-MM-DD")`. -/
register_option linter.deprecateNoSince : Bool := {
  defValue := true
  descr := "enable the deprecateNoSince linter"
}

namespace deprecateNoSince

/-- Gets the value of the `linter.deprecateNoSince` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.deprecateNoSince o

@[inherit_doc Mathlib.Linter.linter.deprecateNoSince]
def deprecateNoSinceLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    let depr := (stx.find? (·.isOfKind ``Lean.deprecated)).getD default
    match depr.getArgs with
      | #[a, b, c, .node _ `null #[]] =>
        let args := #[c, b, a].filter (·.isOfKind `null)
        let lastArg := (args.map (·.getArgs)).flatten.getD 0 depr
        let dt ← IO.Process.run {cmd := "date", args := #["-I"]}
        let fm ← getFileMap
        let pos := fm.toPosition (lastArg.getRange?.getD default).stop
        Linter.logLint linter.deprecateNoSince lastArg m!"\
          After here, please add (since := \"{dt.trimRight}\") or whatever date is appropriate \
          `{pos}`";
      | _ => return

initialize addLinter deprecateNoSinceLinter
