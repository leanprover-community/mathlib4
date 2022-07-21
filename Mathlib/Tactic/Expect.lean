/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Lean

namespace Mathlib.Tactic

open Lean Meta Elab Tactic

/--
`expect_failure tacs` succeeds iff `tacs` fails.

`expect_failure` is similar to `success_if_failure` from core, except that `success_if_failure`
omits `withoutRecover`. When this is fixed, `expect_failure` can be deprecated or turned into a
macro.
-/
elab "expect_failure " tacs:tacticSeq : tactic => do
  if ← try withoutRecover (evalTactic tacs); pure true catch _ => pure false then
    throwErrorAt tacs "tactic sequence succeeded"

/-- `expect_failure_msg msg tacs` succeeds iff `tacs` fails with `msg` as the error message. -/
elab "expect_failure_msg " msg:str tacs:tacticSeq : tactic => do
  match ← try withoutRecover (evalTactic tacs); pure none catch e => pure (some e) with
  | none => throwErrorAt tacs "tactic sequence succeeded"
  | some e =>
    let expectedMsg := msg.getString
    let eMsg ← e.toMessageData.toString
    if eMsg != expectedMsg then
      throwErrorAt msg "expected failure message \"{expectedMsg}\" but got \"{eMsg}\""
