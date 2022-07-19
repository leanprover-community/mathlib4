/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Lean

namespace Mathlib.Tactic

open Lean Meta Elab Tactic

/-- `expect_failure tacs` succeeds iff `tacs` fails. -/
elab "expect_failure " tacs:tacticSeq : tactic => withMainContext do
  if ← try withoutRecover (evalTactic tacs); pure true catch _ => pure false then
    throwErrorAt tacs "tactic succeeded"

/-- `expect_failure_msg msg tacs` succeeds iff `tacs` fails with `msg` as the error message. -/
elab "expect_failure_msg " msg:str tacs:tacticSeq : tactic => withMainContext do
  match ← try withoutRecover (evalTactic tacs); pure none catch e => pure (some e) with
  | none => throwErrorAt tacs "tactic succeeded"
  | some e =>
    let expectedMsg := msg.getString
    let eMsg ← e.toMessageData.toString
    if eMsg != expectedMsg then
      throwErrorAt msg "expected failure message \"{expectedMsg}\" but got \"{eMsg}\""

/-- `expect_goal t` succeeds iff the main goal is the type `t`. -/
elab "expect_goal " type:term : tactic => withMainContext do
  let expectedType ← elabTerm type none
  let goalType ← getMainTarget
  if goalType != expectedType then
    throwErrorAt type s!"expected '{expectedType}' but got '{goalType}'"

/-- `expect_hyp h : t` succeeds iff there exists a `h` in the context whose type is `t`. -/
elab "expect_hyp " hyp:ident ":" type:term : tactic => withMainContext do
  match (← getLCtx).findFromUserName? hyp.getId with
    | some decl => do
      let goalType ← instantiateMVars decl.type
      let expectedType ← elabTerm type none
      if goalType != expectedType then
      throwErrorAt type s!"expected '{expectedType}' but got '{goalType}'"
    | none => throwErrorAt hyp "unknown identifier '{hyp}'"
