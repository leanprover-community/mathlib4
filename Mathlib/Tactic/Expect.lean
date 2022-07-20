/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Lean

namespace Mathlib.Tactic

open Lean Meta Elab Tactic

/-- `expect_failure tacs` succeeds iff `tacs` fails. -/
elab "expect_failure " tacs:tacticSeq : tactic => do
  if ← try withoutRecover (evalTactic tacs); pure true catch _ => pure false then
    throwErrorAt tacs "tactic succeeded"

/-- `expect_failure_msg msg tacs` succeeds iff `tacs` fails with `msg` as the error message. -/
elab "expect_failure_msg " msg:str tacs:tacticSeq : tactic => do
  match ← try withoutRecover (evalTactic tacs); pure none catch e => pure (some e) with
  | none => throwErrorAt tacs "tactic succeeded"
  | some e =>
    let expectedMsg := msg.getString
    let eMsg ← e.toMessageData.toString
    if eMsg != expectedMsg then
      throwErrorAt msg "expected failure message \"{expectedMsg}\" but got \"{eMsg}\""

/-- `expect_goals t₁, t₂, ⋯` succeeds iff the list of goals start with types `t₁`, `t₂` ... -/
elab "expect_goals " types:(colGt term),+ : tactic => do
  let typesList := types.getElems.data
  let goalsList ← getUnsolvedGoals
  if typesList.length > goalsList.length then
    throwError "too many expected goals"
  typesList.zip goalsList |>.forM fun (type, mvarId) => do
    let goalType ← instantiateMVars (← getMVarDecl mvarId).type
    let expectedType ← elabTerm type none
    if goalType != expectedType then
      throwErrorAt type s!"expected '{expectedType}' but got '{goalType}'"

syntax hypRule := ident " : " term

/-- `expect_hyps h₁ : t₁, h₂ : t₂, ⋯` succeeds iff every `hᵢ` in the context has type `tᵢ`. -/
elab "expect_hyps " rules:(hypRule),+ : tactic => withMainContext do
  rules.getElems.forM fun rule => do
    let `(hypRule| $hyp:ident : $type:term) := rule | unreachable!
    match (← getLCtx).findFromUserName? hyp.getId with
      | some decl => do
        let goalType ← instantiateMVars decl.type
        let expectedType ← elabTerm type none
        if goalType != expectedType then
        throwErrorAt type s!"expected '{expectedType}' but got '{goalType}'"
      | none => throwErrorAt hyp "unknown identifier '{hyp}'"
