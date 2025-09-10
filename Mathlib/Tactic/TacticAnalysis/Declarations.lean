/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Tactic.TacticAnalysis
import Mathlib.Tactic.ExtractGoal
import Mathlib.Tactic.MinImports
import Lean.Elab.Tactic.Meta

/-!
# Tactic linters

This file defines passes to run from the tactic analysis framework.
-/

open Lean Mathlib

/--
Define a pass that tries replacing a specific tactic with `grind`.

`tacticKind` is the `SyntaxNodeKind` for the tactic's main parser,
for example `Mathlib.Tactic.linarith`.
-/
def grindReplacementWith (tacticKind : SyntaxNodeKind)
    (reportFailure : Bool := true) (reportSuccess : Bool := false)
    (reportSlowdown : Bool := false) (maxSlowdown : Float := 1) :
    TacticAnalysis.Config := .ofComplex {
  out := List MVarId × MessageData
  ctx := Syntax
  trigger _ stx := if stx.getKind == tacticKind
    then .accept stx else .skip
  test stx goal := do
    let tac ← `(tactic| grind)
    try
      let (goals, _) ← Lean.Elab.runTactic goal tac
      return (goals, m!"")
    catch _e => -- Grind throws an error if it fails.
      let name ← mkAuxDeclName `extracted
      let ((sig, _, modules), _) ← (Mathlib.Tactic.ExtractGoal.goalSignature name goal).run
      let imports := modules.toList.map (s!"import {·}")
      return ([goal], m!"{"\n".intercalate imports}\n\ntheorem {sig} := by\n  fail_if_success grind\n  {stx}")
  tell stx _ oldHeartbeats new newHeartbeats :=
    if let (_ :: _, counterexample ) := new then
      if reportFailure then
        some m!"'grind' failed where '{stx}' succeeded. Counterexample:\n{counterexample}"
      else
        none
    else
      if reportSlowdown ∧ maxSlowdown * oldHeartbeats.toFloat < newHeartbeats.toFloat then
        some m!"'grind' is slower than '{stx}': {newHeartbeats / 1000} versus {oldHeartbeats / 1000} heartbeats"
      else if reportSuccess then
        some m!"'grind' can replace '{stx}'"
      else
        none
    }

/-- Debug `grind` by identifying places where it does not yet supersede `linarith`. -/
register_option linter.tacticAnalysis.linarithToGrind : Bool := {
  defValue := false
}
@[tacticAnalysis linter.tacticAnalysis.linarithToGrind,
  inherit_doc linter.tacticAnalysis.linarithToGrind]
def linarithToGrind := grindReplacementWith `Mathlib.Tactic.linarith

/-- Debug `grind` by identifying places where it does not yet supersede `omega`. -/
register_option linter.tacticAnalysis.omegaToGrind : Bool := {
  defValue := false
}
@[tacticAnalysis linter.tacticAnalysis.omegaToGrind,
  inherit_doc linter.tacticAnalysis.omegaToGrind]
def omegaToGrind := grindReplacementWith ``Lean.Parser.Tactic.omega

/-- Debug `grind` by identifying places where it does not yet supersede `ring`. -/
register_option linter.tacticAnalysis.ringToGrind : Bool := {
  defValue := false
}
@[tacticAnalysis linter.tacticAnalysis.ringToGrind,
  inherit_doc linter.tacticAnalysis.ringToGrind]
def ringToGrind := grindReplacementWith `Mathlib.Tactic.RingNF.ring

/-- Suggest merging two adjacent `rw` tactics if that also solves the goal. -/
register_option linter.tacticAnalysis.rwMerge : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.rwMerge, inherit_doc linter.tacticAnalysis.rwMerge]
def rwMerge : TacticAnalysis.Config := .ofComplex {
  out := (List MVarId × Array Syntax)
  ctx := (Array (Array Syntax))
  trigger ctx stx :=
    match stx with
    | `(tactic| rw [$args,*]) => .continue ((ctx.getD #[]).push args)
    | _ => if let some args := ctx then if args.size > 1 then .accept args else .skip else .skip
  test ctx goal := withOptions (fun opts => opts.set `grind.warning false) do
    let ctxT : Array (TSyntax `Lean.Parser.Tactic.rwRule) := ctx.flatten.map (⟨·⟩)
    let tac ← `(tactic| rw [$ctxT,*])
    try
      let (goals, _) ← Lean.Elab.runTactic goal tac
      return (goals, ctxT.map (↑·))
    catch _e => -- rw throws an error if it fails to pattern-match.
      return ([goal], ctxT.map (↑·))
  tell _stx _old _oldHeartbeats new _newHeartbeats :=
    if new.1.isEmpty then
      m!"Try this: rw {new.2}"
    else none }

/-- Suggest merging `tac; grind` into just `grind` if that also solves the goal. -/
register_option linter.tacticAnalysis.mergeWithGrind : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.mergeWithGrind,
  inherit_doc linter.tacticAnalysis.mergeWithGrind]
def mergeWithGrind : TacticAnalysis.Config where
  run seq := do
    if let #[(preCtx, preI), (_postCtx, postI)] := seq[0:2].array then
      if postI.stx.getKind == ``Lean.Parser.Tactic.grind then
        if let [goal] := preI.goalsBefore then
          preCtx.runTactic preI goal <| fun goal => do
            let tac := postI.stx
            let (goals, _) ← try
                Lean.Elab.runTactic goal tac
              catch _e =>
                pure ([goal], {})
            if goals.isEmpty then
              logWarningAt preI.stx m!"'{preI.stx}; grind' can be replaced with 'grind'"

/-- Suggest replacing a sequence of tactics with `grind` if that also solves the goal. -/
register_option linter.tacticAnalysis.terminalToGrind : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.terminalToGrind,
  inherit_doc linter.tacticAnalysis.terminalToGrind]
def terminalToGrind : TacticAnalysis.Config where
  run seq := do
    let threshold := 3
    -- `replaced` will hold the terminal tactic sequence that can be replaced with `grind`.
    -- We prepend each tactic in turn, starting with the last.
    let mut replaced : List (TSyntax `tactic) := []
    let mut success := false
    let mut oldHeartbeats := 0
    let mut newHeartbeats := 0
    -- We iterate through the tactic sequence in reverse, checking at each tactic if the goal is
    -- already solved by `grind` and if so pushing that tactic onto `replaced`.
    -- By repeating this until `grind` fails for the first time, we get a terminal sequence
    -- of replaceable tactics.
    for (ctx, i) in seq.reverse do
      if replaced.length >= threshold - 1 && i.stx.getKind != ``Lean.Parser.Tactic.grind then
        if let [goal] := i.goalsBefore then
          -- Count the heartbeats of the original tactic sequence, verifying that this indeed
          -- closes the goal like it does in userspace.
          let suffix := ⟨i.stx⟩ :: replaced
          let seq ← `(tactic| $suffix.toArray;*)
          let (oldGoals, heartbeats) ← withHeartbeats <| ctx.runTactic i goal <| fun goal => do
            let (goals, _) ←
              try
                Lean.Elab.runTactic goal seq
              catch _e =>
                pure ([goal], {})
            return goals
          if !oldGoals.isEmpty then
            logWarningAt i.stx m!"Original tactics failed to solve the goal: {seq}"
          oldHeartbeats := heartbeats

          -- To check if `grind` can close the goal, run `grind` on the current goal
          -- and verify that no goals remain afterwards.
          let (newGoals, heartbeats) ← withHeartbeats <| ctx.runTactic i goal <| fun goal => do
            let tac ← `(tactic| grind)
            let (goals, _) ←
              try
                Lean.Elab.runTactic goal tac
              catch _e =>
                pure ([goal], {})
            return goals
          newHeartbeats := heartbeats
          if newGoals.isEmpty then
            success := true
          else
            break
        else
          break
      replaced := ⟨i.stx⟩ :: replaced

    if h : replaced.length >= threshold ∧ success then
      let stx := replaced[0]
      let seq ← `(tactic| $replaced.toArray;*)
      logWarningAt stx m!"replace the proof with 'grind': {seq}"
      if oldHeartbeats * 2 < newHeartbeats then
        logWarningAt stx m!"'grind' is slower than the original: {oldHeartbeats} -> {newHeartbeats}"
