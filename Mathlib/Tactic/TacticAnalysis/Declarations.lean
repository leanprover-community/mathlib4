/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Edward van de Meent
-/
import Mathlib.Tactic.TacticAnalysis
import Mathlib.Tactic.ExtractGoal
import Mathlib.Tactic.MinImports
import Lean.Elab.Tactic.Meta
import Lean.Elab.Command

/-!
# Tactic linters

This file defines passes to run from the tactic analysis framework.
-/

open Lean Meta

namespace Mathlib.TacticAnalysis

/-- Helper structure for the return type of the `test` function in `terminalReplacement`. -/
private inductive TerminalReplacementOutcome where
| success (stx : TSyntax `tactic)
| remainingGoals (stx : TSyntax `tactic) (goals : List MessageData)
| error (stx : TSyntax `tactic) (msg : MessageData)

open Elab.Command

/--
Define a pass that tries replacing one terminal tactic with another.

`newTacticName` is a human-readable name for the tactic, for example "linarith".
This can be used to group messages together, so that `ring`, `ring_nf`, `ring1`, ...
all produce the same message.

`oldTacticKind` is the `SyntaxNodeKind` for the tactic's main parser,
for example `Mathlib.Tactic.linarith`.

`newTactic stx goal` selects the new tactic to try, which may depend on the old tactic invocation
in `stx` and the current `goal`.
-/
def terminalReplacement (oldTacticName newTacticName : String) (oldTacticKind : SyntaxNodeKind)
    (newTactic : Syntax → MVarId → MetaM (TSyntax `tactic))
    (reportFailure : Bool := true) (reportSuccess : Bool := false)
    (reportSlowdown : Bool := false) (maxSlowdown : Float := 1) :
    TacticAnalysis.Config := .ofComplex {
  out := TerminalReplacementOutcome
  ctx := Syntax
  trigger _ stx := if stx.getKind == oldTacticKind
    then .accept stx else .skip
  test stx goal := do
    let tac ← newTactic stx goal
    try
      let (goals, _) ← Lean.Elab.runTactic goal tac
      match goals with
      | [] => return .success tac
      | _ => do
        let goalsMessages ← goals.mapM fun g => do
          let e ← instantiateMVars (← g.getType)
          pure m!"⊢ {MessageData.ofExpr e}\n"
        return .remainingGoals tac goalsMessages
    catch _e =>
      let name ← mkAuxDeclName `extracted
      let ((sig, _, modules), _) ← (Mathlib.Tactic.ExtractGoal.goalSignature name goal).run
      let imports := modules.toList.map (s!"import {·}")
      return .error tac m!"{"\n".intercalate imports}\n\ntheorem {sig} := by\n  fail_if_success {tac}\n  {stx}"
  tell stx _ oldHeartbeats new newHeartbeats :=
    match new with
    | .error _ msg =>
      if reportFailure then
        let msg :=
          m!"`{newTacticName}` failed where `{oldTacticName}` succeeded.\n" ++
          m!"Original tactic:{indentD stx}\n" ++
          m!"Counterexample:{indentD msg}"
        return msg
      else
        return none
    | .remainingGoals newStx goals =>
      if reportFailure then
        let msg :=
          m!"`{newTacticName}` left unsolved goals where `{oldTacticName}` succeeded.\n" ++
          m!"Original tactic:{indentD stx}\n" ++
          m!"Replacement tactic:{indentD newStx}\n" ++
          m!"Unsolved goals:{indentD goals}"
        return msg
      else
        return none
    | .success newStx => do
      -- TODO: we should add a "Try this:" suggestion with code action.
      let msg := if (← liftCoreM <| PrettyPrinter.ppTactic newStx).pretty = newTacticName then
        m!"`{newTacticName}` can replace `{stx}`"
      else
        m!"`{newTacticName}` can replace `{stx}` using `{newStx}`"
      if reportSlowdown ∧ maxSlowdown * oldHeartbeats.toFloat < newHeartbeats.toFloat then
        return some m!"{msg}, but is slower: {newHeartbeats / 1000} versus {oldHeartbeats / 1000} heartbeats"
      else if reportSuccess then
        return some msg
      else
        return none
    }


/--
Define a pass that tries replacing a specific tactic with `grind`.

`tacticName` is a human-readable name for the tactic, for example "linarith".
This can be used to group messages together, so that `ring`, `ring_nf`, `ring1`, ...
all produce the same message.

`tacticKind` is the `SyntaxNodeKind` for the tactic's main parser,
for example `Mathlib.Tactic.linarith`.
-/
def grindReplacementWith (tacticName : String) (tacticKind : SyntaxNodeKind)
    (reportFailure : Bool := true) (reportSuccess : Bool := false)
    (reportSlowdown : Bool := false) (maxSlowdown : Float := 1) :
    TacticAnalysis.Config :=
  terminalReplacement tacticName "grind" tacticKind (fun _ _ => `(tactic| grind))
    reportFailure reportSuccess reportSlowdown maxSlowdown

end Mathlib.TacticAnalysis

open Mathlib TacticAnalysis

/-- Debug `grind` by identifying places where it does not yet supersede `linarith`. -/
register_option linter.tacticAnalysis.regressions.linarithToGrind : Bool := {
  defValue := false
}
@[tacticAnalysis linter.tacticAnalysis.regressions.linarithToGrind,
  inherit_doc linter.tacticAnalysis.regressions.linarithToGrind]
def linarithToGrindRegressions := grindReplacementWith "linarith" `Mathlib.Tactic.linarith

/-- Debug `grind` by identifying places where it does not yet supersede `ring`. -/
register_option linter.tacticAnalysis.regressions.ringToGrind : Bool := {
  defValue := false
}
@[tacticAnalysis linter.tacticAnalysis.regressions.ringToGrind,
  inherit_doc linter.tacticAnalysis.regressions.ringToGrind]
def ringToGrindRegressions := grindReplacementWith "ring" `Mathlib.Tactic.RingNF.ring

/-- Debug `cutsat` by identifying places where it does not yet supersede `omega`. -/
register_option linter.tacticAnalysis.regressions.omegaToCutsat : Bool := {
  defValue := false
}
@[tacticAnalysis linter.tacticAnalysis.regressions.omegaToCutsat,
  inherit_doc linter.tacticAnalysis.regressions.omegaToCutsat]
def omegaToCutsatRegressions :=
  terminalReplacement "omega" "cutsat" ``Lean.Parser.Tactic.omega (fun _ _ => `(tactic| cutsat))
    (reportSuccess := false) (reportFailure := true)

/-- Report places where `omega` can be replaced by `cutsat`. -/
register_option linter.tacticAnalysis.omegaToCutsat : Bool := {
  defValue := false
}
@[tacticAnalysis linter.tacticAnalysis.omegaToCutsat,
  inherit_doc linter.tacticAnalysis.omegaToCutsat]
def omegaToCutsat :=
  terminalReplacement "omega" "cutsat" ``Lean.Parser.Tactic.omega (fun _ _ => `(tactic| cutsat))
    (reportSuccess := true) (reportFailure := false)

/-- Suggest merging two adjacent `rw` tactics if that also solves the goal. -/
register_option linter.tacticAnalysis.rwMerge : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.rwMerge, inherit_doc linter.tacticAnalysis.rwMerge]
def Mathlib.TacticAnalysis.rwMerge : TacticAnalysis.Config := .ofComplex {
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
  tell _stx _old _oldHeartbeats new _newHeartbeats := pure <|
    if new.1.isEmpty then
      m!"Try this: rw {new.2}"
    else none }

/-- Suggest merging `tac; grind` into just `grind` if that also solves the goal. -/
register_option linter.tacticAnalysis.mergeWithGrind : Bool := {
  defValue := false
}

private abbrev mergeWithGrindAllowed : Std.HashSet Name := { `«tactic#adaptation_note_» }

@[tacticAnalysis linter.tacticAnalysis.mergeWithGrind,
  inherit_doc linter.tacticAnalysis.mergeWithGrind]
def Mathlib.TacticAnalysis.mergeWithGrind : TacticAnalysis.Config where
  run seq := do
    if let #[(preCtx, preI), (_postCtx, postI)] := seq[0:2].array then
      if postI.stx.getKind == ``Lean.Parser.Tactic.grind && preI.stx.getKind ∉ mergeWithGrindAllowed then
        if let [goal] := preI.goalsBefore then
          let goals ← try
            preCtx.runTacticCode preI goal postI.stx
          catch _e =>
            pure [goal]
          if goals.isEmpty then
            logWarningAt preI.stx m!"'{preI.stx}; grind' can be replaced with 'grind'"

/-- Suggest replacing a sequence of tactics with `grind` if that also solves the goal. -/
register_option linter.tacticAnalysis.terminalToGrind : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.terminalToGrind,
  inherit_doc linter.tacticAnalysis.terminalToGrind]
def Mathlib.TacticAnalysis.terminalToGrind : TacticAnalysis.Config where
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
          let (oldGoals, heartbeats) ← withHeartbeats <|
            try
              ctx.runTacticCode i goal seq
            catch _e =>
              pure [goal]
          if !oldGoals.isEmpty then
            logWarningAt i.stx m!"Original tactics failed to solve the goal: {seq}"
          oldHeartbeats := heartbeats

          -- To check if `grind` can close the goal, run `grind` on the current goal
          -- and verify that no goals remain afterwards.
          let tac ← `(tactic| grind)
          let (newGoals, heartbeats) ← withHeartbeats <|
            try
              ctx.runTacticCode i goal tac
            catch _e =>
              pure [goal]
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

open Elab.Command

/--
When running the "tryAtEachStep" tactic analysis linters,
only run on a fraction `1/n` of the goals found in the library.

This is useful for running quick benchmarks.
-/
register_option linter.tacticAnalysis.tryAtEachStep.fraction : Nat := {
  defValue := 1
}

/-- Run a tactic at each proof step. -/
def Mathlib.TacticAnalysis.tryAtEachStep (tac : Syntax → MVarId → CommandElabM (TSyntax `tactic)) : TacticAnalysis.Config where
  run seq := do
    let fraction := linter.tacticAnalysis.tryAtEachStep.fraction.get (← getOptions)
    for (ctx, i) in seq do
      if let [goal] := i.goalsBefore then
        if (hash goal) % fraction = 0 then
          let tac ← tac i.stx goal
          let goalsAfter ← try
            ctx.runTacticCode i goal tac
          catch _e =>
            pure [goal]
          if goalsAfter.isEmpty then
            logInfoAt i.stx m!"`{i.stx}` can be replaced with `{tac}`"

/-- Run `grind` at every step in proofs, reporting where it succeeds. -/
register_option linter.tacticAnalysis.tryAtEachStepGrind : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.tryAtEachStepGrind,
   inherit_doc linter.tacticAnalysis.tryAtEachStepGrind]
def tryAtEachStepGrind := tryAtEachStep fun _ _ => `(tactic| grind)

/-- Run `simp_all` at every step in proofs, reporting where it succeeds. -/
register_option linter.tacticAnalysis.tryAtEachStepSimpAll : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.tryAtEachStepSimpAll,
   inherit_doc linter.tacticAnalysis.tryAtEachStepSimpAll]
def tryAtEachStepSimpAll := tryAtEachStep fun _ _ => `(tactic| simp_all)

/-- Run `aesop` at every step in proofs, reporting where it succeeds. -/
register_option linter.tacticAnalysis.tryAtEachStepAesop : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.tryAtEachStepAesop,
   inherit_doc linter.tacticAnalysis.tryAtEachStepAesop]
def tryAtEachStepAesop := tryAtEachStep
  -- As `aesop` isn't imported here, we construct the tactic syntax manually.
  fun _ _ => return ⟨TSyntax.raw <|
    mkNode `Aesop.Frontend.Parser.aesopTactic #[mkAtom "aesop", mkNullNode]⟩

/-- Run `grind +premises` at every step in proofs, reporting where it succeeds. -/
register_option linter.tacticAnalysis.tryAtEachStepGrindPremises : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.tryAtEachStepGrindPremises,
   inherit_doc linter.tacticAnalysis.tryAtEachStepGrindPremises]
def tryAtEachStepGrindPremises := tryAtEachStep fun _ _ => `(tactic| grind +premises)

-- TODO: add compatibility with `rintro` and `intros`
/-- Suggest merging two adjacent `intro` tactics which don't pattern match. -/
register_option linter.tacticAnalysis.introMerge : Bool := {
  defValue := true
}

@[tacticAnalysis linter.tacticAnalysis.introMerge, inherit_doc linter.tacticAnalysis.introMerge]
def Mathlib.TacticAnalysis.introMerge : TacticAnalysis.Config := .ofComplex {
  out := Option (TSyntax `tactic)
  ctx := Array (Array Term)
  trigger ctx stx :=
    match stx with
    | `(tactic| intro%$x $args*) => .continue ((ctx.getD #[]).push
      -- if `intro` is used without arguments, treat it as `intro _`
      <| if args.size = 0 then #[⟨mkHole x⟩] else args)
    | _ => if let some args := ctx then if args.size > 1 then .accept args else .skip else .skip
  test ctx goal := do
    let ctxT := ctx.flatten
    let tac ← `(tactic| intro $ctxT*)
    try
      let _ ← Lean.Elab.runTactic goal tac
      return some tac
    catch _e => -- if for whatever reason we can't run `intro` here.
      return none
  tell _stx _old _oldHeartbeats new _newHeartbeats := pure <|
    if let some tac := new then m!"Try this: {tac}" else none}
