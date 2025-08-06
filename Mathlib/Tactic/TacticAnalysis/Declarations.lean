import Mathlib.Tactic.TacticAnalysis

open Lean

@[tacticAnalysis]
def grindReplacement : TacticAnalysis.Config := .ofComplex `linter.tacticAnalysis.grindReplacement {
  out := (List MVarId × MessageData)
  ctx := Syntax
  trigger _ stx := if
      stx.getKind ∈
        [`Mathlib.Tactic.linarith, `Lean.Parser.Tactic.omega, `Mathlib.Tactic.RingNF.ring]
    then .accept stx else .skip
  test stx goal := withOptions (fun opts => opts.set `grind.warning false) do
    let tac ← `(tactic| grind)
    try
      let (goals, _) ← Lean.Elab.runTactic goal tac
      return (goals, m!"")
    catch _e => -- Grind throws an error if it fails.
      let name ← mkAuxDeclName `extracted
      let ((sig, _, modules), _) ← (Mathlib.Tactic.ExtractGoal.goalSignature name goal).run
      let imports := modules.toList.map (s!"import {·}")
      return ([goal], m!"{"\n".intercalate imports}\n\ntheorem {sig} := by\n  fail_if_success grind\n  {stx}")
  tell stx _old new :=
    if new.1.1 != [] then
      m!"'grind' failed where '{stx}' succeeded. Counterexample:\n{new.1.2}"
    /-
    else
      if old.2 * 2 < new.2 then
        return m!"'grind' is slower than '{stx}': {new.2 / 1000} versus {old.2 / 1000} heartbeats"
    -/
    else none }

/-
@[tacticAnalysis]
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
  tell _stx _old new :=
    if new.1.1.isEmpty then
      m!"Try this: rw {new.1.2}"
    else none }

@[tacticAnalysis]
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

@[tacticAnalysis]
def terminalToGrind : TacticAnalysis.Config where
  run seq := do
    let threshold := 3
    let mut replaced : Array (TSyntax `tactic) := #[]
    let mut success := false
    for (ctx, i) in seq.reverse do
      if replaced.size >= threshold - 1 && i.stx.getKind != ``Lean.Parser.Tactic.grind then
        if let [goal] := i.goalsBefore then
          let goals ← ctx.runTactic i goal <| fun goal => do
            let tac ← `(tactic| grind)
            let (goals, _) ←
              try
                Lean.Elab.runTactic goal tac
              catch _e =>
                pure ([goal], {})
            return goals
          if goals.isEmpty then
            success := true
          else
            break
        else
          break
      replaced := replaced.push ⟨i.stx⟩
    replaced := replaced.reverse

    if h : replaced.size >= threshold ∧ success then
      let stx := replaced[0]
      let seq ← `(tactic| $replaced;*)
      logWarningAt stx m!"replace the proof with 'grind': {seq}"
-/
