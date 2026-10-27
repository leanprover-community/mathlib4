/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib contributors
-/
module

public meta import Aesop
public meta import Mathlib.Tactic.DepRewrite
public meta import Mathlib.Tactic.GRewrite.Elab
public meta import Mathlib.Tactic.SimpRw
public meta import Mathlib.Tactic.TacticAnalysis.Declarations

/-!
# Tactic replacement linters

This file defines always-on tactic analysis passes which find uses of powerful tactics that can be
replaced by simpler ones.
-/

public meta section

open Lean Elab Command
open Mathlib TacticAnalysis

/--
Check a terminal replacement at every execution of a source-level tactic before suggesting it.

Tactic combinators such as `<;>` can execute the same syntax once for each generated goal.  A
source replacement is valid only when the new tactic closes every one of those goals.
-/
private def terminalReplacementAtAllOccurrences (newTacticName : String)
    (oldTacticKind : SyntaxNodeKind)
    (newTactic : ContextInfo → TacticInfo → Syntax → CommandElabM (TSyntax `tactic)) :
    TacticAnalysis.Config where
  run _ := pure ()
  runAll := some fun seqs => do
    let mut seen : Array (String.Pos.Raw × String.Pos.Raw) := #[]
    for seq in seqs do for i in seq do
      if i.tacI.stx.getKind != oldTacticKind then
        continue
      let some start := i.tacI.stx.getPos? | continue
      let some stop := i.tacI.stx.getTailPos? | continue
      let span := (start, stop)
      if seen.contains span then
        continue
      seen := seen.push span
      let suggestion ← newTactic i.ctxI i.tacI i.tacI.stx
      let mut succeedsEverywhere := true
      for seq' in seqs do for j in seq' do
        if j.tacI.stx.getKind == oldTacticKind && j.tacI.stx.getPos? == some start &&
            j.tacI.stx.getTailPos? == some stop then
          if let [goal] := j.tacI.goalsBefore then
            let tac ← newTactic j.ctxI j.tacI j.tacI.stx
            let goals ← try
              ({ j.ctxI with mctx := j.tacI.mctxBefore }).runTacticCode j.tacI goal tac
            catch _ =>
              pure [goal]
            if !goals.isEmpty then
              succeedsEverywhere := false
          else
            succeedsEverywhere := false
      if succeedsEverywhere then
        let msg ← addMessageContext m!"`{newTacticName}` can replace `{i.tacI.stx}`"
        let header := (← msg.toString) ++ "\n\nTry this:"
        liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion
          (header := header) i.tacI.stx suggestion

/-- Report places where `aesop` can be replaced by `simp_all`. -/
register_option linter.tacticAnalysis.aesopToSimpAll : Bool := {
  defValue := true
}

@[tacticAnalysis linter.tacticAnalysis.aesopToSimpAll,
  inherit_doc linter.tacticAnalysis.aesopToSimpAll]
def aesopToSimpAll :=
  terminalReplacementAtAllOccurrences "simp_all"
    ``Aesop.Frontend.Parser.aesopTactic (fun _ _ _ => `(tactic| simp_all))

/-- Report places where `aesop` can be replaced directly by `simp`. -/
register_option linter.tacticAnalysis.aesopToSimp : Bool := {
  defValue := true
}

@[tacticAnalysis linter.tacticAnalysis.aesopToSimp,
  inherit_doc linter.tacticAnalysis.aesopToSimp]
def aesopToSimp :=
  terminalReplacementAtAllOccurrences "simp"
    ``Aesop.Frontend.Parser.aesopTactic (fun _ _ _ => `(tactic| simp))

/-- Report places where `simp_all` can be replaced by `simp`. -/
register_option linter.tacticAnalysis.simpAllToSimp : Bool := {
  defValue := true
}

@[tacticAnalysis linter.tacticAnalysis.simpAllToSimp,
  inherit_doc linter.tacticAnalysis.simpAllToSimp]
def simpAllToSimp :=
  terminalReplacementAtAllOccurrences "simp" ``Lean.Parser.Tactic.simpAll
    (fun _ _ stx => match stx with
      | `(tactic| simp_all%$tk $cfg:optConfig $(discharger)? $[only%$o]?
          $[[$args,*]]?) =>
        `(tactic| simp%$tk $cfg:optConfig $[$discharger]? $[only%$o]? $[[$args,*]]?)
      | _ => `(tactic| simp))

/-- Report places where `grind` can be replaced by `lia`. -/
register_option linter.tacticAnalysis.grindToLia : Bool := {
  defValue := true
}

@[tacticAnalysis linter.tacticAnalysis.grindToLia,
  inherit_doc linter.tacticAnalysis.grindToLia]
def grindToLia :=
  terminalReplacementAtAllOccurrences "lia" ``Lean.Parser.Tactic.grind
    (fun _ _ _ => `(tactic| lia))

/-- Construct the corresponding `rw` call for a `simp_rw`, `rw!`, or `grw` call. -/
private def rewriteToRw (stx : Syntax) : CommandElabM (TSyntax `tactic) :=
  match stx with
  | `(tactic| simp_rw $_:optConfig $rules:rwRuleSeq $(loc)?) =>
    `(tactic| rw $rules:rwRuleSeq $[$loc]?)
  | `(tactic| rw! $_:optConfig $rules:rwRuleSeq $(loc)?) =>
    `(tactic| rw $rules:rwRuleSeq $[$loc]?)
  | `(tactic| grw $_:optConfig $rules:rwRuleSeq $(loc)?) =>
    `(tactic| rw $rules:rwRuleSeq $[$loc]?)
  | _ => `(tactic| rw [])

/-- Pretty-print the goals in a recorded metavariable context for comparison with a replacement. -/
private def ppGoals (ctxI : ContextInfo) (mctx : MetavarContext) (goals : List MVarId) :
    CommandElabM (List String) :=
  goals.mapM fun goal => do
    let lctx := (mctx.decls.find! goal).lctx
    (·.1) <$> ctxI.runCoreMWithMessages (Meta.MetaM.run (ctx := { lctx }) (s := { mctx }) do
      withOptions (·.setBool `pp.mvars false) do
        return toString (← Meta.ppGoal goal))

/--
Define a pass that tries replacing a tactic and checks that it produces the same proof state.

Unlike `terminalReplacement`, this also handles tactics which leave goals for subsequent tactics.
-/
private def tacticReplacement (newTacticName : String)
    (oldTacticKind : SyntaxNodeKind)
    (newTactic : Syntax → CommandElabM (TSyntax `tactic)) : TacticAnalysis.Config where
  run _ := pure ()
  runAll := some fun seqs => do
    let mut seen : Array (String.Pos.Raw × String.Pos.Raw) := #[]
    for seq in seqs do for i in seq do
      if i.tacI.stx.getKind != oldTacticKind then
        continue
      let some start := i.tacI.stx.getPos? | continue
      let some stop := i.tacI.stx.getTailPos? | continue
      let span := (start, stop)
      if seen.contains span then
        continue
      seen := seen.push span
      let suggestion ← newTactic i.tacI.stx
      let mut matchesEverywhere := true
      for seq' in seqs do for j in seq' do
        if j.tacI.stx.getKind == oldTacticKind && j.tacI.stx.getPos? == some start &&
            j.tacI.stx.getTailPos? == some stop then
          if let [goal] := j.tacI.goalsBefore then
            let tac ← newTactic j.tacI.stx
            let oldGoals ← ppGoals j.ctxI j.tacI.mctxAfter j.tacI.goalsAfter
            let newGoals? ← try
              some <$> ({ j.ctxI with mctx := j.tacI.mctxBefore }).runTacticCode j.tacI goal tac
                ⟨String, fun goal => withOptions (·.setBool `pp.mvars false) do
                  return toString (← Meta.ppGoal goal)⟩
            catch _ =>
              pure none
            if newGoals? != some oldGoals then
              matchesEverywhere := false
          else
            matchesEverywhere := false
      if matchesEverywhere then
        let msg ← if (← liftCoreM <| PrettyPrinter.ppTactic suggestion).pretty = newTacticName then
          pure m!"`{newTacticName}` can replace `{i.tacI.stx}`"
        else
          pure m!"`{newTacticName}` can replace `{i.tacI.stx}` using `{suggestion}`"
        let msg ← addMessageContext msg
        let header := (← msg.toString) ++ "\n\nTry this:"
        liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion
          (header := header) i.tacI.stx suggestion

/-- Report places where `simp_rw` can be replaced by `rw`. -/
register_option linter.tacticAnalysis.simpRwToRw : Bool := {
  defValue := true
}

@[tacticAnalysis linter.tacticAnalysis.simpRwToRw,
  inherit_doc linter.tacticAnalysis.simpRwToRw]
def simpRwToRw :=
  tacticReplacement "rw" ``Mathlib.Tactic.simpRw rewriteToRw

/-- Report places where `rw!` can be replaced by `rw`. -/
register_option linter.tacticAnalysis.depRwToRw : Bool := {
  defValue := true
}

@[tacticAnalysis linter.tacticAnalysis.depRwToRw,
  inherit_doc linter.tacticAnalysis.depRwToRw]
def depRwToRw :=
  tacticReplacement "rw" ``Mathlib.Tactic.DepRewrite.depRwSeq rewriteToRw

/-- Report places where `grw` can be replaced by `rw`. -/
register_option linter.tacticAnalysis.grwToRw : Bool := {
  defValue := true
}

@[tacticAnalysis linter.tacticAnalysis.grwToRw,
  inherit_doc linter.tacticAnalysis.grwToRw]
def grwToRw :=
  tacticReplacement "rw" ``Mathlib.Tactic.GRewrite.grwSeq rewriteToRw
