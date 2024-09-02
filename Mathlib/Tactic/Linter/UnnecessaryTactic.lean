/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Lean.Linter.Util

/-!
#  The "unnecessaryTactic" linter

The "unnecessaryTactic" linter emits a warning somewhere.
-/

open Lean Elab Command

namespace Mathlib.Linter

--partial
--def findTacs (stx : Syntax) : Array (Array Syntax) :=
--  let next := stx.foldArgs (fun arg r => r ++ findTacs arg) #[]
--  if let .node _ ``Lean.Parser.Tactic.tacticSeq1Indented #[.node _ _ args] := stx then
--    let tacs := args.filter (fun s => s.getAtomVal != ";" && !s.isOfKind `null)
--    if 2 ≤ tacs.size then
--      next.push tacs
--    else next
--  else next

abbrev exclusions : HashSet SyntaxNodeKind := HashSet.empty
  |>.insert `Batteries.Tactic.«tacticOn_goal-_=>_»
  |>.insert `«tactic#adaptation_note_»
  |>.insert ``Lean.Parser.Tactic.tacticRepeat_
  |>.insert ``Lean.cdot
  --|>.insert `«;»
  --|>.insert `null
  |>.insert ``Lean.Parser.Tactic.induction
  |>.insert `Mathlib.Tactic.induction'
  --|>.insert ``Lean.Parser.Term.byTactic
  --|>.insert `by

partial
def findRanges (stx : Syntax) : HashSet (String.Range × SyntaxNodeKind) :=
  let next := stx.foldArgs (fun arg r => r.merge (findRanges arg)) {}
  match stx.getKind with
      -- ignore default values when they involve tactics and syntax quotations
    | ``Lean.Parser.Term.binderTactic | ``Lean.Parser.Tactic.quot => {}
    | ``Lean.Parser.Tactic.tacticSeq1Indented =>
      -- first, we sift out `;` and `null` nodes that are interspersed in `tacticSeq`
      let tacs := stx[0].getArgs.filter (! [`«;», `null].contains ·.getKind)
      -- if there are at least two tactics in the block...
      if 2 ≤ tacs.size then
        -- we exclude the `exclusions` and add everything else to the ranges to be inspected
        let tacs := tacs.filter (! exclusions.contains ·.getKind)
        next.insertMany <|
          (tacs.filterMap fun t => t.getRange?.map (·, t.getKind)).toList.reduceOption
      else next
    | _ => next

partial
def erasable (rgs : HashSet (String.Range × SyntaxNodeKind)) (tree : InfoTree) :
    HashSet (String.Range × SyntaxNodeKind) := Id.run do
  match tree with
    | .context _ t => erasable rgs t
    | .node info args =>
      if let .ofTacticInfo i := info then
        let rg := rgs.find? ((i.stx.getRange? true).getD default, i.stx.getKind)
        if rg.isSome && i.goalsBefore != i.goalsAfter then
          --dbg_trace "{i.stx.getKind} -- modifies"
          return (args.foldl (fun a b => (erasable (rgs.erase rg.get!) b).merge (a.erase rg.get!)) {}).insert rg.get!
        else
          if rg.isSome then
            --dbg_trace "{i.stx.getKind} -- does not modify"
            return args.foldl (fun a b => (erasable (rgs.erase rg.get!) b).merge a) {}
          else
            return args.foldl (fun a b => (erasable rgs b).merge a) {}

      else
        return args.foldl (fun a b => (erasable rgs b).merge a) {}
    | _  => return {}

def ctorInfo : Info → String
  | .ofTacticInfo _ => "TacticInfo"
  | .ofTermInfo _ => "TermInfo"
  | .ofCommandInfo _ => "CommandInfo"
  | .ofMacroExpansionInfo _ => "MacroExpansionInfo"
  | .ofOptionInfo _ => "OptionInfo"
  | .ofFieldInfo _ => "FieldInfo"
  | .ofCompletionInfo _ => "CompletionInfo"
  | .ofUserWidgetInfo _ => "UserWidgetInfo"
  | .ofCustomInfo _ => "CustomInfo"
  | .ofFVarAliasInfo _ => "FVarAliasInfo"
  | .ofFieldRedeclInfo _ => "FieldRedeclInfo"
  | .ofOmissionInfo _ => "OmissionInfo"



partial
def traceIT : InfoTree → String
    | .context _ t => "context " ++ traceIT t
    | .node info args => args.foldl (· ++ traceIT ·) s!"node {ctorInfo info}"
    | _  => "mvar"


partial
def wr : HashSet (String.Range × SyntaxNodeKind) → InfoTree → HashSet (String.Range × SyntaxNodeKind)
  | rgs, .context _ t => wr rgs t
  | rgs, .node info args =>
    --let rest := args.foldl (fun a b => (wr rgs b).merge a) {}
    if let .ofTacticInfo i := info then
      let rg := rgs.find? ((i.stx.getRange? true).getD default, i.stx.getKind)
      if rg.isSome && i.goalsBefore != i.goalsAfter then
        let newRgs := rgs.erase rg.get!
        let rest := args.foldl (fun a b => (wr newRgs b).merge (a.erase rg.get!)) newRgs
        --dbg_trace "{i.stx.getKind} -- erasing"
        rest.erase (i.stx.getRange?.getD default, i.stx.getKind)
      else
        if rg.isSome then
          --dbg_trace "{i.stx.getKind} -- unused"
          args.foldl (fun a b => (wr rgs b).merge a) rgs
        else
          args.foldl (fun a b => (wr rgs b).merge a) rgs

    else
      args.foldl (fun a b => (wr rgs b).merge a) rgs
  | rgs, _  => rgs

/-- The "unnecessaryTactic" linter emits a warning when there are multiple active goals. -/
register_option linter.unnecessaryTactic : Bool := {
  defValue := true
  descr := "enable the unnecessaryTactic linter"
}

namespace UnnecessaryTactic

@[inherit_doc Mathlib.Linter.linter.unnecessaryTactic]
def unnecessaryTacticLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.unnecessaryTactic (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let rgs := findRanges stx
  --for r in rgs do
  --  logInfoAt (.ofRange r) m!"found you {(r.start, r.stop - r.start)}!"
  let trees ← getInfoTrees
  let mut fd := {}
  --dbg_trace "found {trees.size} infotrees"
  for t in trees do
    if let .node _ arg := t then -- (.ofOptionInfo i) (.ofCompletionInfo i)
      if arg.isEmpty then
        --dbg_trace traceIT t
        --let rg := i.stx.getRange?.getD default
        --dbg_trace "{(rg.start, rg.stop)} -- {rg.stop - rg.start}"
        continue
    --dbg_trace traceIT t
    fd := wr rgs t
    fd := erasable rgs t
    --dbg_trace "size: {fd.size}, rgs: {rgs.size}"
    for (e, str) in rgs do
      if ! fd.contains (e, str) then
        Linter.logLint linter.unnecessaryTactic (.ofRange e)
          m!"'{str}, {(e.start, e.stop - e.start)}' is unnecessary."
    --dbg_trace fd.size
    --for (e, str) in fd do
    --  dbg_trace "erasable: {(e.start, e.stop - e.start)} {str}}"

initialize addLinter unnecessaryTacticLinter

end UnnecessaryTactic

end Mathlib.Linter
