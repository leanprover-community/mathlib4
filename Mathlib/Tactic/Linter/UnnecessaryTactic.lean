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
  |>.insert ``Lean.Parser.Tactic.induction
  |>.insert `«tactic#adaptation_note_»

def keepTactic (s : Syntax) : Bool :=
  (s.getAtomVal != ";" && !s.isOfKind `null) &&
  ! exclusions.contains s.getKind


partial
def findRanges (stx : Syntax) : HashSet String.Range :=
  let next := stx.foldArgs (fun arg r => r.merge (findRanges arg)) {}
  if let .node _ ``Lean.Parser.Tactic.tacticSeq1Indented #[.node _ _ args] := stx then
    let tacs := args.filter keepTactic
    if 2 ≤ tacs.size then
      next.insertMany <| (tacs.map (·.getRange?)).toList.reduceOption
    else next
  else next

partial
def wr : HashSet String.Range → InfoTree → HashSet (String.Range × String)
  | rgs, .context _ t => wr rgs t
  | rgs, .node info args =>
    --let rest := args.foldl (fun a b => (wr rgs b).merge a) {}
    if let .ofTacticInfo i := info then
      let rg := rgs.find? ((i.stx.getRange? true).getD default)
      if rg.isSome && i.goalsBefore == i.goalsAfter
        then
        let rest := args.foldl (fun a b => (wr (rgs.erase rg.get!) b).merge a) {}
        --dbg_trace "adding {i.stx}"
        rest.insert (i.stx.getRange?.getD default, s!"{i.stx.getKind}\n{i.stx}")
      else
        --dbg_trace "tactic, not equal\n{i.stx}\n"
      args.foldl (fun a b => (wr rgs b).merge a) {}

    else
      args.foldl (fun a b => (wr rgs b).merge a) {}
  | _rgs, _  => {}

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
  for t in trees do
    fd := wr rgs t
    --dbg_trace "size: {fd.size}, rgs: {rgs.size}"
    for (e, str) in fd do
      Linter.logLint linter.unnecessaryTactic (.ofRange e) m!"'{str}' is unnecessary."

initialize addLinter unnecessaryTacticLinter

end UnnecessaryTactic

end Mathlib.Linter
