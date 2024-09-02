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
  |>.insert `«;»
  |>.insert `null
  --|>.insert ``Lean.Parser.Term.byTactic
  --|>.insert `by
#check HashMap
partial
def findRanges (stx : Syntax) : HashSet (String.Range × SyntaxNodeKind) :=
  let next := stx.foldArgs (fun arg r => r.merge (findRanges arg)) {}
  if let .node _ ``Lean.Parser.Tactic.tacticSeq1Indented #[.node _ _ args] := stx then
    let tacs := args.filter (! exclusions.contains ·.getKind)
    if 2 ≤ tacs.size then
      next.insertMany <| (tacs.filterMap fun t => t.getRange?.map (·, t.getKind)).toList.reduceOption
    else next
  else next

partial
def erasable (toErase rgs : HashSet (String.Range × SyntaxNodeKind)) (tree : InfoTree) :
    HashSet (String.Range × SyntaxNodeKind) := Id.run do
  let mut toErase := toErase
  match tree with
    | .context _ t => erasable toErase rgs t
    | .node info args =>
      let rest := args.foldl (fun a b => (erasable toErase rgs b).merge a) {}
      if let .ofTacticInfo i := info then
        let rg := rgs.find? ((i.stx.getRange? true).getD default, i.stx.getKind)
        if rg.isSome && i.goalsBefore != i.goalsAfter then
          dbg_trace "{i.stx.getKind} -- erasing"
          toErase := toErase.insert rg.get!
          return args.foldl (fun a b => (erasable toErase rgs b).merge a) {}
        else
          if rg.isSome then
            dbg_trace "{i.stx.getKind} -- unused"
            args.foldl (fun a b => (wr rgs b).merge a) rgs
          else
            args.foldl (fun a b => (wr rgs b).merge a) rgs

      else
        args.foldl (fun a b => (wr rgs b).merge a) rgs
    | _  => rgs

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
        dbg_trace "{i.stx.getKind} -- erasing"
        rest.erase (i.stx.getRange?.getD default, i.stx.getKind)
      else
        if rg.isSome then
          dbg_trace "{i.stx.getKind} -- unused"
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
  dbg_trace "found {trees.size} infotrees"
  for t in trees do
    fd := wr rgs t
    --dbg_trace "size: {fd.size}, rgs: {rgs.size}"
    for (e, str) in fd do
      Linter.logLint linter.unnecessaryTactic (.ofRange e) m!"'{str}, {(e.start, e.stop - e.start)}' is unnecessary."

initialize addLinter unnecessaryTacticLinter

end UnnecessaryTactic

end Mathlib.Linter
