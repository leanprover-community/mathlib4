/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Lean.Linter.Util
import Std.Data.Array.Basic

/-!
#  The non-terminal `simp` linter

The non-terminal `simp` linter makes sure that `simp` is not used as a finishing tactic.
If you want to use `simp [...]` followed by other tactics, then replace `simp [...]` by
* a `suffices \"expr after simp\" by simpa` line;
* the output of `simp? [...]`, so that the final code contains `simp only [...]`;
* something else that does not involve `simp`!

The linter equates "non-terminal" with "does not strictly decrease the number of goals".

##  Implementation detail

The code in this linter is just a very small modification of the code for the
`unreachableTactic` linter.
-/

open Lean Elab

namespace Mathlib.Linter

/-- The non-terminal `simp` linter makes sure that `simp` is not used as a finishing tactic. -/
register_option linter.nonTerminalSimp : Bool := {
  defValue := true
  descr := "enable the 'non-terminal `simp`' linter"
}

namespace nonTerminalSimp

/-- `onlyOrNotSimp stx` if `stx` is syntax for `simp` *without* `only`, then returns `false` else
returs `true`. -/
def onlyOrNotSimp : Syntax → Bool
  | .node _info `Lean.Parser.Tactic.simp #[_, _, _, only?, _, _] => only?[0].getAtomVal == "only"
  | _ => true

/-- The monad for collecting `simp`s that are not `simp only`. -/
abbrev M := StateRefT (HashMap String.Range Syntax) IO

section goals_heuristic
variable (t : TacticInfo)
/-!
###  Heuristics for determining active and inactive goals

The three definitions `inertGoals`, `activeGoalsBefore`, `activeGoalsAfter` extract a list of
`MVarId`s attempting to determine which on which goals the tactic `t` is acting.
This is mostly based on the heuristic that the tactic with "change" an `MVarId`.
-/

/-- `inertGoals t` are the goals that appear before and after the `TacticInfo` `t`.
They should correspond to the goals that are unmodified by `t`. -/
def inertGoals : List MVarId :=
  t.goalsBefore.filter (·.name ∈ t.goalsAfter.map (·.name))

/-- `activeGoalsBefore t` are the `MVarId`s before the `TacticInfo` `t` that "disappear" after it.
They should correspond to the goals in which the tactic `t` performs some action. -/
def activeGoalsBefore : List MVarId :=
  t.goalsBefore.filter (·.name ∉ t.goalsAfter.map (·.name))

/-- `activeGoalsAfter t` are the `MVarId`s after the `TacticInfo` `t` that wern't present before it.
They should correspond to the goals changed by the tactic `t`. -/
def activeGoalsAfter : List MVarId :=
  t.goalsAfter.filter (·.name ∉ t.goalsBefore.map (·.name))

end goals_heuristic

variable (kind : SyntaxNodeKind) in
/-- `extractRealGoals kind tree` takes as input a `SyntaxNodeKind` and an `InfoTree` and returns
the array of pairs `(stx, mvars)`, where `stx` is a syntax node of kind `kind` and `mvars` are
the goals that have been "created" by the tactic in `stx`.

A typical usage is to find the goals following a `simp` application. -/
partial
def extractRealGoals' : InfoTree → Array (Syntax × List MVarId)
  | .node k args =>
    let kargs := (args.map extractRealGoals').foldl (· ++ ·) #[]
    if let Lean.Elab.Info.ofTacticInfo i := k then
      if i.stx.getKind == kind && (i.stx.getRange? true).isSome then
        kargs.push (i.stx, activeGoalsAfter i) else kargs
    else kargs
  | .context _ t => extractRealGoals' t
  | _ => default

variable (take? : Syntax → Bool) in
/-- `extractRealGoals kind tree` takes as input a `SyntaxNodeKind` and an `InfoTree` and returns
the array of pairs `(stx, mvars)`, where `stx` is a syntax node of kind `kind` and `mvars` are
the goals that have been "created" by the tactic in `stx`.

A typical usage is to find the goals following a `simp` application. -/
partial
def extractRealGoals : InfoTree → Array (Syntax × List MVarId)
  | .node k args =>
    let kargs := (args.map extractRealGoals).foldl (· ++ ·) #[]
    if let Lean.Elab.Info.ofTacticInfo i := k then
      if take? i.stx && (i.stx.getRange? true).isSome then
        kargs.push (i.stx, activeGoalsAfter i) else kargs
    else kargs
  | .context _ t => extractRealGoals t
  | _ => default

variable (kind : SyntaxNodeKind) in
@[deprecated extractRealGoals]
partial
def extractGoals : InfoTree → Array (Syntax × List MVarId × List MVarId)
  | .node i args =>
    let kargs := (args.map extractGoals).foldl (· ++ ·) #[]
    if let Lean.Elab.Info.ofTacticInfo i := i then
--      dbg_trace "{i.stx}"
      if i.stx.getKind == kind then kargs.push (i.stx, i.goalsBefore, i.goalsAfter) else kargs
    else kargs
  | .context _ t => extractGoals t
  | _ => default

variable (mvs : List MVarId) in
/-- `getRealFollowers mvs tree` extracts from the `InfoTree` `tree` the array of syntax nodes
that have any one of the `MVarId`s in `mvs` as a goal on which they are "actively"
performing an action. -/
partial
def getRealFollowers : InfoTree → Array Syntax
  | .node k args =>
    let kargs := (args.map getRealFollowers).foldl (· ++ ·) #[]
    if let Lean.Elab.Info.ofTacticInfo i := k then
      if (mvs.map fun x => (x.name ∈ (activeGoalsBefore i).map (·.name) : Bool)).any (·) then kargs.push k.stx else kargs
    else kargs
  | .context _ t => getRealFollowers t
  | _ => default

variable (mvs : List MVarId) in
@[deprecated getRealFollowers]
partial
def getFollowers : InfoTree → Array Syntax
  | .node k args =>
    let kargs := (args.map getFollowers).foldl (· ++ ·) #[]
    if let Lean.Elab.Info.ofTacticInfo i := k then
      if i.goalsBefore == mvs then kargs.push k.stx else kargs
    else kargs
  | _ => default


mutual
/-- Search for `simp`s that
* are not `simp only` and
* do not close a goal.

Add such `simp`s to the state. -/
partial def addNonSimpOnlysList (trees : PersistentArray InfoTree) : M Unit := do
--  let gls := trees.map (extractGoals ``Lean.Parser.Tactic.refine ·)
/-
  Command.liftCoreM do
    Meta.MetaM.run do
      let res := trees.foldl (fun d e => d ++ extractGoals `Lean.Parser.Tactic.refine e) #[]
      for (a, b) in res do
        let mvs ← b.mapM (·.getType)
        logInfo "()"
-/

/-
  let mut rest := #[]
  for d in gls do
  --let postGoals ← gls.mapM fun d =>
    for (s, _, aft) in d do
      dbg_trace "* Following {s}\n"
      let _x_ ← trees.mapM fun s => (for y in (getRealFollowers aft s) do dbg_trace "** {y}\n"; return )
      rest := rest.push aft
-/

--      return aft --(return Prod.snd d)
--  for r in rest do
--    dbg_trace "following {r.map (·.name)}"
--    let x ← trees.mapM fun s => (dbg_trace (getFollowers r s); return )
--  for g in gls do
--    for (stx, goals_before, goals_after) in g do
--      IO.println s!"{stx}"
--      IO.println <| goals_before.map (·.name)
--      IO.println <| goals_after.map (·.name)
  trees.forM addNonSimpOnlys



@[inherit_doc addNonSimpOnlysList]
partial def addNonSimpOnlys : InfoTree → M Unit
  | .node i c => do
    if let .ofTacticInfo i := i then
      let non_terminal_simp? := (! onlyOrNotSimp i.stx) &&
                                (! i.goalsAfter.length < i.goalsBefore.length)
      match i.stx.getRange? true, non_terminal_simp? with
        | some r, true => modify (·.insert r i.stx)
        | _, _ => pure ()
    addNonSimpOnlysList c
  | .context _ t => addNonSimpOnlys t
  | .hole _ => pure ()

end

abbrev allowedSimpFollowers : Array SyntaxNodeKind := #[]

/-- Gets the value of the `linter.nonTerminalSimp` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.nonTerminalSimp o

/-- The main entry point to the unreachable tactic linter. -/
def nonTerminalSimpLinter : Linter where run := withSetOptionIn fun _stx => do
  unless getLinterHash (← getOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return
--  dbg_trace "processing"
  let trees ← getInfoTrees
  let (_, map) ← (addNonSimpOnlysList trees).run {}
--  dbg_trace "processing1"

  trees.forM fun tree => do
--    dbg_trace "processing2"
    let d := extractRealGoals (fun stx => stx.getKind == ``Lean.Parser.Tactic.simp && (stx.getRange? true).isSome) tree --``Lean.Parser.Tactic.refine tree
--    dbg_trace "processing3 {d.map Prod.fst} {d.size}"
    for (st, aft) in d do
--      dbg_trace "* Following {st}\n"

      --for s in trees do
--      let mut tot := #[]
      for y in (getRealFollowers aft tree) do

--        tots := tots.push (y, st)
--          dbg_trace "{y.getAtomVal} follows {st.getAtomVal}"
          Linter.logLint linter.nonTerminalSimp y m!"follows {st}\n{y.getKind}"
--          tot := tot.push m!"follows {st}"
--      logInfo m!"{tot}"
/-
  let gls := trees.map (extractGoals ``Lean.Parser.Tactic.refine ·)
  for d in gls do
  --let postGoals ← gls.mapM fun d =>
    for (st, _, aft) in d do
      --dbg_trace "* Following {s}\n"
      for s in trees do
        for y in (getRealFollowers aft s) do

--        tots := tots.push (y, st)
          Linter.logLint linter.nonTerminalSimp y m!"follows {st}"
-/
--          dbg_trace "** {y} {r}\n"; --return
--      rest := rest.push aft

/-
  let simps := map.toArray
  let key (r : String.Range) := (r.start.byteIdx, (-r.stop.byteIdx : Int))
  let mut last : String.Range := ⟨0, 0⟩
  for (r, stx) in let _ := @lexOrd; let _ := @ltOfOrd.{0}; simps.qsort (key ·.1 < key ·.1) do
    if last.start ≤ r.start && r.stop ≤ last.stop then continue
    Linter.logLint linter.nonTerminalSimp stx
      "non-terminal simp: consider replacing it with\n\
        * `suffices \"expr after simp\" by simpa`\n\
        * the output of `simp?`\n"
    last := r
-/

initialize addLinter nonTerminalSimpLinter
