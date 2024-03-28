/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Lean.Linter.Util
import Std.Data.Array.Basic
import Std.Data.List.Basic
import Std.Data.Array.Merge

--import Mathlib.adomaniLeanUtils.inspect_syntax

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

end nonTerminalSimp

end Mathlib.Linter

section goals_heuristic
namespace Lean namespace Elab namespace TacticInfo
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

end TacticInfo end Elab end Lean
end goals_heuristic

namespace Mathlib.Linter.nonTerminalSimp
open Lean Elab TacticInfo

variable (kind : SyntaxNodeKind) in
/-- `extractRealGoals' kind tree` takes as input a `SyntaxNodeKind` and an `InfoTree` and returns
the array of pairs `(stx, mvars)`, where `stx` is a syntax node of kind `kind` and `mvars` are
the goals that have been "created" by the tactic in `stx`.

A typical usage is to find the goals following a `simp` application. -/
partial
def extractRealGoals' : InfoTree → Array (Syntax × List MVarId)
  | .node k args =>
    let kargs := (args.map extractRealGoals').foldl (· ++ ·) #[]
    if let Lean.Elab.Info.ofTacticInfo i := k then
      if i.stx.getKind == kind && (i.stx.getRange? true).isSome then
        kargs.push (i.stx, i.activeGoalsAfter) else kargs
    else kargs
  | .context _ t => extractRealGoals' t
  | _ => default

variable (take? : Syntax → Bool) in
/-- `extractRealGoals take? tree` takes as input a function `take? : Syntax → Bool` and
an `InfoTree` and returns the array of pairs `(stx, mvars)`,
where `stx` is a syntax node such that `take? stx` is `true` and
`mvars` are the goals that have been "created" by the tactic in `stx`.

A typical usage is to find the goals following a `simp` application. -/
partial
def extractRealGoals : InfoTree → Array (Syntax × List MVarId)
  | .node k args =>
    let kargs := (args.map extractRealGoals).foldl (· ++ ·) #[]
    if let Lean.Elab.Info.ofTacticInfo i := k then
      if take? i.stx && (i.stx.getRange? true).isSome then
        kargs.push (i.stx, i.activeGoalsAfter) else kargs
    else kargs
  | .context _ t => extractRealGoals t
  | _ => default

variable (take? : Syntax → Bool) in
/-- `extractRealGoalsCtx take? tree` takes as input a function `take? : Syntax → Bool` and
an `InfoTree` and returns the array of pairs `(stx, mvars)`,
where `stx` is a syntax node such that `take? stx` is `true` and
`mvars` are the goals that have been "created" by the tactic in `stx`.

A typical usage is to find the goals following a `simp` application. -/
partial
def extractRealGoalsCtx : InfoTree → Array (Syntax × MetavarContext × List MVarId)
  | .node k args =>
    let kargs := (args.map extractRealGoalsCtx).foldl (· ++ ·) #[]
    if let Lean.Elab.Info.ofTacticInfo i := k then
      if take? i.stx && (i.stx.getRange? true).isSome then
        kargs.push (i.stx, i.mctxAfter, i.activeGoalsAfter) else kargs
    else kargs
  | .context _ t => extractRealGoalsCtx t
  | _ => default

variable (take? : Syntax → Bool) in
-- also returns the preceding goals that change.  is there only one always?
/-- `extractRealGoalsCtx' take? tree` takes as input a function `take? : Syntax → Bool` and
an `InfoTree` and returns the array of pairs `(stx, mvars)`,
where `stx` is a syntax node such that `take? stx` is `true` and
`mvars` are the goals that have been "created" by the tactic in `stx`.

A typical usage is to find the goals following a `simp` application. -/
partial
def extractRealGoalsCtx' : InfoTree → Array (Syntax × MetavarContext × MetavarContext × List MVarId × List MVarId)
  | .node k args =>
    let kargs := (args.map extractRealGoalsCtx').foldl (· ++ ·) #[]
    if let Lean.Elab.Info.ofTacticInfo i := k then
      if take? i.stx && (i.stx.getRange? true).isSome then
        #[(i.stx, i.mctxBefore, i.mctxAfter, i.activeGoalsBefore, i.activeGoalsAfter)] ++ kargs else kargs
    else if let .ofFVarAliasInfo i := k then
      dbg_trace (i.userName, i.id.name, i.baseId.name)
      kargs
    else kargs
  | .context _ t => extractRealGoalsCtx' t
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

abbrev allowedSimpFollowers : HashSet SyntaxNodeKind := HashSet.empty
  |>.insert ``cdotTk
  |>.insert ``Lean.Parser.Tactic.tacticSeq1Indented
--  |>.insert ``nullKind
  |>.insert `null
  |>.insert ``Lean.Parser.Tactic.tacticSeq
  |>.insert ``Lean.Parser.Tactic.paren
  |>.insert ``cdot
  |>.insert ``Lean.Parser.Tactic.simpa
  |>.insert ``Lean.Parser.Tactic.simp
  |>.insert ``Lean.Parser.Tactic.allGoals
  |>.insert ``Lean.Parser.Tactic.eqRefl
  |>.insert ``Lean.Parser.Tactic.tacticRfl
  |>.insert ``Lean.Parser.Tactic.rewriteSeq
    -- `Lean.Parser.Tactic.rwSeq` would catch `rw`: unnecessary, `rewrite` already catches it

--def simpLocs : Syntax → Syntax
--  | `(simp config discharger?) => default
--  | _ => default

partial
def getLocs (stx : Syntax) (all? : Syntax → Bool := fun _ ↦ false) : Array Syntax :=
  match stx with
    | stx@(.node _ ``Lean.Parser.Tactic.location loc) =>
      if all? stx then #[] else loc.eraseIdx 0
    | .node _ _ args => (args.map (getLocs · all?)).flatten
    | _ => default

abbrev star : Syntax :=
  Syntax.node1 .none ``Lean.Parser.Tactic.locationWildcard (Lean.mkAtom "*")

def simpLocs : Syntax → Bool
  | .node _info `Lean.Parser.Tactic.simp
    #[_, _, _, .node .none _ #[/-no only-/], _, .node .none _ loc] =>
    match loc with
      | #[.node _ ``Lean.Parser.Tactic.location #[_at, loc]] =>
        --dbg_trace "{loc}"
        true
      | #[] =>
        --dbg_trace "no loc"
        true
      | _ => false
  | _ => false

def modifiedLocs (stx : Syntax) : Array Name :=
  let locs := getLocs stx
  dbg_trace "{stx} modifies {locs}"
  #[]

partial
def sloc : Syntax → Command.CommandElabM Unit
  | stx@(.node _ _ args) => do
    --if simpLocs stx then logInfoAt stx "here"
    let _ ← args.mapM sloc
  | _ => return
#check List.getLastD
partial
def getTactics : Syntax → Array Syntax
  | stx@(.node _ kind args) =>
    let next := (args.map getTactics).flatten
    let parts := kind.components
    if parts.contains `Tactic
       && (! "location".isPrefixOf (parts.getLastD default).toString)
       && (! "rwRule".isPrefixOf (parts.getLastD default).toString)
    then next.push stx else next
  | _ => default

partial
def getIds : Syntax → Array Name
  | .node _ _ args => (args.map getIds).flatten
  | .atom _ v => match v with
                  | "*" => #[`wildcard]
                  | "⊢" => #[`goal]
                  | "|" => #[`goal]
                  | _ => default
  | stx => #[stx.getId]

/-- `stained` is the type of the stained locations: it can be
* the `Name` (typically of a local declaration);
* the goal (`⊢`);
* the "wildcard" -- all the declaration in context (`*`).
-/
inductive stained
  | name     : Name → stained
  | goal     : stained
  | wildcard : stained
  deriving Repr, Inhabited, DecidableEq, Hashable

/-- Converting a `stained` to a `String`:
* a `Name` is represented by the corresponding string;
* `goal` is represented by `⊢`;
* `wildcard` is represented by `*`.
-/
instance : ToString stained where
  toString | .name n => n.toString | .goal => "⊢" | .wildcard => "*"

partial
def getStainedold : Syntax → Array stained
  | .node _ _ args => (args.map getStainedold).flatten
  | .atom _ v => match v with
                  | "*" => #[.wildcard]
                  | "⊢" => #[.goal]
                  | "|" => #[.goal]
                  | _ => default
  | stx => #[.name stx.getId]

def getStained!old (stx : Syntax) : Array stained :=
  match getStainedold stx with
    | #[] => #[.goal]
    | out => out

/-- extracts the "locations" from syntax, producing an array of `stained`. -/
partial
def getL : Syntax → Array stained
  | .node _ _ arg => (arg.map getL).flatten
  | .ident _ _ v _ => #[.name v]
  | .atom _ v => match v with
                  | "*" => #[.wildcard]
                  | "⊢" => #[.goal]
                  | "|" => #[.goal]
                  | _ => default
  | _ => default

set_option hygiene false in
run_cmd Command.liftCoreM do Meta.MetaM.run do
    let simpStx ← `(tactic| simp at h j ⊢)
    let rwStx ← `(tactic| rw [] at h j ⊢)
    let stxs := #[simpStx, rwStx]
    for stx in stxs do
      let locs := getL stx
      guard <| locs = #[.name `h, .name `j, .goal]
    let rwStar ← `(tactic| rw [] at *)
    guard <| getL rwStar = #[.wildcard]

/-- `getStained stx` expects `stx` to be an argument of a node of `SyntaxNodeKind`
`Lean.Parser.Tactic.location`.
Typically, we apply `getStained` to the output of `getLocs`. -/
partial
def getStained (stx : Syntax) (all? : Syntax → Bool := fun _ ↦ false) : Array stained :=
  match stx with
    | stx@(.node _ ``Lean.Parser.Tactic.location loc) =>
      if all? stx then #[] else (loc.map getL).flatten
    | .node _ _ args => (args.map (getStained · all?)).flatten
    | _ => default

/-- `getStained! stx` acts almost like `getStained stx`, except that it returns
`#[⊢]` if `getStained stx = #[]`. -/
def getStained! (stx : Syntax) (all? : Syntax → Bool := fun _ ↦ false) : Array stained :=
  match getStained stx all? with
    | #[] => #[.goal]
    | out => out


open Lean Elab Command
elab "get " cmd:command : command => do
  let tcts := getTactics cmd
--  logInfo m!"{tcts.map fun t => (t, getLocs t)}"
  for tac in tcts do
--    let locs := getLocs tac
--    logInfoAt tac m!"may act on {locs.map getStained}"
--    dbg_trace "{tac}:\nlocs: {getLocs tac}\n"
--    let _ ← (getLocs tac).mapM (Meta.inspect ·)
--    dbg_trace "{tac.getKind} {getStained tac}"
    let locs := getStained tac

--    Meta.inspect tac
    dbg_trace "{tac}\n{locs}\n"
--    logInfoAt tac m!"may act on {locs} and {getStained! tac}"
    --logInfo m!"tactic: '{tac}'\nacts:   {locs}\natoms: {locs.map getStained}"
--    let _ ← locs.mapM Meta.inspect
--    dbg_trace "{locs}"
--    let _ ← locs.flatten.mapM Meta.inspect
--    let _ ← inspect locs[0]!
--    logInfo m!"{locs}"
    sloc tac
  --Meta.inspect cmd
  elabCommand cmd

#eval show MetaM _ from do
  IO.println star
--  Meta.inspect star
  dbg_trace star

get
example {n m h : Nat} : True := by
  refine ?_
  rw [] at *
  rw [] at n n n |-
  try simp at n m h ⊢
--  simp

--inspect
--get
example {n : Nat} : True := by
  simp [] at n n n |-

variable {n : Nat} (h : n + 0 = n) in
--inspect
get
example : True := by
  simp (config := {singlePass := true}) [] at h |-

  --exact .intro

#eval 0

--"simp" (config)? (discharger)? (&" only")?
--  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)?

variable (mvs : List MVarId) in
/-- `getRealFollowers mvs tree` extracts from the `InfoTree` `tree` the array of syntax nodes
that have any one of the `MVarId`s in `mvs` as a goal on which they are "actively"
performing an action. -/
partial
def getRealFollowers : InfoTree → Array Syntax
  | .node k args =>
    let kargs := (args.map getRealFollowers).foldl (· ++ ·) #[]
    if (k.stx.getRange? true).isNone || allowedSimpFollowers.contains k.stx.getKind then kargs else
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

partial
def showTargets : InfoTree → List (List (Option Name × Name))
  | .node i c =>
    let rest := (c.toList.map showTargets).join
    if let .ofTacticInfo i := i then
      let mvs := i.goalsBefore
      let mc := i.mctxBefore
      let decls := mc.decls
      let lctxs := mvs.map decls.find?
      let lsome := lctxs.reduceOption
      let lcts := lsome.map (·.lctx)
      let fvars := lcts.map (·.getFVarIds)
      let prenms := (lcts.zip fvars).map fun (lc, a) => (a.toList.map fun b => (lc.getRoundtrippingUserName? b, b.name))
--      let nms := prenms.join
      --dbg_trace nms
      rest ++ prenms
--      match i.stx.getRange? true, non_terminal_simp? with
--        | some r, true => rest
--        | _, _ => rest
    else if let .ofFVarAliasInfo i := i then
      dbg_trace (i.userName, i.id.name, i.baseId.name)
      rest
    else rest
  | .context _ t => showTargets t
  | .hole _ => []

/-- Gets the value of the `linter.nonTerminalSimp` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.nonTerminalSimp o

--#check Parser.Term.have
--#check MessageLog.hasErrors
--#check State.messages
open Lean Term Elab Command Meta
--def stained : HashSet Name := .empty

def stained.toFVarId (lctx: LocalContext) : stained → Array FVarId
  | name n   => #[((lctx.findFromUserName? n).getD default).fvarId]
  | goal     => #[default]
  | wildcard => lctx.getFVarIds.push default

/-- `SyntaxNodeKind`s that are mostly "formatting": mostly they are ignored
because we do not want the linter to spend time on them.
The nodes that they contain will be visited by the linter anyway. -/
def ignored : HashSet Name := HashSet.empty
  |>.insert ``Lean.Parser.Tactic.tacticSeq1Indented
  |>.insert ``Lean.Parser.Tactic.tacticSeq
  |>.insert ``Lean.Parser.Term.byTactic
  |>.insert `null
  |>.insert `by
--  |>.insert ``Lean.Parser.Tactic.rwSeq
  -- even ignoring `try`, the linter still looks at the "tried" tactics
  |>.insert ``Lean.Parser.Tactic.tacticTry_
  |>.insert `«]»
  |>.insert `Std.Tactic.«tacticOn_goal-_=>_»

/-- `SyntaxNodeKind`s of tactics that stain the locations on which they act
and that can only be followed by other `stainers`. -/
def stainers : HashSet Name := HashSet.empty
  |>.insert ``Lean.Parser.Tactic.simp
--  |>.insert ``Lean.Parser.Tactic.rwSeq  -- remove me! `rw` is not a stainer!

def ctor : Info → Syntax
  | .ofTacticInfo i         => /-dbg_trace "TacticInfo"-/         i.stx
  | .ofTermInfo i           => /-dbg_trace "TermInfo"-/           i.stx
  | .ofCommandInfo i        => /-dbg_trace "CommandInfo"-/        i.stx
  | .ofMacroExpansionInfo i => /-dbg_trace "MacroExpansionInfo"-/ i.stx
  | .ofOptionInfo i         => /-dbg_trace "OptionInfo"-/         i.stx
  | .ofFieldInfo i          => /-dbg_trace "FieldInfo"-/          i.stx
  | .ofCompletionInfo i     => /-dbg_trace "CompletionInfo"-/     i.stx
  | .ofUserWidgetInfo i     => dbg_trace "UserWidgetInfo";        i.stx
  | .ofCustomInfo i         => dbg_trace "CustomInfo";            i.stx
  | .ofFVarAliasInfo _i     => dbg_trace "FVarAliasInfo";         default
  | .ofFieldRedeclInfo i    => dbg_trace "FieldRedeclInfo";       i.stx
  | .ofOmissionInfo i       => dbg_trace "OmissionInfo";          i.stx

#check getFileMap

/-
Lean.Server.combineIdents

CommandInfo
CompletionInfo
MacroExpansionInfo
TacticInfo
TermInfo
OptionInfo
-/

partial
def showFVars : InfoTree → CommandElabM Unit
  | .node i c => do
    logInfo (ctor i)
--    if let .ofFVarAliasInfo i := i then
--      dbg_trace (i.userName, i.id.name, i.baseId.name)
--      logInfo m!"{(i.userName, i.id.name, i.baseId.name)}"
    let _ ← c.toArray.mapM showFVars
  | .context _ t => showFVars t
  | .hole _ => return

open Lsp

/-- The main entry point to the unreachable tactic linter. -/
def nonTerminalSimpLinter : Linter where run := withSetOptionIn fun _stx => do
  unless getLinterHash (← getOptions) && (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then
    return
--  dbg_trace "processing"
  let trees ← getInfoTrees
--  let _ ← trees.toList.mapM showFVars
  let fm ← getFileMap
  let refs := Server.findReferences fm trees.toArray
  let mut allRefs := #[]
  for r in refs do allRefs := allRefs.push r.stx; --logInfo m!"ref stx: '{r.stx}'"
  let cRefs := Server.combineIdents trees.toArray refs
  let dRefs := Server.dedupReferences refs
--  dbg_trace "{(allRefs.size, cRefs.size, dRefs.size)}"
--  logInfo m!"{allRefs}"
--  logInfo m!"{dRefs.map fun d => ((HashMap.contains Lean.Lsp.ModuleRefs d.ident))}"
--  logInfo m!"{dRefs.map fun d => (d.stx, [d.range.start, d.range.end], d.ident.toString, d.aliases.map (·.toString))}"
--  logInfo m!"{cRefs.map fun d => (d.stx, d.ident.toString, d.aliases.map (·.toString))}"
  let x := trees.toList.map (extractRealGoalsCtx' (fun _ => true)) -- (·.getKind == ``Lean.Parser.Tactic.tacticHave_))
--  let mut stains : HashSet stained := .empty
--  let mut sfvrs : HashSet FVarId := .empty
--  let mut stains : HashSet FVarId := .empty
  let _ : Ord FVarId := ⟨fun f g => compare f.name.toString g.name.toString⟩
  let mut stains : HashMap FVarId SyntaxNodeKind := .empty
  for d in x do for (s, ctxb, ctx, mvsb, mvs) in d do
--    let newMVb := mvsb.diff mvs
--    let newMVa := mvs.diff mvsb
    if ignored.contains s.getKind then continue
--    logInfo m!"generating syntax: '{s}'"  Lean.Parser.Term.byTactic
    --logInfoAt s m!"{s} has locs: {getLocs s}"
--    for locs in getLocs s do
--    for locs in getStained! s do
--      Meta.inspect s
--    logInfoAt s m!"{s}\nstains '{getStained! s}'"
    let currMVara := mvs[0]!
    let currMVarb := mvsb[0]!
    let lctxb := ((ctxb.decls.find? currMVarb).getD default).lctx
    let lctxa := ((ctx.decls.find? currMVara).getD default).lctx
    for d in getStained! s do
      if stainers.contains s.getKind then
        let locsAfter := d.toFVarId lctxa
        for l in locsAfter do
          stains := stains.insert l s.getKind
      else
        let locsBefore := d.toFVarId lctxb
        for l in locsBefore do
          if let some kind := stains.find? l then
            Linter.logLint linter.nonTerminalSimp s m!"{kind} stained '{d}'"
--    logInfoAt s m!"{s}\nstains '{(getStained! s).map fun d =>
--      ((((d.toFVarId lctxb).map (·.name)).zip ((d.toFVarId lctxa).map (·.name))))}'"

initialize addLinter nonTerminalSimpLinter


#exit


--  let (_, map) ← (addNonSimpOnlysList trees).run {}
--  dbg_trace "processing1"
--  Meta.inspect _stx
  --let xx := trees.toList.map (extractGoals ( ``Lean.Parser.Tactic.tacticHave_))
  --for d in xx do
  --  for (s, b, a) in d do
--      logInfo m!"{s}\nbefore: {b.map (·.name)}\nafter:  {a.map (·.name)}\n"
--  let x := trees.toList.map (extractRealGoalsCtx (·.getKind == ``Lean.Parser.Tactic.tacticHave_))
  let x := trees.toList.map (extractRealGoalsCtx' (fun _ => true)) -- (·.getKind == ``Lean.Parser.Tactic.tacticHave_))
  let mut stains : HashSet stained := .empty
  let mut sfvrs : HashSet FVarId := .empty
--  let mut stains : HashSet FVarId := .empty
  let _ : Ord FVarId := ⟨fun f g => compare f.name.toString g.name.toString⟩
  for d in x do for (s, ctxb, ctx, mvsb, mvs) in d do
    let newMVb := mvsb.diff mvs
    let newMVa := mvs.diff mvsb
    if ignored.contains s.getKind then continue
--    logInfo m!"generating syntax: '{s}'"  Lean.Parser.Term.byTactic
    --logInfoAt s m!"{s} has locs: {getLocs s}"
--    for locs in getLocs s do
--    for locs in getStained! s do
--      Meta.inspect s
--      logInfoAt s m!"{s}\nstains '{locs}'"
    let declsb := (ctxb.decls.find? (newMVb.getD 0 default)).getD default
    let decls := (ctx.decls.find? (newMVa.getD 0 default)).getD default
--    liftCoreM do
--      return (← Meta.MetaM.run do
--        logInfo m!"ctx.decls: {← ctx.decls.toList.mapM fun m => do
--      return (m.1.name, match m.2.kind with | .natural => "nat" | .synthetic => "syn" | _ => "opq", ← ppExpr m.2.type)}").1
--    let declsIdxs := ctx.decls.toList.map fun m => (m.2.index)
--    let dsorted := declsIdxs.toArray.qsort (· < ·)
--    dbg_trace "index: [0,{declsIdxs.length-1}]? {dsorted == Array.range declsIdxs.length} {declsIdxs.length}\n"
    let lctx := decls.lctx
    let lctxb := declsb.lctx
    let newStained := getStained! s
    let all := if newStained.contains .wildcard then
      lctx.decls.toArray.reduceOption.map (stained.name ·.userName) else #[]
    let newStained := (newStained.erase .wildcard) ++ all
    let fvsb := newStained.map (stained.toFVarId lctxb)
    let fvsb := fvsb.flatten.sortAndDeduplicate
    let fvs := newStained.map (stained.toFVarId lctx)
    let fvs := fvs.flatten.sortAndDeduplicate
--    dbg_trace s!"syntax: {s}\n{s.getKind}\n"
    --Meta.inspect s
--    dbg_trace s!"\n---\n{s[0]} ({s.getKind})"
----    dbg_trace "already stained: {stains.toList.map (·.name)}"
--    dbg_trace "already stained: {stains.toList}"
--    dbg_trace "already sfvrsed: {sfvrs.toList.map (·.name)}"
--    dbg_trace "getStained! s: {newStained}"
--    dbg_trace "getLocs s:     {getLocs s}"
--    dbg_trace "(fvrsb, fvrs) stains:  {(fvsb.map (·.name)).zip (fvs.map (·.name))} -- {fvsb.size == fvs.size}"
--    dbg_trace "(mvsb, mvsa) stains:\nb: {newMVb.map (·.name)}\na: {newMVa.map (·.name)}"
    let unchMVs := mvsb.diff newMVb
    if unchMVs != mvs.diff newMVa then logErrorAt s "unchanged diff!"
--    dbg_trace "unchanged: {unchMVs.map (·.name)} {unchMVs == mvs.diff newMVa}"
--    dbg_trace "fvrs stains:   {fvs.map (·.name)}\n"
--    dbg_trace "goal? '{(lctxb.decls.get! 0).get!.userName}'"
    let inds := fvs.erase default
--    for v in inds do
--      dbg_trace "checking {v.name}"
--      let uname := ((lctx.find? v).getD default).userName
--      if stains.contains v then logInfoAt s m!"'{s.getKind}' acts on '{(v.name, uname)}' is stained!" else stains := stains.insert v
    for v in newStained do
      --dbg_trace "checking {v}"
      let stainer? := stainers.contains s.getKind
      if stains.contains v && !stainer? then
          return
          --logInfoAt s m!"'{s}' acts on the stained '{v}'!\n({s.getKind}) --hyps"
      else
        if stainer? then
          stains := stains.insert v
        else
          --dbg_trace "{s.getKind} does not stain '{v}'"

    for v in fvs do
      --dbg_trace "checking {v.name}"
      let stainer? := stainers.contains s.getKind
      if sfvrs.contains v && !stainer? then
          return
          --logInfoAt s m!"'{s}' acts on the stained '{v.name}'!\n({s.getKind}) --fvars"
      else
        if stainer? then
          sfvrs := sfvrs.insert v
        --else
          --dbg_trace "{s.getKind} does not stain '{v.name}'"

initialize addLinter nonTerminalSimpLinter
#exit

    logInfoAt s m!"{s}\nstains '{(getStained! s).zip (fvs.map fun ls => ls.map (·.name))}'"

--      logInfoAt s m!"in mvar {((getStained locs).map (stained.toFVarId lctx)).flatten.map fun d =>
--        (d.name)}"
--    let stains := (getLocs s).map getStained!
    let mdecls := (mvs.map ctx.findDecl?).reduceOption
    let cts := mdecls.map (·.lctx)
    let sepLdecls := cts.map (·.decls.toList |>.reduceOption)
    let ldecls := sepLdecls.join
    logInfo m!"{s}\nbefore: {mvsb.map (·.name)}\nafter:  {mvs.map (·.name)}\n"
    Command.liftCoreM do
      let _ ← Meta.MetaM.run do
--      dbg_trace "types:"
      for g in ldecls do
        let gt ← Meta.ppExpr g.type
        dbg_trace "· {gt}\n· {g.userName}\n· {g.fvarId.name}\n"
--      dbg_trace (← ldecls.mapM (Meta.ppExpr ·.toExpr))
    let fvs := cts.map (·.getFVarIds)
    let values := (ldecls.map (·.value?)).reduceOption
--    dbg_trace "values: {values.length}\nfvs: {fvs.length}"
    Command.liftCoreM do
      let _ ← Meta.MetaM.run do
      let pps ← values.mapM fun x => Meta.ppExpr x
--      logInfo m!"generated decls: '{pps}'"
/-
  let x := trees.toList.map showTargets
  let y := trees.toList.map fun o => (extractGoals ``Parser.Term.haveDecl o) --``Lean.Parser.Tactic.simp o)
  for d in y do
    for (stx, bef, aft) in d do
      dbg_trace stx
      dbg_trace "{bef.map (·.name)} -- {aft.map (·.name)}"
  for d in x do
    logInfo "d"
    for e in d do logInfo m!"{e}\n"
--  dbg_trace x
-/
  trees.forM fun tree => do
    let mut con := 0
--    dbg_trace "processing2"
    let d := extractRealGoals (fun stx => ! onlyOrNotSimp stx && (stx.getRange? true).isSome) tree --``Lean.Parser.Tactic.refine tree
--    dbg_trace "processing3 {d.map Prod.fst} {d.size}"
    for (st, aft) in d do
--      dbg_trace "* Following {st}\n"

      --for s in trees do
--      let mut tot := #[]
      for y in (getRealFollowers aft tree) do
          con := con + 1

--        tots := tots.push (y, st)
--          dbg_trace "{y.getAtomVal} follows {st.getAtomVal}"
--          logInfoAt st m!"({con})"
          Linter.logLint linter.nonTerminalSimp y m!"{y}: {y.getKind}"
--          Linter.logLint linter.nonTerminalSimp y m!"follows {st} ({con})\n{y.getKind}"
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
