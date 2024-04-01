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
import Std.Lean.HashSet

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

/-- `onlyOrNotSimp stx` returns
* `false` if `stx` is syntax for `simp` *without* `only`,
* otherwise it returns `true`.
-/
def onlyOrNotSimp : Syntax → Bool
  | .node _info `Lean.Parser.Tactic.simp #[_, _, _, only?, _, _] => only?[0].getAtomVal == "only"
  | _ => true

/-
|-node Lean.Parser.Tactic.simp, none
|   |-atom original: ⟨⟩⟨ ⟩-- 'simp'
|   |-node null, none
|   |-node null, none
|   |-node null, none
|   |   |-atom original: ⟨⟩⟨\n  ⟩-- 'only'
|   |-node null, none
|   |-node null, none


|-node Lean.Parser.Tactic.simpAll, none
|   |-atom original: ⟨⟩⟨ ⟩-- 'simp_all'
|   |-node null, none
|   |-node null, none
|   |-node null, none
|   |   |-atom original: ⟨⟩⟨\n  ⟩-- 'only'
|   |-node null, none
-/

/-- `flexible? stx` is `true` on syntax that takes a "wide" variety of inputs and modifies
them in possibly unpredictable ways.

The prototypical flexible tactic is `simp`
The prototypical non-flexible tactic `rw`.  `simp only` is also non-flexible. -/
def flexible? : Syntax → Bool
  | .node _ ``Lean.Parser.Tactic.simp #[_, _, _, only?, _, _] => only?[0].getAtomVal != "only"
  | .node _ ``Lean.Parser.Tactic.simpAll #[_, _, _, only?, _] => only?[0].getAtomVal != "only"
  | _ => false

/-- `flex? tac` logs an info `true` if the tactic is flexible, logs a warning `false` otherwise. -/
elab "flex? " tac:tactic : command => do
  match flexible? tac with
    | true  => logWarningAt tac m!"{flexible? tac}"
    | false => logInfoAt tac m!"{flexible? tac}"

/-- info: false -/#guard_msgs in
flex? done
/-- info: false -/#guard_msgs in
flex? simp only
/-- info: false -/#guard_msgs in
flex? simp_all only
/-- warning: true -/#guard_msgs in
flex? simp
/-- warning: true -/#guard_msgs in
flex? simp_all

/-- info: -/ #guard_msgs in
#eval show MetaM _ from do
  let simp_all_only ← `(tactic| simp_all only)
  guard <| ! flexible? simp_all_only

  let simp_only ← `(tactic| simp only)
  guard <| ! flexible? simp_only

  let simp_all ← `(tactic| simp_all)
  guard <| flexible? simp_all

  let simp ← `(tactic| simp)
  guard <| flexible? simp


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

variable (take? : Syntax → Bool) in
-- also returns the preceding goals that change.  is there only one always?
/-- `extractRealGoalsCtx' take? tree` takes as input a function `take? : Syntax → Bool` and
an `InfoTree` and returns the array of pairs `(stx, mvars)`,
where `stx` is a syntax node such that `take? stx` is `true` and
`mvars` are the goals that have been "created" by the tactic in `stx`.

A typical usage is to find the goals following a `simp` application. -/
partial
def extractRealGoalsCtx' : InfoTree →
    Array (Syntax × MetavarContext × MetavarContext × List MVarId × List MVarId)
  | .node k args =>
    let kargs := (args.map extractRealGoalsCtx').foldl (· ++ ·) #[]
    if let Lean.Elab.Info.ofTacticInfo i := k then
      if take? i.stx && (i.stx.getRange? true).isSome then
        #[(i.stx, i.mctxBefore, i.mctxAfter, i.activeGoalsBefore, i.activeGoalsAfter)] ++ kargs
      else kargs
    else kargs
  | .context _ t => extractRealGoalsCtx' t
  | _ => default

/-- returns the array of `Syntax` that represent "locations", typically, everything that happens
in `locs` in `tac at locs`. -/
partial
def getLocs (stx : Syntax) (all? : Syntax → Bool := fun _ ↦ false) : Array Syntax :=
  match stx with
    | stx@(.node _ ``Lean.Parser.Tactic.location loc) =>
      if all? stx then #[] else loc.eraseIdx 0
    | .node _ _ args => (args.map (getLocs · all?)).flatten
    | _ => default

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

/-- info: #[h] -/ #guard_msgs in
#eval show CoreM _ from do IO.println s!"{getL (← `(tactic| cases $(⟨mkIdent `h /-`-/⟩)))}"
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

/-- Gets the value of the `linter.nonTerminalSimp` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.nonTerminalSimp o

/-- `stained.toFMVarId mv lctx st` takes a metavariable `mv`, a local context `lctx` and
a `stained` `st` and returns the array of pairs `(FVarId, mv)`s that `lctx` assigns to `st`
(the second component is always `mv`):
* if `st` "is" a `Name`, returns the singleton of the `FVarId` with the name carried by `st`,
* if `st` is `.goal`, returns the singleton `#[default]`,
* if `st` is `.wildcard`, returns the array of all the `FVarId`s in `lctx` with also `default`
  (to keep track of the `goal`).
-/
def stained.toFMVarId (mv : MVarId) (lctx: LocalContext) : stained → Array (FVarId × MVarId)
  | name n   => match lctx.findFromUserName? n with
                  | none => #[]
                  | some decl => #[(decl.fvarId, mv)]
  | goal     => #[(default, mv)]
  | wildcard => (lctx.getFVarIds.push default).map (·, mv)

/-- `SyntaxNodeKind`s that are mostly "formatting": mostly they are ignored
because we do not want the linter to spend time on them.
The nodes that they contain will be visited by the linter anyway. -/
def ignored : HashSet Name :=
  { ``Lean.Parser.Tactic.tacticSeq1Indented,
    ``Lean.Parser.Tactic.tacticSeq,
    ``Lean.Parser.Term.byTactic,
    `null,
    `by,
--    ``Lean.Parser.Tactic.rwSeq,
    -- even ignoring `try`, the linter still looks at the "tried" tactics
    ``Lean.Parser.Tactic.tacticTry_,
    `«]»,
    `Std.Tactic.«tacticOn_goal-_=>_»,
    ``Lean.Parser.Tactic.tacticSorry,
    ``Lean.Parser.Tactic.tacticRepeat_,
    ``Lean.Parser.Tactic.tacticStop_,
    ``Lean.Parser.Tactic.«tactic_<;>_»,
    `«;»,
    ``cdotTk,
    ``cdot }

/-- `SyntaxNodeKind`s that are allowed to follow a flexible tactic:
  `simp`, `simp_all`, `simp_a`, `rfl`, `omega`, `abel`, `ring`, `linarith`, `nlinarith`,
  `norm_cast`, `aesop`, `tauto`.
-/
def followers : HashSet Name :=
  { ``Lean.Parser.Tactic.simp,
    ``Lean.Parser.Tactic.simpAll,
    ``Lean.Parser.Tactic.simpa,
    ``Lean.Parser.Tactic.tacticRfl,
    ``Lean.Parser.Tactic.omega,
    `Mathlib.Tactic.Abel.abel,
    `Mathlib.Tactic.RingNF.ring,
    `linarith,
    `nlinarith,
    ``Lean.Parser.Tactic.tacticNorm_cast_,
    `Aesop.Frontend.Parser.aesopTactic,
    `Mathlib.Tactic.Tauto.tauto }

/-- `SyntaxNodeKind`s of tactics that stain the locations on which they act
and that can only be followed by other `stainers`. -/
def stainers : HashSet Name :=
  { ``Lean.Parser.Tactic.simp,
    ``Lean.Parser.Tactic.simpAll }

/-- `getIds stx` extracts the `declId` nodes from the `Syntax` `stx`.
If `stx` is an `alias` or an `export`, then it extracts an `ident`, instead of a `declId`. -/
partial
def getIds : Syntax → Array Name
  | .node _ _ args => (args.attach.map fun ⟨a, _⟩ => getIds a).flatten
  | .ident _ _ name _ => #[name]
  | _ => default

/-- `getFVarIdCandidates fv name lctx` takes an input an `FVarId`, a `Name` and a `LocalContext`.
It returns an array of guesses for a "best fit" `FVarId` in the given `LocalContext`.
The first entry of the array is the input `FVarId` `fv`, if it is present.
The next entry of the array is the `FVarId` with the given `Name `, if present.

Usually, the first entry of the returned array is "the best approximation" to `(fv, name)`. -/
def getFVarIdCandidates (fv : FVarId) (name : Name) (lctx : LocalContext) : Array FVarId :=
  #[lctx.find? fv, lctx.findFromUserName? name].reduceOption.map (·.fvarId)

def persistFVars (fv : FVarId) (before after : LocalContext) : FVarId :=
  let ldecl := (before.find? fv).getD default
  let name := ldecl.userName
  (getFVarIdCandidates fv name after).getD 0 default

def reallyPersist (fmvars : Array (FVarId × MVarId)) (mvs0 mvs1 : List MVarId) (ctx0 ctx1 : MetavarContext) :
    Array (FVarId × MVarId) := Id.run do
  -- split the input `fmvars` into
  -- * the `active` ones, whose `mvar` appears in `mvs0` and
  -- * the `inert` ones, the rest.
  -- `inert` gets copied unchanged, while we transform `active`
  let (active, inert) := fmvars.partition fun (_, mv) => mvs0.contains mv
  let mut new := #[]
  for (fvar, mvar) in active do       -- for each `active` pair `(fvar, mvar)`
    match ctx0.decls.find? mvar with  -- check if `mvar` is managed by `ctx0` (it should be)
      | none => -- the `mvar` is not managed by `ctx0`: no change
        new := new.push (fvar, mvar)
      | some mvDecl0 => -- the `mvar` *is* managed by `ctx0`: push the pair `(fvar, mvar)` through
        for mv1 in mvs1 do  -- for each new `MVarId` in `mvs1`
          match ctx1.decls.find? mv1 with  -- check if `mv1` is managed by `ctx1` (it should be)
            | none => dbg_trace "'really_persist' coud this happen?" default -- ??? maybe `.push`?
            | some mvDecl1 =>  -- we found a "new" declaration
              let persisted_fv := persistFVars fvar mvDecl0.lctx mvDecl1.lctx  -- persist `fv`
              new := new.push (persisted_fv, mv1)
/-
    for lc0 in lctx0 do    -- for each "before" `LocalContext`
      for lc1 in lctx1 do  -- for each "after"  `LocalContext`
        let persisted_fv := persistFVars fv lc0 lc1  -- persist `fv`
        for mv1 in mvs1 do
          new := new.push (persisted_fv, mv1)
-/
  return inert ++ new

/-
universe u v in
instance {A : Type u} {B : Type v} [Hashable A] [Hashable B] : Hashable (A ⊕ B) where
  hash ab := by cases ab with
    | inl a => sorry
    | inr b => sorry
-/

/-- The main entry point to the unreachable tactic linter. -/
def nonTerminalSimpLinter : Linter where run := withSetOptionIn fun _stx => do
  unless getLinterHash (← getOptions) && (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  let trees ← getInfoTrees
  let x := trees.toList.map (extractRealGoalsCtx' (fun _ => true))
--  let _ : Ord FVarId := ⟨fun f g => compare f.name.toString g.name.toString⟩
  -- `stains` records pairs `(location, mvar)`, where
  -- * `location` is either a hypothesis or the main goal modified by a flexible tactic and
  -- * `mvar` is the metavariable containing the modified location
  let mut stains : HashMap (FVarId × MVarId) (stained × SyntaxNodeKind) := .empty
  let mut msgs : Array (Syntax × SyntaxNodeKind × stained) := #[]
  for d in x do for (s, ctx0, ctx1, mvs0, mvs1) in d do
--    if ! ignored.contains s.getKind then
--      logInfoAt s[0] m!"{mvs0.map (·.name)} ⊆ -- '{s}'\n{mvs1.map (·.name)}"
--    logInfoAt s m!"{stains.toArray.map fun ((fv, mv), xx) => ((fv.name, mv.name), xx)}"

    --nowlogInfoAt s m!"stains before:\n* {stains.toArray.map fun (a, b, c) => ((a.1.name, a.2.name), b, c)}"
    --nowlet persisted := reallyPersist (stains.toArray.map Prod.fst) mvs0 mvs1 ctx0 ctx1
    --nowlogInfoAt s m!"pers {persisted.map fun (fv, mv) => (fv.name, mv.name)}"
    let skind := s.getKind
    if ignored.contains skind then /-dbg_trace "ignoring {skind}"-/ continue
--    logInfoAt s m!"acting on: {getStained! s}"
    for d in getStained! s do
--      logInfoAt s m!"(flex, solves?) = {(flexible? s, (mvs1.length < mvs0.length : Bool))}"
      let shouldStain? := flexible? s && mvs1.length == mvs0.length
/-
      logInfoAt s m!"new shouldStain? '{shouldStain?}'"
      let shouldStain? :=
        match stainers.contains skind, onlyOrNotSimp s, skind, (! mvs1.length < mvs0.length) with
        | false, _, _, _ => false -- not a stainer
        | _, tf, ``Lean.Parser.Tactic.simp, _ =>
          /-dbg_trace "{s}`simp *not* only`";-/ !tf -- `simp *not* only`
--        | true, true, ``Lean.Parser.Tactic.simp, solves? => solves?
            -- if `simp *not* only` check if it closes a goal
        | true, true, ``Lean.Parser.Tactic.simpAll, _ => true -- `simp_all`
        | true, _, _, _ => true
--      logInfoAt s m!"{shouldStain?}"
-/
--unused?      let lctx0 := (mvs0.map ctx0.decls.find?).reduceOption.map (·.lctx)
--unused?      let lctx1 := (mvs1.map ctx1.decls.find?).reduceOption.map (·.lctx)
--unused?      for lc0 in lctx0 do
--unused?        let fvars := stains.toArray.map Prod.fst
--unused?        for lc1 in lctx1 do for fv in fvars do
--unused?          let cand_fv := persistFVars fv.1 lc0 lc1
--unused?          let olds := stains.toArray.filter fun (a, _) => a == fv
--unused?          for (_, stnd, k) in olds do
--unused?            stains := stains.insert (cand_fv, default) (stnd, k)
          --nowlogInfoAt s m!"candidate: {(fv.1.name, fv.2.name)} --> {cand_fv.name}"
        --nowlet ldecls := fvars.map fun (d, _) => (lc0.get! d|>.userName, d.name)
        --nowlogInfoAt s m!"ldecls before '{s}' (username, fvarid):\n{ldecls}"
      --nowfor lctx in lctx1 do
        --nowlet fvars := lctx.getFVarIds
        --nowlet ldecls := fvars.map fun d => (lctx.get! d|>.userName, d.name)
        --nowlogInfoAt s m!"ldecls after '{s}' (username, fvarid):\n{ldecls}"


/-
      let found_stained := stained_in_syntax.filter (·.toFVarId lctx0 != default)
      let stained_in_syntax := stained_in_syntax.filter
      logInfo m!"'{s}'\n* stained_in_syntax: {stained_in_syntax}\n* found_fvs: \
        {found_fvs.map fun d => (((lctx0.fvarIdToDecl.find? d).getD default).userName, d.name)}"
      logInfo m!"'{s}' has ids: {stained_in_syntax}\n  found: \
        {(found_stained).map fun d =>
          (((lctx0.fvarIdToDecl.find? (d.toFVarId lctx0)).getD default).userName, d.name)}"

      logInfo m!"'{s}' has ids: {stained_in_syntax}\n  stained: \
        {(stained_in_syntax.map (·.toFVarId lctx0)).flatten.map fun d =>
          (((lctx0.fvarIdToDecl.find? d).getD default).userName, d.name)}"
-/
      if shouldStain? then
--        logInfoAt s "inside shouldStain?"
        --if followers.contains skind then continue
--      if stainers.contains skind &&
--        !onlyOrNotSimp s &&
--        (! mvs1.length < mvs0.length) then
        for currMVar1 in mvs1 do--.getD 0 default
          let lctx1 := ((ctx1.decls.find? currMVar1).getD default).lctx
          let locsAfter := d.toFMVarId currMVar1 lctx1

          for l in locsAfter do
--            logInfoAt s --trace[flexible]
--              m!"{s} is staining {(((lctx1.fvarIdToDecl.find? l).getD default).userName, l.name)}\
--                ({l == default}, {currMVar1.name})"
            stains := stains.insert l (d, skind)
            --nowlogInfoAt s m!"inserting {((l.1.name, l.2.name), d, skind)}"

      else
        --let stained_in_syntax := getL s
        --logInfoAt s m!"stained_in_syntax: {stained_in_syntax}"
        if !followers.contains skind then
          for currMVar0 in mvs0 do --.getD 0 default
            let lctx0 := ((ctx0.decls.find? currMVar0).getD default).lctx
            --let foundFvs := (stained_in_syntax.map (·.toFMVarId currMVar0 lctx0)).flatten --.filter (· != default)
            -- we collect all the references to potential locations:
            -- * in `at`-clauses via `d.toFVarId`, e.g. the `h` in `rw at h`;
            -- * inside the syntax of the tactic `d`, e.g. the `h` in `rw [h]`.
            --logInfoAt s m!"foundFvs.names: {foundFvs.map fun (a, b) => (a.name, b.name)}"
            let locsBefore := d.toFMVarId currMVar0 lctx0 --++ foundFvs
            for l in locsBefore do
              if let some (stdLoc, kind) := stains.find? l then
                msgs := msgs.push (s, kind, stdLoc)
--                Linter.logLint linter.nonTerminalSimp s m!"{kind} stained '{d}' at '{s}'"

        -- tactics often change the name of the current `MVarId`, so we migrate the `FvarId`s
        -- in the "old" `mvars` to the "same" `FVarId` in the "new" `mvars`
      --nowlet persisted := reallyPersist (stains.toArray.map Prod.fst) mvs0 mvs1 ctx0 ctx1
      --nowlogInfoAt s m!"pers2 {stains.toArray.map fun ((fv, mv), _) =>
      --now  (fv.name, mv.name)} {persisted.map fun (fv, mv) => (fv.name, mv.name)}"


      let mut new : HashMap (FVarId × MVarId) (stained × SyntaxNodeKind) := .empty
      for (fv, (stLoc, kd)) in stains.toArray do
        let psisted := reallyPersist #[fv] mvs0 mvs1 ctx0 ctx1
        if psisted == #[] && mvs1 != [] then
          new := new.insert fv (stLoc, kd)
          dbg_trace "lost {((fv.1.name, fv.2.name), stLoc, kd)}"
        for p in psisted do new := new.insert p (stLoc, kd)
      stains := new

    --nowlogInfoAt s m!"stains after:\n* {stains.toArray.map fun (a, b, c) => ((a.1.name, a.2.name), b, c)}"
  for (s, kind, d) in msgs do
    Linter.logLint linter.nonTerminalSimp s m!"{kind} stained '{d}' at '{s}'"



initialize addLinter nonTerminalSimpLinter
