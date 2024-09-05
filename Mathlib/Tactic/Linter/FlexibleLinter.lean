/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Lean.Linter.Util
import Batteries.Data.Array.Basic
import Batteries.Lean.HashSet

/-!
#  The "flexible" linter

The "flexible" linter makes sure that a "rigid" tactic (such as `rw`) does not act on the
output of a "flexible" tactic (such as `simp`).

For example, this ensures that, if you want to use `simp [...]` in the middle of a proof,
then you should replace `simp [...]` by one of
* a `suffices \"expr after simp\" by simpa` line;
* the output of `simp? [...]`, so that the final code contains `simp only [...]`;
* something else that does not involve `simp`!

Otherwise, the linter will complain.

## TODO
The example
```lean
example (h : 0 = 0) : True := by
  simp at h
  assumption
```
should trigger the linter, since `assumption` uses `h` that has been "stained" by `simp at h`.
However, `assumption` contains no syntax information for the location `h`, so the linter in its
current form does not catch this.

## Implementation notes

A large part of the code is devoted to tracking `FVar`s and `MVar`s between tactics.

For the `FVar`s, this follows the following heuristic:
* if the unique name of the `FVar` is preserved, then we use that;
* otherwise, if the `userName` of the `FVar` is preserved, then we use that;
* if neither is preserved, we drop the ball and stop tracking the `FVarId`.

For the `MVar`s, we use the information of `Lean.Elab.TacticInfo.goalsBefore` and
`Lean.Elab.TacticInfo.goalsAfter`.
By looking at the `mvar`s that are either only "before" or only "after", we focus on the
"active" goals.
We then propagate all the `FVarId`s that were present in the "before" goals to the "after" goals,
while leaving untouched the ones in the "inert" goals.
-/

open Lean Elab

namespace Mathlib.Linter

/-- The flexible linter makes sure that "rigid" tactics do not follow "flexible" tactics. -/
register_option linter.flexible : Bool := {
  defValue := false
  descr := "enable the flexible linter"
}

/-- `flexible? stx` is `true` if `stx` is syntax for a tactic that takes a "wide" variety of
inputs and modifies them in possibly unpredictable ways.

The prototypical flexible tactic is `simp`.
The prototypical non-flexible tactic `rw`.
`simp only` is also non-flexible. -/
--  TODO: adding more entries here, allows to consider more tactics to be flexible
def flexible? : Syntax → Bool
  | .node _ ``Lean.Parser.Tactic.simp #[_, _, _, only?, _, _] => only?[0].getAtomVal != "only"
  | .node _ ``Lean.Parser.Tactic.simpAll #[_, _, _, only?, _] => only?[0].getAtomVal != "only"
  | _ => false

end Mathlib.Linter

section goals_heuristic
namespace Lean.Elab.TacticInfo

/-!
###  Heuristics for determining active and inactive goals

The two definitions `activeGoalsBefore`, `activeGoalsAfter` extract a list of
`MVarId`s attempting to determine which on which goals the tactic `t` is acting.
This is mostly based on the heuristic that the tactic will "change" an `MVarId`.
-/

/-- `activeGoalsBefore t` are the `MVarId`s before the `TacticInfo` `t` that "disappear" after it.
They should correspond to the goals in which the tactic `t` performs some action. -/
def activeGoalsBefore (t : TacticInfo) : List MVarId :=
  t.goalsBefore.filter (·.name ∉ t.goalsAfter.map (·.name))

/-- `activeGoalsAfter t` are the `MVarId`s after the `TacticInfo` `t` that were not present before.
They should correspond to the goals created or changed by the tactic `t`. -/
def activeGoalsAfter (t : TacticInfo) : List MVarId :=
  t.goalsAfter.filter (·.name ∉ t.goalsBefore.map (·.name))

end Lean.Elab.TacticInfo
end goals_heuristic

namespace Mathlib.Linter.Flexible

variable (take? : Syntax → Bool) in
/-- `extractCtxAndGoals take? tree` takes as input a function `take? : Syntax → Bool` and
an `InfoTree` and returns the array of pairs `(stx, mvars)`,
where `stx` is a syntax node such that `take? stx` is `true` and
`mvars` indicates the goal state:
 * the context before `stx`
 * the context after `stx`
 * a list of metavariables closed by `stx`
 * a list of metavariables created by `stx`

A typical usage is to find the goals following a `simp` application.
-/
partial
def extractCtxAndGoals : InfoTree →
    Array (Syntax × MetavarContext × MetavarContext × List MVarId × List MVarId)
  | .node k args =>
    let kargs := (args.map extractCtxAndGoals).foldl (· ++ ·) #[]
    if let .ofTacticInfo i := k then
      if take? i.stx && (i.stx.getRange? true).isSome then
        #[(i.stx, i.mctxBefore, i.mctxAfter, i.activeGoalsBefore, i.activeGoalsAfter)] ++ kargs
      else kargs
    else kargs
  | .context _ t => extractCtxAndGoals t
  | _ => default

/-- `Stained` is the type of the stained locations: it can be
* a `Name` (typically of associated to the `FVarId` of a local declaration);
* the goal (`⊢`);
* the "wildcard" -- all the declaration in context (`*`).
-/
inductive Stained
  | name     : Name → Stained
  | goal     : Stained
  | wildcard : Stained
  deriving Repr, Inhabited, DecidableEq, Hashable

/-- Converting a `Stained` to a `String`:
* a `Name` is represented by the corresponding string;
* `goal` is represented by `⊢`;
* `wildcard` is represented by `*`.
-/
instance : ToString Stained where
  toString | .name n => n.toString | .goal => "⊢" | .wildcard => "*"

/--
`toStained stx` scans the input `Syntax` `stx` extracting identifiers and atoms, making an effort
to convert them to `Stained`.
The function is used to extract "location" information about `stx`: either explicit locations as in
`rw [] at locations` or implicit ones as `rw [h]`.

Whether or not what this function extracts really is a location will be determined by the linter
using data embedded in the `InfoTree`s. -/
partial
def toStained : Syntax → HashSet Stained
  | .node _ _ arg => (arg.map toStained).foldl (·.merge ·) {}
  | .ident _ _ val _ => {.name val}
  | .atom _ val => match val with
                  | "*" => {.wildcard}
                  | "⊢" => {.goal}
                  | "|" => {.goal}
                  | _ => {}
  | _ => {}

/-- `getStained stx` expects `stx` to be an argument of a node of `SyntaxNodeKind`
`Lean.Parser.Tactic.location`.
Typically, we apply `getStained` to the output of `getLocs`.

See `getStained!` for a similar function. -/
partial
def getStained (stx : Syntax) (all? : Syntax → Bool := fun _ ↦ false) : HashSet Stained :=
  match stx with
    | stx@(.node _ ``Lean.Parser.Tactic.location loc) =>
      if all? stx then {} else (loc.map toStained).foldl (·.merge ·) {}
    | .node _ _ args => (args.map (getStained · all?)).foldl (·.merge ·) {}
    | _ => default

/-- `getStained! stx` expects `stx` to be an argument of a node of `SyntaxNodeKind`
`Lean.Parser.Tactic.location`.
Typically, we apply `getStained!` to the output of `getLocs`.

It returns the `HashSet` of `Stained` determined by the locations in `stx`.

The only difference with `getStained stx`, is that `getStained!` never returns `{}`:
if `getStained stx = {}`, then `getStained' stx = {.goal}`.

This means that tactics that do not have an explicit "`at`" in their syntax will be treated as
acting on the main goal. -/
def getStained! (stx : Syntax) (all? : Syntax → Bool := fun _ ↦ false) : HashSet Stained :=
  let out := getStained stx all?
  if out.size == 0 then {.goal} else out

/-- `Stained.toFMVarId mv lctx st` takes a metavariable `mv`, a local context `lctx` and
a `Stained` `st` and returns the array of pairs `(FVarId, mv)`s that `lctx` assigns to `st`
(the second component is always `mv`):
* if `st` "is" a `Name`, returns the singleton of the `FVarId` with the name carried by `st`;
* if `st` is `.goal`, returns the singleton `#[default]`;
* if `st` is `.wildcard`, returns the array of all the `FVarId`s in `lctx` with also `default`
  (to keep track of the `goal`).
-/
def Stained.toFMVarId (mv : MVarId) (lctx: LocalContext) : Stained → Array (FVarId × MVarId)
  | name n   => match lctx.findFromUserName? n with
                  | none => #[]
                  | some decl => #[(decl.fvarId, mv)]
  | goal     => #[(default, mv)]
  | wildcard => (lctx.getFVarIds.push default).map (·, mv)

/-- `SyntaxNodeKind`s that are mostly "formatting": mostly they are ignored
because we do not want the linter to spend time on them.
The nodes that they contain will be visited by the linter anyway. -/
def combinatorLike : HashSet Name :=
  { -- "continuators": these typically wrap other tactics inside them.
    -- The linter ignores the wrapper, but does recurse into the enclosed tactics
    ``Lean.Parser.Tactic.tacticSeq1Indented,
    ``Lean.Parser.Tactic.tacticSeq,
    ``Lean.Parser.Term.byTactic,
    `by,
    ``Lean.Parser.Tactic.tacticTry_,
    `choice,  -- involved in `first`
    ``Lean.Parser.Tactic.allGoals,
    `Std.Tactic.«tacticOn_goal-_=>_»,
    ``Lean.Parser.Tactic.«tactic_<;>_»,
    ``cdotTk,
    ``cdot,
    -- "stopper tactics": their effect is analogous to "continuators", but they do not wrap
    -- other tactics inside them.  Some are "finishing" tactics, so there really is nothing beyond
    -- them in their branch of the InfoTree.
    ``Lean.Parser.Tactic.tacticSorry,
    ``Lean.Parser.Tactic.tacticRepeat_,
    ``Lean.Parser.Tactic.tacticStop_,
    `Mathlib.Tactic.Abel.abelNF,
    `Mathlib.Tactic.RingNF.ringNF }

/-- `SyntaxNodeKind`s that are allowed to follow a flexible tactic:
  `simp`, `simp_all`, `simpa`, `dsimp`, `constructor`, `congr`, `done`, `rfl`, `omega`, `abel`,
  `ring`, `linarith`, `nlinarith`, `norm_cast`, `aesop`, `tauto`, `fun_prop`, `split`, `split_ifs`.
-/
def followers : HashSet Name :=
  { ``Lean.Parser.Tactic.simp,
    ``Lean.Parser.Tactic.simpAll,
    ``Lean.Parser.Tactic.simpa,
    ``Lean.Parser.Tactic.dsimp,
    ``Lean.Parser.Tactic.constructor,
    ``Lean.Parser.Tactic.congr,
    ``Lean.Parser.Tactic.done,
    ``Lean.Parser.Tactic.tacticRfl,
    ``Lean.Parser.Tactic.omega,
    `Mathlib.Tactic.Abel.abel,
    `Mathlib.Tactic.RingNF.ring,
    `Mathlib.Tactic.normNum,
    `linarith,
    `nlinarith,
    ``Lean.Parser.Tactic.tacticNorm_cast_,
    `Aesop.Frontend.Parser.aesopTactic,
    `Mathlib.Tactic.Tauto.tauto,
    `Mathlib.Meta.FunProp.funPropTacStx,
    `Lean.Parser.Tactic.split,
    `Mathlib.Tactic.splitIfs }

/-- By default, if a `SyntaxNodeKind` is not special-cased here, then the linter assumes that
the tactic will use the goal as well: this heuristic works well with `exact`, `refine`, `apply`.
For tactics such as `cases` this is not true: for these tactics, `usesGoal?` yields `false. -/
def usesGoal? : SyntaxNodeKind → Bool
  | ``Lean.Parser.Tactic.cases => false
  | `Mathlib.Tactic.cases' => false
  | ``Lean.Parser.Tactic.obtain => false
  | ``Lean.Parser.Tactic.tacticHave_ => false
  | ``Lean.Parser.Tactic.rcases => false
  | ``Lean.Parser.Tactic.specialize => false
  | ``Lean.Parser.Tactic.subst => false
  | ``«tacticBy_cases_:_» => false
  | ``Lean.Parser.Tactic.induction => false
  | _ => true

/-- `getFVarIdCandidates fv name lctx` takes an input an `FVarId`, a `Name` and a `LocalContext`.
It returns an array of guesses for a "best fit" `FVarId` in the given `LocalContext`.
The first entry of the array is the input `FVarId` `fv`, if it is present.
The next entry of the array is the `FVarId` with the given `Name`, if present.

Usually, the first entry of the returned array is "the best approximation" to `(fv, name)`. -/
def getFVarIdCandidates (fv : FVarId) (name : Name) (lctx : LocalContext) : Array FVarId :=
  #[lctx.find? fv, lctx.findFromUserName? name].reduceOption.map (·.fvarId)

/-!
Tactics often change the name of the current `MVarId`, as well as the names of the `FVarId`s
appearing in their local contexts.
The function `reallyPersist` makes an attempt at "tracking" pairs `(fvar, mvar)` across a
simultaneous change represented by an "old" list of `MVarId`s and the corresponding
`MetavarContext` and a new one.

This arises in the context of the information encoded in the `InfoTree`s when processing a
tactic proof.
-/

/-- `persistFVars` is one step in persisting: track a single `FVarId` between two `LocalContext`s.
If an `FVarId` with the same unique name exists in the new context, use it.
Otherwise, if an `FVarId` with the same `userName` exists in the new context, use it.
If both of these fail, return `default` (i.e. "fail"). -/
def persistFVars (fv : FVarId) (before after : LocalContext) : FVarId :=
  let ldecl := (before.find? fv).getD default
  let name := ldecl.userName
  (getFVarIdCandidates fv name after).getD 0 default

/-- `reallyPersist` converts an array of pairs `(fvar, mvar)` to another array of the same type. -/
def reallyPersist
    (fmvars : Array (FVarId × MVarId)) (mvs0 mvs1 : List MVarId) (ctx0 ctx1 : MetavarContext) :
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
  return inert ++ new

/-- The main implementation of the flexible linter. -/
def flexibleLinter : Linter where run := withSetOptionIn fun _stx => do
  unless Linter.getLinterValue linter.flexible (← getOptions) && (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  let trees ← getInfoTrees
  let x := trees.toList.map (extractCtxAndGoals (fun _ => true))
  -- `stains` records pairs `(location, mvar)`, where
  -- * `location` is either a hypothesis or the main goal modified by a flexible tactic and
  -- * `mvar` is the metavariable containing the modified location
  let mut stains : Array ((FVarId × MVarId) × (Stained × Syntax)) := .empty
  let mut msgs : Array (Syntax × Syntax × Stained) := #[]
  for d in x do for (s, ctx0, ctx1, mvs0, mvs1) in d do
    let skind := s.getKind
    if combinatorLike.contains skind then continue
    let shouldStain? := flexible? s && mvs1.length == mvs0.length
    for d in getStained! s do
      if shouldStain? then
        for currMVar1 in mvs1 do
          let lctx1 := ((ctx1.decls.find? currMVar1).getD default).lctx
          let locsAfter := d.toFMVarId currMVar1 lctx1

          for l in locsAfter do
            stains := stains.push (l, (d, s))

      else
        let stained_in_syntax := if usesGoal? skind then (toStained s).insert d else toStained s
        if !followers.contains skind then
          for currMv0 in mvs0 do
            let lctx0 := ((ctx0.decls.find? currMv0).getD default).lctx
            let mut foundFvs : HashSet (FVarId × MVarId):= {}
            for st in stained_in_syntax do
              for d in st.toFMVarId currMv0 lctx0 do
                if !foundFvs.contains d then foundFvs := foundFvs.insert d
            for l in foundFvs do
              if let some (_stdLoc, (st, kind)) := stains.find? (Prod.fst · == l) then
                msgs := msgs.push (s, kind, st)

      -- tactics often change the name of the current `MVarId`, so we migrate the `FvarId`s
      -- in the "old" `mvars` to the "same" `FVarId` in the "new" `mvars`
      let mut new : Array ((FVarId × MVarId) × (Stained × Syntax)) := .empty
      for (fv, (stLoc, kd)) in stains do
        let psisted := reallyPersist #[fv] mvs0 mvs1 ctx0 ctx1
        if psisted == #[] && mvs1 != [] then
          new := new.push (fv, (stLoc, kd))
          dbg_trace "lost {((fv.1.name, fv.2.name), stLoc, kd)}"
        for p in psisted do new := new.push (p, (stLoc, kd))
      stains := new

  for (s, stainStx, d) in msgs do
    Linter.logLint linter.flexible stainStx m!"'{stainStx}' is a flexible tactic modifying '{d}'…"
    logInfoAt s m!"… and '{s}' uses '{d}'!"

initialize addLinter flexibleLinter

end Mathlib.Linter.Flexible
