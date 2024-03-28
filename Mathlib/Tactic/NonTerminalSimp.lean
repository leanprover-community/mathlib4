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
def extractRealGoalsCtx' : InfoTree → Array (Syntax × MetavarContext × MetavarContext × List MVarId × List MVarId)
  | .node k args =>
    let kargs := (args.map extractRealGoalsCtx').foldl (· ++ ·) #[]
    if let Lean.Elab.Info.ofTacticInfo i := k then
      if take? i.stx && (i.stx.getRange? true).isSome then
        #[(i.stx, i.mctxBefore, i.mctxAfter, i.activeGoalsBefore, i.activeGoalsAfter)] ++ kargs else kargs
    else kargs
  | .context _ t => extractRealGoalsCtx' t
  | _ => default

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

open Lean Term Elab Command Meta

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

/-- The main entry point to the unreachable tactic linter. -/
def nonTerminalSimpLinter : Linter where run := withSetOptionIn fun _stx => do
  unless getLinterHash (← getOptions) && (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  let trees ← getInfoTrees
  let x := trees.toList.map (extractRealGoalsCtx' (fun _ => true))
  let _ : Ord FVarId := ⟨fun f g => compare f.name.toString g.name.toString⟩
  let mut stains : HashMap FVarId SyntaxNodeKind := .empty
  for d in x do for (s, ctxb, ctx, mvsb, mvs) in d do
    if ignored.contains s.getKind then continue
    let currMVara := mvs.getD 0 default
    let currMVarb := mvsb.getD 0 default
    let lctxb := ((ctxb.decls.find? currMVarb).getD default).lctx
    let lctxa := ((ctx.decls.find? currMVara).getD default).lctx
    for d in getStained! s do
      if stainers.contains s.getKind &&
        !onlyOrNotSimp s &&
        (! mvs.length < mvsb.length) then
        let locsAfter := d.toFVarId lctxa
        for l in locsAfter do
          stains := stains.insert l s.getKind
      else
        let locsBefore := d.toFVarId lctxb
        for l in locsBefore do
          if let some kind := stains.find? l then
            Linter.logLint linter.nonTerminalSimp s m!"{kind} stained '{d}'"

initialize addLinter nonTerminalSimpLinter
