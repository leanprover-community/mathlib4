/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public meta import Lean.Elab.InfoTree.Util
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep
public import Batteries.Tactic.Unreachable
public meta import Lean.Parser.Syntax
public import Mathlib.Tactic.Linter.UnusedTacticExtension

/-!
# The unused tactic linter

The unused linter makes sure that every tactic call actually changes *something*.

The inner workings of the linter are as follows.

The linter inspects the goals before and after each tactic execution.
If they are not identical, the linter is happy.
If they are identical, then the linter checks if the tactic is whitelisted.
Possible reason for whitelisting are
* tactics that emit messages, such as `extract_goal` or `says`;
* tactics that are in place to assert something, such as `guard`;
* tactics that allow to work on a specific goal, such as `on_goal`;
* "flow control" tactics, such as `success_if_fail` and related.

## Special cases

- `swap_var`: the only change that `swap_var` makes is to rename local declarations.
  Thus, to check that `swap_var` was used, we inspect the names of all the local declarations
  before and after and see if there is some change.
- `try`: the only thing `try` does is to do nothing if the inner tactic throws an error.
  So, to check that `try` was used, we check that the goals did not change.
- `<;>`/`all_goals`/`any_goals`: if there is exactly 1 goal, then these are redundant.
  If there are no goals, then these could in principle not be redundant,
  but we lint against such cases as well.
  `any_goals` can be replaced with `all_goals` when all goals were changed.

## Notable exclusions

* The linter does not enter a "sequence tactic": upon finding `tac <;> [tac1, tac2, ...]`
  the linter assumes that the tactic is doing something and does not recurse into each
  `tac1, tac2, ...`.
  This is just for lack of an implementation: it may not be hard to do this.

* The tactic does not check the discharger for `linear_combination`,
  but checks `linear_combination` itself.
  The main reason is that `skip` is a common discharger tactic and the linter would
  then always fail whenever the user explicitly chose to pass `skip` as a discharger tactic.

## TODO
* The linter seems to be silenced by `set_option ... in`: maybe it should enter `in`s?

## Implementation notes

Yet another linter copied from the `unreachableTactic` linter!
-/

meta section

open Lean Elab Std Linter

namespace Mathlib.Linter

/--
The unused tactic linter makes sure that every tactic call actually changes *something*.
It has special support for tactics `<;>`, `try`, `all_goals`, `any_goals` and `swap_var`.
-/
public register_option linter.unusedTactic : Bool := {
  defValue := true
  descr := "enable the unused tactic linter"
}

namespace UnusedTactic

-- Tactics that are expected to not change the state but should also not be flagged by the
-- unused tactic linter.
#allow_unused_tactic!
  -- the following `SyntaxNodeKind`s play a role in silencing `test`s
  Lean.Parser.Tactic.guardHyp
  Lean.Parser.Tactic.guardHypConv
  Lean.Parser.Tactic.guardTarget
  Lean.Parser.Tactic.guardTargetConv
  Lean.Parser.Tactic.failIfSuccess

/--
A list of blocklisted syntax kinds, which are expected to have subterms that contain
unused tactics.
-/
initialize ignoreTacticKindsRef : IO.Ref NameHashSet ←
  IO.mkRef <| .ofArray #[
    `Mathlib.Tactic.Says.says,
    ``Parser.Term.binderTactic,
    ``Lean.Parser.Term.dynamicQuot,
    ``Lean.Parser.Tactic.quotSeq,
    ``Lean.Parser.Tactic.tacticStop_,
    ``Lean.Parser.Command.notation,
    ``Lean.Parser.Command.mixfix,
    ``Lean.Parser.Tactic.discharger,
    ``Lean.Parser.Command.registerTryTactic,
    `Batteries.Tactic.seq_focus,
    `Mathlib.Tactic.Hint.registerHintStx,
    `Mathlib.Tactic.LinearCombination.linearCombination,
    `Aesop.Frontend.Parser.addRules,
    `Aesop.Frontend.Parser.aesopTactic,
    `Aesop.Frontend.Parser.aesopTactic?,
    ``Mathlib.Linter.UnusedTactic.«command#show_kind_»,
    -- the following `SyntaxNodeKind`s play a role in silencing `test`s
    ``Lean.Parser.Tactic.failIfSuccess,
    `Mathlib.Tactic.successIfFailWithMsg,
    `Mathlib.Tactic.failIfNoProgress
  ]

/-- Is this a syntax kind that contains intentionally unused tactic subterms? -/
public def isIgnoreTacticKind (ignoreTacticKinds : NameHashSet) (k : SyntaxNodeKind) : Bool :=
  k matches .str _ "quot" ||
  ignoreTacticKinds.contains k

/--
Adds a new syntax kind whose children will be ignored by the `unusedTactic` linter.
This should be called from an `initialize` block.
-/
public def addIgnoreTacticKind (kind : SyntaxNodeKind) : BaseIO Unit :=
  ignoreTacticKindsRef.modify (·.insert kind)

/-- Accumulates the set of all `tactic` and `conv` syntaxes.
This includes `<;>` but excludes all other tactics whose syntax is atomic, such as `;`.
-/
partial def getTactics (ignoreTacticKinds : NameHashSet)
    (tactics convs : Parser.SyntaxNodeKindSet) (stx : Syntax) :
    StateRefT (Std.HashMap Syntax.Range (Syntax × Option MessageData)) BaseIO Unit := do
  if let .node _ k args := stx then
    if !isIgnoreTacticKind ignoreTacticKinds k then
      args.forM (getTactics ignoreTacticKinds tactics convs)
    if tactics.contains k || convs.contains k then
      if let some r := stx.getRange? true then
        modify (·.insert r (stx, none))
      -- The `<;>` syntax is an atom, so to add it we special case it.
      if k == ``Lean.Parser.Tactic.«tactic_<;>_» || k == ``Lean.Parser.Tactic.Conv.«conv_<;>_» then
        if let some arg := args[1]? then
          if let some r := arg.getRange? true then
            modify (·.insert r (arg, none))

/-- `getNames mctx` extracts the names of all the local declarations implied by the
`MetavarContext` `mctx`. -/
def getNames (mctx : MetavarContext) : List Name :=
  let lcts := mctx.decls.toList.map (MetavarDecl.lctx ∘ Prod.snd)
  let locDecls := (lcts.map (PersistentArray.toList ∘ LocalContext.decls)).flatten.reduceOption
  locDecls.map LocalDecl.userName

/--
For each `TacticInfo` in the info tree that corresponds to a tactic syntax:
- If the tactic is used, erase it from the set of tactics.
- If the tactic is unused, add a message to this tactic, if it doesn't have a message already.
-/
def eraseUsedTactics (exceptions : Std.HashSet SyntaxNodeKind)
    (trees : PersistentArray InfoTree)
    (tactics convs : Parser.SyntaxNodeKindSet)
    (map : Std.HashMap Syntax.Range (Syntax × Option MessageData)) :
    Std.HashMap Syntax.Range (Syntax × Option MessageData) :=
  trees.foldl (init := map) <| InfoTree.foldInfo fun _ i ranges => Id.run do
    let .ofTacticInfo i := i | return ranges
    let stx := i.stx
    let some r := stx.getRange? true | return ranges
    let withMsg (msg : MessageData) (stx? : Option Syntax := none) :=
      ranges.modify r fun | (stx, none) => (stx?.getD stx, msg) | x => x
    match stx with
    | .atom _ "<;>" =>
      -- Bespoke check for `<;>`: if it generates at most 1 goal, we consider it unused.
      match i.goalsAfter with
      | [] => return withMsg m!"`<;>` can be removed"
      | [_] => return withMsg m!"`<;>` can be replaced with `;`"
      | _ => return ranges.erase r
    | .node _ kind _ =>
      unless tactics.contains kind || convs.contains kind do return ranges
      -- if the tactic is allowed to not change the goals
      if exceptions.contains kind then
        return ranges.erase r
      if i.goalsBefore.isEmpty then
        return withMsg m!"there are no goals left for `{stx}`"
      match kind with
      | ``Lean.Parser.Tactic.tacticTry_ =>
        -- `try` is unused if the inner tactic succeeded.
        if i.goalsAfter != i.goalsBefore then
          return withMsg "`try` can be removed" stx[0]
      | ``Lean.Parser.Tactic.allGoals =>
        -- `all_goals` is unused if it acts on 1 goal.
        if i.goalsBefore matches [_] then
          return withMsg m!"`all_goals` can be removed" stx[0]
      | ``Lean.Parser.Tactic.anyGoals =>
        -- `any_goals` is unused if it acts on 1 goal,
        -- or if the inner tactic succeeded on all goals.
        if i.goalsBefore matches [_] then
          return withMsg "`any_goals` can be removed" stx[0]
        if i.goalsAfter.all (!i.goalsBefore.contains ·) then
          return withMsg "`any_goals` can be replaced with `all_goals`" stx[0]
      | `Mathlib.Tactic.«tacticSwap_var__,,» =>
        -- `swap_var` is used if it changes the username of a free variable.
        if getNames i.mctxBefore == getNames i.mctxAfter then
          return withMsg m!"`swap_var` does not change the variable names in the goal"
      | _ =>
        -- The tactic is unused if the goals stay the same.
        if i.goalsAfter == i.goalsBefore then
          return withMsg m!"`{stx}` does not change the goal"
      return ranges.erase r
    | _ => return ranges

/-- The main entry point to the unused tactic linter. -/
def unusedTacticLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.unusedTactic (← getLinterOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return
  let env ← getEnv
  let cats := (Parser.parserExtension.getState env).categories
  -- These lookups may fail when the linter is run in a fresh, empty environment
  let some tactics := Parser.ParserCategory.kinds <$> cats.find? `tactic
    | return
  let some convs := Parser.ParserCategory.kinds <$> cats.find? `conv
    | return
  let trees ← getInfoTrees
  let exceptions := (← allowedRef.get).union <| allowedUnusedTacticExt.getState env
  let (_, map) ← (getTactics (← ignoreTacticKindsRef.get) tactics convs stx).run {}
  let map := eraseUsedTactics exceptions trees tactics convs map
  let unused := map.toArray
  let key (r : Lean.Syntax.Range) := (r.start.byteIdx, (-r.stop.byteIdx : Int))
  let mut last : Lean.Syntax.Range := ⟨0, 0⟩
  for (r, stx, msg?) in let _ := @lexOrd; let _ := @ltOfOrd.{0}; unused.qsort (key ·.1 < key ·.1) do
    if stx.getKind ∈ [``Batteries.Tactic.unreachable, ``Batteries.Tactic.unreachableConv] then
      continue
    if last.start ≤ r.start && r.stop ≤ last.stop then continue
    let msg := msg?.getD m!"`{stx}` is never executed"
    Linter.logLint linter.unusedTactic stx m!"Unused tactic linter: {msg}."
    last := r

initialize addLinter unusedTacticLinter
