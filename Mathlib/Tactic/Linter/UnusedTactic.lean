/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public meta import Lean.Elab.InfoTree.Util
public meta import Lean.Parser.Syntax
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep
public import Batteries.Tactic.Unreachable

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
  We also warn if `any_goals` can be replaced with `all_goals`, or with `on_goal n =>`.
- `t <;> [t1; t2; ...]`: each subtactic is linted individually.
  A padding `skip` (to match the number of goals) is never reported as unused.

## Notable exclusions

* The tactic does not check the discharger for `linear_combination`,
  but checks `linear_combination` itself.
  The main reason is that `skip` is a common discharger tactic and the linter would
  then always fail whenever the user explicitly chose to pass `skip` as a discharger tactic.

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

/--
`Parser`s/tactics allowed to not change the tactic state.
This can be increased dynamically, using `allow_unused_tactic` or `local allow_unused_tactic`.
-/
def initialAllowedUnusedTactics : Std.HashSet SyntaxNodeKind :=
  .ofArray #[
    `«tactic#adaptation_note_»,
    `tacticSleep_heartbeats_,
    ``Lean.Parser.Tactic.show,
    ``Lean.Parser.Tactic.Conv.skip,
    `Batteries.Tactic.«tacticOn_goal_=>_»,
    `Mathlib.Tactic.change?,
    `Mathlib.Tactic.Says.says,
    `Mathlib.Tactic.tacticMatch_target_,
    `Mathlib.Tactic.«tacticRename_bvar_→__»,
    -- the following `SyntaxNodeKind`s play a role in silencing `test`s,
    ``Lean.Parser.Tactic.guardHyp,
    ``Lean.Parser.Tactic.guardHypConv,
    ``Lean.Parser.Tactic.guardTarget,
    ``Lean.Parser.Tactic.guardTargetConv,
    ``Lean.Parser.Tactic.failIfSuccess,
    ``Lean.Parser.Tactic.traceState,
    ``Lean.Parser.Tactic.Conv.convTrace_state,
    `Mathlib.Tactic.successIfFailWithMsg,
    `Mathlib.Tactic.failIfNoProgress,
    `Mathlib.Tactic.ExtractGoal.extractGoal,
  ]

/--
Defines the `allowedUnusedTacticExt` extension for adding a `HashSet` of `allowedUnusedTactic`s
to the environment.
-/
initialize allowedUnusedTacticExt :
    SimpleScopedEnvExtension SyntaxNodeKind (Std.HashSet SyntaxNodeKind) ←
  registerSimpleScopedEnvExtension {
    initial := initialAllowedUnusedTactics
    addEntry := .insert
  }

/--
Add each identifier in `ids` (resolved as a `SyntaxNodeKind`) to the environment extension
`ext`, according to the attribute kind `attrKind` (`local ...`, `scoped ...`, or global).

If resolving an identifier fails, an error is thrown.
If an identifier denotes an imported constant, its use is recorded as indirect through `cmdName`.
-/
def addSyntaxNodeKinds (ext : SimpleScopedEnvExtension SyntaxNodeKind (Std.HashSet SyntaxNodeKind))
    (cmdName : String) (attrKind : Syntax) (ids : TSyntaxArray `ident) :
    Elab.Command.CommandElabM Unit := do
  let ids ← Command.liftCoreM do ids.mapM fun id ↦ do
    try
      realizeGlobalConstNoOverload id
    catch e =>
      throwErrorAt id m!"{e.toMessageData}\n\
        The command `#show_kind {id}` may help to find the correct `SyntaxNodeKind`."
  let attrKind ← liftMacroM <| toAttributeKind attrKind
  for id in ids do
    ext.add id attrKind
    if attrKind != .local then
      if (← getEnv).isImportedConst id then
        recordIndirectModUse cmdName id

/--
`allow_unused_tactic` takes as input a space-separated list of identifiers.
These identifiers are then allowed by the unused tactic linter:
even if these tactics do not modify goals, there will be no warning emitted.

Note: for this to work, these identifiers should be the `SyntaxNodeKind` of each tactic.

For instance, you can allow the `done` and `skip` tactics using
```lean
allow_unused_tactic Lean.Parser.Tactic.done Lean.Parser.Tactic.skip
```

This change is global and persistent across imports. For a file-local or scoped change, use
`local allow_unused_tactic` or `scoped allow_unused_tactic`, respectively.

The command `#show_kind tac` may help to find the `SyntaxNodeKind`.
-/
elab (name := allowUnusedTactic) attrKind:attrKind "allow_unused_tactic"
    ppSpace colGt ids:ident* : command =>
  addSyntaxNodeKinds allowedUnusedTacticExt "allow_unused_tactic" attrKind ids

/-- `#allow_unused_tactic` is deprecated in favour of `allow_unused_tactic` -/
syntax (name := hashStx) "#allow_unused_tactic" ("!")? ppSpace colGt ident* : command

macro_rules
| `(command| #allow_unused_tactic $ids) => `(command| local allow_unused_tactic $ids)
| `(command| #allow_unused_tactic ! $ids) => `(command| allow_unused_tactic $ids)

deprecated_syntax hashStx "use `allow_usused_tactic` instead of `#allow_unused_tactic"
  (since := "2026-08-07")

/--
`#show_kind tac` takes as input the syntax of a tactic and returns the `SyntaxNodeKind`
at the head of the tactic syntax tree.

The input syntax needs to parse, though it can be *extremely* elided.
For instance, to see the `SyntaxNodeKind` of the `refine` tactic, you could use
```lean
#show_kind refine _
```
The trailing underscore `_` makes the syntax valid, since `refine` expects something else.
-/
elab "#show_kind " stx:tactic : command =>
  logInfoAt stx m!"The `{.ofConstName ``SyntaxNodeKind}` is `{stx.raw.getKind}`."

/--
Tactics whose subterms are allowed to contain unused subtactics.
This can be increased dynamically, using `allow_unused_subtactics_inside`
-/
def initialIgnoredTacticKinds : Std.HashSet SyntaxNodeKind :=
  .ofArray #[
    `Mathlib.Tactic.Says.says,
    ``Parser.Term.binderTactic,
    ``Lean.Parser.Term.dynamicQuot,
    ``Lean.Parser.Tactic.quotSeq,
    ``Lean.Parser.Tactic.tacticStop_,
    ``Lean.Parser.Command.notation,
    ``Lean.Parser.Command.mixfix,
    ``Lean.Parser.Tactic.discharger,
    ``Lean.Parser.Command.registerTryTactic,
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

/--
Environment extension for adding a `HashSet` of ignored tactic kinds to the environment.
-/
initialize ignoredTacticKindsExt :
    SimpleScopedEnvExtension SyntaxNodeKind (Std.HashSet SyntaxNodeKind) ←
  registerSimpleScopedEnvExtension {
    initial := initialIgnoredTacticKinds
    addEntry := .insert
  }

/--
`allow_unused_subtactics_inside` takes as input a space-separated list of identifiers.
Subterms of these identifiers are then ignored by the unused tactic linter:
even if these subtactics do not modify goals, there will be no warning emitted.

Note: for this to work, these identifiers should be the `SyntaxNodeKind` of each tactic.

For instance, you can allow unused subtactics in `t <;> [t1; t2; ...]` using:
```lean
allow_unused_subtactics_inside Batteries.Tactic.seq_focus
```

This change is global and persistent across imports. For a file-local or scoped change, use
`local allow_unused_subtactics_inside` or `scoped allow_unused_subtactics_inside`, respectively.

The command `#show_kind tac` may help to find the `SyntaxNodeKind`.
-/
elab (name := allowUnusedSubtacticsInside) attrKind:attrKind "allow_unused_subtactics_inside"
    ppSpace colGt ids:ident* : command =>
  addSyntaxNodeKinds ignoredTacticKindsExt "allow_unused_subtactics_inside" attrKind ids

/-- Accumulates the set of all `tactic` and `conv` syntaxes.
This includes `<;>` but excludes all other tactics whose syntax is atomic, such as `;`.
-/
partial def getTactics (ignoredTacticKinds : Std.HashSet SyntaxNodeKind)
    (tactics convs : Parser.SyntaxNodeKindSet) (stx : Syntax) :
    StateRefT (Std.HashMap Syntax.Range (Syntax × Option MessageData)) BaseIO Unit := do
  if let .node _ k args := stx then
    if tactics.contains k || convs.contains k then
      if let some r := stx.getRange? true then
        modify (·.insert r (stx, none))
      -- The `<;>` syntax is an atom, so to add it we special case it.
      if k == ``Lean.Parser.Tactic.«tactic_<;>_» || k == ``Lean.Parser.Tactic.Conv.«conv_<;>_» then
        if let some arg := args[1]? then
          if let some r := arg.getRange? true then
            modify (·.insert r (arg, none))
    unless k matches .str _ "quot" || ignoredTacticKinds.contains k do
      -- Instead of writing `args.forM getTactics`,
      -- we separate the last `getTactics` call,
      -- so that this function uses tail recursion.
      if h : args.size ≠ 0 then
        let last := args.size - 1
        args.forM (stop := last) (getTactics ignoredTacticKinds tactics convs)
        getTactics ignoredTacticKinds tactics convs args[last]

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
        -- or if the inner tactic succeeded on all goals, or on at most one goal.
        if i.goalsBefore matches [_] then
          return withMsg "`any_goals` can be removed" stx[0]
        let touched := i.goalsBefore.filter (!i.goalsAfter.contains ·)
        if touched == i.goalsBefore then
          return withMsg "`any_goals` can be replaced with `all_goals`" stx[0]
        else if touched.isEmpty then
          return withMsg m!"`any_goals` failed on each goal" stx[0]
        else if let [goal] := touched then
          let n := i.goalsBefore.idxOf goal + 1
          return withMsg m!"`any_goals` can be replaced with `on_goal {n} =>`"
      | `Mathlib.Tactic.«tacticSwap_var__,,» =>
        -- `swap_var` is used if it changes the username of a free variable.
        if getNames i.mctxBefore == getNames i.mctxAfter then
          return withMsg m!"`swap_var` does not change the variable names in the goal"
      | `Batteries.Tactic.seq_focus =>
        -- In `t <;> [t1; t2; ...]`, lint subtactics, but ignore padding `skip`s
        let inBrackets (r': Syntax.Range) : Bool := r.start <= r'.start && r'.stop <= r.stop
        return (ranges.erase r).filter fun r' ⟨stx', _⟩ =>
          !(inBrackets r' && stx'.getKind == ``Lean.Parser.Tactic.skip)
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
  let exceptions := allowedUnusedTacticExt.getState env
  let (_, map) ← (getTactics (ignoredTacticKindsExt.getState env) tactics convs stx).run {}
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
