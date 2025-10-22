/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Parser.Syntax
import Batteries.Tactic.Unreachable
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header
import Mathlib.Tactic.Linter.UnusedTacticExtension

/-!
# The unused tactic linter

The unused linter makes sure that every tactic call actually changes *something*.

The inner workings of the linter are as follows.

The linter inspects the goals before and after each tactic execution.
If they are not identical, the linter is happy.
If they are identical, then the linter checks if the tactic is whitelisted.
Possible reason for whitelisting are
* tactics that emit messages, such as `have?`, `extract_goal`, or `says`;
* tactics that are in place to assert something, such as `guard`;
* tactics that allow to work on a specific goal, such as `on_goal`;
* "flow control" tactics, such as `success_if_fail` and related.

The only tactic that has a bespoke criterion is `swap_var`: the reason is that the only change that
`swap_var` has is to relabel the usernames of local declarations.
Thus, to check that `swap_var` was used, so we inspect the names of all the local declarations
before and after and see if there is some change.

## Notable exclusions

* `conv` is completely ignored by the linter.

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

open Lean Elab Std Linter

namespace Mathlib.Linter

/-- The unused tactic linter makes sure that every tactic call actually changes *something*. -/
register_option linter.unusedTactic : Bool := {
  defValue := true
  descr := "enable the unused tactic linter"
}

namespace UnusedTactic

/-- The monad for collecting the ranges of the syntaxes that do not modify any goal. -/
abbrev M := StateRefT (Std.HashMap String.Range Syntax) IO

-- Tactics that are expected to not change the state but should also not be flagged by the
-- unused tactic linter.
#allow_unused_tactic!
  Lean.Parser.Term.byTactic
  Lean.Parser.Tactic.tacticSeq
  Lean.Parser.Tactic.tacticSeq1Indented
  Lean.Parser.Tactic.tacticTry_
  -- the following `SyntaxNodeKind`s play a role in silencing `test`s
  Lean.Parser.Tactic.guardHyp
  Lean.Parser.Tactic.guardTarget
  Lean.Parser.Tactic.failIfSuccess

/--
A list of blacklisted syntax kinds, which are expected to have subterms that contain
unevaluated tactics.
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
    ``Lean.Parser.Tactic.Conv.conv,
    `Batteries.Tactic.seq_focus,
    `Mathlib.Tactic.Hint.registerHintStx,
    `Mathlib.Tactic.LinearCombination.linearCombination,
    `Mathlib.Tactic.LinearCombination'.linearCombination',
    `Aesop.Frontend.Parser.addRules,
    `Aesop.Frontend.Parser.aesopTactic,
    `Aesop.Frontend.Parser.aesopTactic?,
    -- the following `SyntaxNodeKind`s play a role in silencing `test`s
    ``Lean.Parser.Tactic.failIfSuccess,
    `Mathlib.Tactic.successIfFailWithMsg,
    `Mathlib.Tactic.failIfNoProgress
  ]

/-- Is this a syntax kind that contains intentionally unused tactic subterms? -/
def isIgnoreTacticKind (ignoreTacticKinds : NameHashSet) (k : SyntaxNodeKind) : Bool :=
  k.components.contains `Conv ||
  "slice".isPrefixOf k.toString ||
  k matches .str _ "quot" ||
  ignoreTacticKinds.contains k

/--
Adds a new syntax kind whose children will be ignored by the `unusedTactic` linter.
This should be called from an `initialize` block.
-/
def addIgnoreTacticKind (kind : SyntaxNodeKind) : IO Unit :=
  ignoreTacticKindsRef.modify (·.insert kind)

variable (ignoreTacticKinds : NameHashSet) (isTacKind : SyntaxNodeKind → Bool) in
/-- Accumulates the set of tactic syntaxes that should be evaluated at least once. -/
@[specialize] partial def getTactics (stx : Syntax) : M Unit := do
  if let .node _ k args := stx then
    if !isIgnoreTacticKind ignoreTacticKinds k then
      args.forM getTactics
    if isTacKind k then
      if let some r := stx.getRange? true then
        modify fun m => m.insert r stx

/-- `getNames mctx` extracts the names of all the local declarations implied by the
`MetavarContext` `mctx`. -/
def getNames (mctx : MetavarContext) : List Name :=
  let lcts := mctx.decls.toList.map (MetavarDecl.lctx ∘ Prod.snd)
  let locDecls := (lcts.map (PersistentArray.toList ∘ LocalContext.decls)).flatten.reduceOption
  locDecls.map LocalDecl.userName

mutual
/-- Search for tactic executions in the info tree and remove the syntax of the tactics that
changed something. -/
partial def eraseUsedTacticsList (exceptions : Std.HashSet SyntaxNodeKind)
    (trees : PersistentArray InfoTree) : M Unit :=
  trees.forM (eraseUsedTactics exceptions)

/-- Search for tactic executions in the info tree and remove the syntax of the tactics that
changed something. -/
partial def eraseUsedTactics (exceptions : Std.HashSet SyntaxNodeKind) : InfoTree → M Unit
  | .node i c => do
    if let .ofTacticInfo i := i then
      let stx := i.stx
      let kind := stx.getKind
      if let some r := stx.getRange? true then
        if exceptions.contains kind
        -- if the tactic is allowed to not change the goals
        then modify (·.erase r)
        else
        -- if the goals have changed
        if i.goalsAfter != i.goalsBefore
        then modify (·.erase r)
        -- bespoke check for `swap_var`: the only change that it does is
        -- in the usernames of local declarations, so we check the names before and after
        else
        if (kind == `Mathlib.Tactic.«tacticSwap_var__,,») &&
                (getNames i.mctxBefore != getNames i.mctxAfter)
        then modify (·.erase r)
    eraseUsedTacticsList exceptions c
  | .context _ t => eraseUsedTactics exceptions t
  | .hole _ => pure ()

end

/-- The main entry point to the unused tactic linter. -/
def unusedTacticLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.unusedTactic (← getLinterOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return
  if stx.isOfKind ``Mathlib.Linter.UnusedTactic.«command#show_kind_» then return
  let env ← getEnv
  let cats := (Parser.parserExtension.getState env).categories
  -- These lookups may fail when the linter is run in a fresh, empty environment
  let some tactics := Parser.ParserCategory.kinds <$> cats.find? `tactic
    | return
  let some convs := Parser.ParserCategory.kinds <$> cats.find? `conv
    | return
  let trees ← getInfoTrees
  let exceptions := (← allowedRef.get).union <| allowedUnusedTacticExt.getState env
  let go : M Unit := do
    getTactics (← ignoreTacticKindsRef.get) (fun k => tactics.contains k || convs.contains k) stx
    eraseUsedTacticsList exceptions trees
  let (_, map) ← go.run {}
  let unused := map.toArray
  let key (r : String.Range) := (r.start.byteIdx, (-r.stop.byteIdx : Int))
  let mut last : String.Range := ⟨0, 0⟩
  for (r, stx) in let _ := @lexOrd; let _ := @ltOfOrd.{0}; unused.qsort (key ·.1 < key ·.1) do
    if stx.getKind ∈ [``Batteries.Tactic.unreachable, ``Batteries.Tactic.unreachableConv] then
      continue
    if last.start ≤ r.start && r.stop ≤ last.stop then continue
    Linter.logLint linter.unusedTactic stx m!"'{stx}' tactic does nothing"
    last := r

initialize addLinter unusedTacticLinter
