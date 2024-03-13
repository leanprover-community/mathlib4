/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Lean.Linter.Util
import Std.Tactic.Unreachable

/-!
#  The unused tactic linter

The unused linter makes sure that every tactic call actually changes *something*.

##  Implementation notes

Yet another linter copied from the `unreachableTactic` linter!
-/

open Lean Elab

namespace Mathlib.Linter

/-- The unused tactic linter makes sure that every tactic call actually changes *something*. -/
register_option linter.unusedTactic : Bool := {
  defValue := true
  descr := "enable the unused tactic linter"
}

namespace unusedTactic

/-- The monad for collecting `simp`s that are not `simp only`. -/
abbrev M := StateRefT (HashMap String.Range Syntax) IO

/-- `Parser`s allowed to not change the tactic state. -/
abbrev allowed := [
  ``Lean.Parser.Tactic.«tactic_<;>_»,
  ``Lean.Parser.Tactic.tacticSeq,
  ``Lean.Parser.Tactic.tacticSeq1Indented,
  `Mathlib.Tactic.Says.says,
  `Std.Tactic.«tacticOn_goal-_=>_»
]

/--
A list of blacklisted syntax kinds, which are expected to have subterms that contain
unevaluated tactics.
-/
initialize ignoreTacticKindsRef : IO.Ref NameHashSet ←
  IO.mkRef <| HashSet.empty
    |>.insert `Mathlib.Tactic.Says.says
    |>.insert ``Parser.Term.binderTactic
    |>.insert ``Lean.Parser.Term.dynamicQuot
    |>.insert ``Lean.Parser.Tactic.quotSeq
    |>.insert ``Lean.Parser.Tactic.tacticStop_
    |>.insert ``Lean.Parser.Command.notation
    |>.insert ``Lean.Parser.Command.mixfix
    |>.insert ``Lean.Parser.Tactic.discharger

/-- Is this a syntax kind that contains intentionally unevaluated tactic subterms? -/
def isIgnoreTacticKind (ignoreTacticKinds : NameHashSet) (k : SyntaxNodeKind) : Bool :=
  match k with
  | .str _ "quot" => true
  | _ => ignoreTacticKinds.contains k

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

mutual
/-- Search for tactic executions in the info tree and remove executed tactic syntaxes. -/
partial def eraseUsedTacticsList (trees : PersistentArray InfoTree) : M Unit :=
  trees.forM eraseUsedTactics

/-- Search for tactic executions in the info tree and remove executed tactic syntaxes. -/
partial def eraseUsedTactics : InfoTree → M Unit
  | .node i c => do
    if let .ofTacticInfo i := i then
      if let some r := i.stx.getRange? true then
        if i.goalsAfter != i.goalsBefore || i.stx.getKind ∈ allowed then
          modify (·.erase r)
    eraseUsedTacticsList c
  | .context _ t => eraseUsedTactics t
  | .hole _ => pure ()

end

/-- Gets the value of the `linter.unused` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.unusedTactic o

/-- The main entry point to the unused tactic linter. -/
def unusedTactic : Linter where run := withSetOptionIn fun stx => do
  unless getLinterHash (← getOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return
  let cats := (Parser.parserExtension.getState (← getEnv)).categories
  -- These lookups may fail when the linter is run in a fresh, empty environment
  let some tactics := Parser.ParserCategory.kinds <$> cats.find? `tactic
    | return
  let some convs := Parser.ParserCategory.kinds <$> cats.find? `conv
    | return
  let trees ← getInfoTrees
  let go : M Unit := do
    getTactics (← ignoreTacticKindsRef.get) (fun k => tactics.contains k || convs.contains k) stx
    eraseUsedTacticsList trees
  let (_, map) ← go.run {}
  let unused := map.toArray
  let key (r : String.Range) := (r.start.byteIdx, (-r.stop.byteIdx : Int))
  let mut last : String.Range := ⟨0, 0⟩
  for (r, stx) in let _ := @lexOrd; let _ := @ltOfOrd.{0}; unused.qsort (key ·.1 < key ·.1) do
    if stx.getKind ∈ [``Std.Tactic.unreachable, ``Std.Tactic.unreachableConv] then continue
    if last.start ≤ r.start && r.stop ≤ last.stop then continue
    Linter.logLint linter.unusedTactic stx m!"'{stx}' tactic does nothing"
    last := r

initialize addLinter unusedTactic
