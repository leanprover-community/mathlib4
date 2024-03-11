/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Lean.Linter.Util
import Std.Data.Array.Basic

/-!
#  The pointless tactic linter

The pointless linter makes sure that every tactic call actually changes *something*.
-/

open Lean Elab

namespace Mathlib.Linter

/-- The non-terminal `simp` linter makes sure that `simp` is not used as a finishing tactic. -/
register_option linter.pointless : Bool := {
  defValue := true
  descr := "enable the 'non-terminal `simp`' linter"
}

namespace pointless

/-- `onlyOrNotSimp stx` if `stx` is syntax for `simp` *without* `only`, then returns `false` else
returs `true`. -/
def onlyOrNotSimp : Syntax → Bool
  | .node _info `Lean.Parser.Tactic.simp #[_, _, _, only?, _, _] => only?[0].getAtomVal == "only"
  | _ => true

/-- The monad for collecting `simp`s that are not `simp only`. -/
abbrev M := StateRefT (HashMap String.Range Syntax) IO

/-- `Parser`s allowed to not change the tactic state. -/
abbrev allowed := [
  `cdotTk, `«]»,
  `Lean.Parser.Tactic.«tactic_<;>_»,
  `Lean.Parser.Tactic.induction,
  `Lean.Parser.Tactic.exact,
  `Lean.Parser.Tactic.cases,
  `Lean.Parser.Tactic.tacticSeq1Indented,
  `Lean.Parser.Tactic.tacticSeq,
  `Lean.Parser.Tactic.tacticTry_,
  `Mathlib.Tactic.casesM,
  `Lean.Parser.Tactic.paren,
  `«{»,
  `«<;>»,
  `«;»,
  `Lean.Parser.Tactic.tacticRfl,
  `Lean.Parser.Tactic.contradiction,
  `Lean.Parser.Tactic.first,
  -- revise decision
  `Lean.Parser.Tactic.simp
]

mutual
/-- Search for `simp`s that
* are not `simp only` and
* do not close a goal.

Add such `simp`s to the state. -/
partial def pointlessList (trees : PersistentArray InfoTree) : M Unit :=
  trees.forM pointless

@[inherit_doc pointlessList]
partial def pointless : InfoTree → M Unit
  | .node i c => do
    if let .ofTacticInfo i := i then
      if let some r := i.stx.getRange? true then
        if i.goalsAfter == i.goalsBefore &&
           ! i.stx[0].getKind == `simp_rw &&
           ! i.stx.getKind ∈ allowed
        then
          dbg_trace i.stx.getKind
          dbg_trace i.stx[0].getKind
          modify (·.insert r i.stx)
    pointlessList c
  | .context _ t => pointless t
  | .hole _ => pure ()

end

/-- Gets the value of the `linter.pointless` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.pointless o

/-- The main entry point to the pointless tactic linter. -/
def pointlessLinter : Linter where run := withSetOptionIn fun _stx => do
  unless getLinterHash (← getOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return
  let (_, map) ← (pointlessList (← getInfoTrees)).run {}
  let simps := map.toArray
  let key (r : String.Range) := (r.start.byteIdx, (-r.stop.byteIdx : Int))
  let mut last : String.Range := ⟨0, 0⟩
  for (r, stx) in let _ := @lexOrd; let _ := @ltOfOrd.{0}; simps.qsort (key ·.1 < key ·.1) do
    if last.start ≤ r.start && r.stop ≤ last.stop then continue
    Linter.logLint linter.pointless stx
      "pointless tactic: consider removing it!"
    last := r

initialize addLinter pointlessLinter
