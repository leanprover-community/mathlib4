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

The linter equates "non-terminal" with "closes at least one goal".
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

mutual
/-- Search for `simp`s that
* are not `simp only` and
* do not close a goal.

Add such `simp`s to the state. -/
partial def addNonSimpOnlysList (trees : PersistentArray InfoTree) : M Unit :=
  trees.forM addNonSimpOnlys

@[inherit_doc addNonSimpOnlysList]
partial def addNonSimpOnlys : InfoTree → M Unit
  | .node i c => do
    if let .ofTacticInfo i := i then
      let non_terminal_simp? := (! onlyOrNotSimp i.stx) &&
                                (! i.goalsAfter.length < i.goalsBefore.length)
      match i.stx.getRange? true, non_terminal_simp? with
        | some r, true => dbg_trace "{i.stx}"; modify (·.insert r i.stx)
        | _, _ => pure ()
    addNonSimpOnlysList c
  | .context _ t => addNonSimpOnlys t
  | .hole _ => pure ()

end

/-- Gets the value of the `linter.nonTerminalSimp` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.nonTerminalSimp o

/-- The main entry point to the unreachable tactic linter. -/
def nonTerminalSimpLinter : Linter where run := withSetOptionIn fun _stx => do
  unless getLinterHash (← getOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return
  let (_, map) ← (addNonSimpOnlysList (← getInfoTrees)).run {}
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

initialize addLinter nonTerminalSimpLinter
