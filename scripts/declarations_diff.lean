import Lean
--import Batteries -- technically not needed, since `Mathlib` already imports it
--import Mathlib
--import Archive
--import Counterexamples
import Lean.Elab.Command
import Mathlib.adomaniLeanUtils.inspect_syntax

import Lean

open Lean Elab Command

theorem my_rw_rule : 1 + 1 = 2 := by simp

elab " my_rewrite " " @ " hyp:ident : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let hyp' := mkNode `Lean.Parser.Tactic.locationHyp #[hyp]
    let hyp' ← `(Lean.Parser.Tactic.location| at $(hyp))
    dbg_trace hyp'
    Lean.Elab.Tactic.evalTactic (← `(tactic| rw [``rw_rule] at $hyp'))
inspect
example (h : 1 + 1 = 2) : True := by
  rw [] at h
  my_rewrite @ h

open Lean

/--
Prints each declaration in the environment that is not an internal detail.

CI uses the name of this command: if you change it, make sure to update the CI configuration.
-/
elab "#all_declarations " branch:str : command => do
  let mut sorted : Array String := ∅
  for (nm, _) in (← getEnv).constants do
    if !nm.isInternalDetail then
      sorted := sorted.binInsert (· < ·) nm.toString
  dbg_trace "* Writing {sorted.size} declarations to '{branch.getString}'"
  IO.FS.writeFile branch.getString <| .intercalate "\n" sorted.toList
