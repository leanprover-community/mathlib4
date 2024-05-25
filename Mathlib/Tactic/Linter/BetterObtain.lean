/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lean.Elab.Command
import Lean.Linter.Util

/-! ## Attempt to remove stream-of-conciousness syntax from `obtain`

Create a clone `myobtain` which requires a proof directly.

On second thought, just write a linter against it... -/

open Lean Elab

namespace Mathlib.Linter.Style

-- /--
-- The `myobtain` tactic is a combination of `have` and `rcases`. See `rcases` for
-- a description of supported patterns.

-- ```lean
-- myobtain ⟨patt⟩ : type := proof
-- ```
-- is equivalent to
-- ```lean
-- have h : type := proof
-- rcases h with ⟨patt⟩
-- ```

-- If `⟨patt⟩` is omitted, `rcases` will try to infer the pattern.

-- Unlike in the core lean version, `:= proof` is required, even if `type` is omitted.
-- -/
-- syntax (name := myobtain) "myobtain" (ppSpace Tactic.rcasesPatMed)? (" : " term)? " := " term,+ : tactic

-- --@[builtin_tactic Lean.Parser.Tactic.obtain]
-- --@[tactic Lean.Parser.Tactic.RCases.myobtain]
-- def evalObtain' : Tactic := fun stx => do
--   match stx with
--   | `(tactic| myobtain%$tk $[$pat?:rcasesPatMed]? $[: $ty?]? := $val,*) =>
--     let pat? ← liftM <| pat?.mapM RCasesPatt.parse
--     if true then
--       let pat  := pat?.getD (RCasesPatt.one tk `_)
--       let pat  := pat.typed? tk ty?
--       let tgts := val.getElems.map fun val => (none, val.raw)
--       let g ← getMainGoal
--       g.withContext do replaceMainGoal (← RCases.rcases tgts pat g)
--   | _ => throwUnsupportedSyntax

/-- Whether a syntax element is an `obtain` tactic call without a provided proof. -/
def is_obtain_without_proof : Syntax → Bool
  -- Cases with a proof.
  | `(tactic|obtain $_pat := $_proof) => false
  | `(tactic|obtain $_pat : $_type := $_proof) => false
  -- Case without a proof.
  | `(tactic|obtain : $_type) => true
  | `(tactic|obtain $_pat : $_type) => true
  | _ => false

/-- The `badObtain` linter emits a warning upon uses of "stream-of-conciousness" obtain,
i.e. with the proof postponed. -/
register_option linter.badObtain : Bool := {
  defValue := true
  descr := "enable the `badObtain` linter"
}

/-- Gets the value of the `linter.badObtain` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.badObtain o

/-- The `badObtain` linter: this lints ...
why bad?
what else?
-/
def badObtainLinter : Linter where run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    if let some ((head, _n)::_chain) := stx.findStack? (fun _ ↦ true) is_obtain_without_proof then
      Linter.logLint linter.badObtain head m!"Bad obtain syntax; please remove"

initialize addLinter badObtainLinter
