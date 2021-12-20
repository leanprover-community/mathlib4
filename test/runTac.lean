import Lean.Elab.Tactic.ElabTerm
import Mathlib.Tactic.RunTac

open Lean Elab Tactic

example : True := by
  run_tac do
    evalApplyLikeTactic Meta.apply (← `(True.intro))
