import Lean.Elab.Tactic.ElabTerm
import Mathlib.Tactic.RunCmd

open Lean Elab Tactic

example : True := by
  run_tac
    evalApplyLikeTactic MVarId.apply (← `(True.intro))

example : True := by_elab
  Term.elabTerm (← `(True.intro)) none
