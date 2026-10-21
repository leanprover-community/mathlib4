module

public meta import Lean.Elab.Tactic.ElabTerm

@[expose] public section

open Lean Elab Tactic

example : True := by
  run_tac
    evalApplyLikeTactic MVarId.apply (← `(True.intro))

example : True := by_elab
  Term.elabTerm (← `(True.intro)) none
