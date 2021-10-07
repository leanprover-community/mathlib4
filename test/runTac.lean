import Lean.Elab.Tactic.ElabTerm
import Mathlib.Tactic.RunTac

open Lean Elab Tactic

example : True := by
  runTac do
    evalApplyLikeTactic Meta.apply (← `(True.intro))
