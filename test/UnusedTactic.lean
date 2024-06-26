import Mathlib.Tactic.Linter.UnusedTactic
import Mathlib.Tactic.AdaptationNote

def why2 : True → True := (by refine ·)

example : True := by
  #adaptation_note /--hi-/
  exact .intro
