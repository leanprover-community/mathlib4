import Aesop
import Mathlib.Tactic.Reap.Tactic.Generator

def reapTacGen : Aesop.TacGen := TacticGenerator.generateTactics


macro "reap!!" : tactic => `(tactic| aesop? (add 100% reapTacGen))
