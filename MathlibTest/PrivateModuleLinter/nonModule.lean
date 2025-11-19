import Mathlib.Tactic.Linter.PrivateModule

/- Should not fire because this file does not use `module`, even though it is nonempty and has only private defs. -/

private theorem foo : True := trivial

private def bar : Bool := true
