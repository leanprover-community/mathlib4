import Mathlib.Tactic.AutoInduction.Attr
import Lean

set_option autoImplicit false
set_option linter.unusedTactic false

open Lean Elab Parser Tactic Meta

/--
`autoinduction` effectively calls `induction _ using` with the relevant definition marked with the
`@[autoinduction]` attribute. In addition, it uses the arguments specified at that point to
try to provide a value for the respective argument.
-/
syntax (name := autoinductiontac) "autoinduction" elimTarget
  (" generalizing" (ppSpace colGt term:max)+)? (inductionAlts)? : tactic
