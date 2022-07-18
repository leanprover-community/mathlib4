import Lean.Elab.Command

open Lean Meta Elab Tactic

/--
`fconstructor` is like `constructor`
(it calls `apply` using the first constructor of an inductive datatype)
except that it does not reorder goals.
-/
elab "fconstructor " : tactic =>
  constructor (cfg := {newGoals := ApplyNewGoals.all})
