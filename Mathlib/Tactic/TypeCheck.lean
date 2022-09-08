import Lean.Elab.Tactic.Basic

open Lean Meta

/-- Type check the given expression, and trace its type. -/
elab tk:"type_check " e:term : tactic => do
  let e ← Lean.Elab.Term.elabTerm e none
  check e
  let type ← inferType e
  Lean.logInfoAt tk f!"{← Lean.instantiateMVars type}"
