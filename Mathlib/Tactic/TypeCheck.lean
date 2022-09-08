import Lean.Elab.Tactic.Basic

/-- Type check the given expression, and trace its type. -/
elab tk:"type_check " e:term : tactic => do
  let e ← Lean.Elab.Term.elabTerm e none
  try
    Lean.Meta.check e
    let type ← Lean.Meta.inferType e
    Lean.logInfoAt tk f!"{← Lean.instantiateMVars type}"
  catch _ =>
    Lean.logInfoAt tk "Term does not type check"
