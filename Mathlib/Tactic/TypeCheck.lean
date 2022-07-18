import Lean.Elab.Tactic.Basic

syntax (name := typeCheck) "type_check " term : tactic

elab tk:"type_check " e:term : tactic => do
  let e ← Lean.Elab.Term.elabTerm e none
  let type ← Lean.Meta.inferType e
  Lean.logInfoAt tk f!"{← Lean.instantiateMVars type}"
