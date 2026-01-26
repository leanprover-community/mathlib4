
/-!
# Defines the `trace` tactic.
-/

public meta section

open Lean Meta Elab Tactic

/-- Evaluates a term to a string (when possible), and prints it as a trace message. -/
elab (name := Lean.Parser.Tactic.trace) tk:"trace " val:term : tactic => do
  let e ← elabTerm (← `(toString $val)) (some (mkConst `String))
  logInfoAt tk <|← unsafe evalExpr String (mkConst `String) e
