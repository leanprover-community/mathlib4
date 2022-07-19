import Mathlib.Util.TermUnsafe

open Lean Meta Elab Tactic
elab (name := Lean.Parser.Tactic.trace) tk:"trace " val:term : tactic =>
  withRef tk do
    let e ← elabTerm (← `(toString $val)) (some (mkConst `String))
    logInfo <|← unsafe evalExpr String (mkConst `String) e
