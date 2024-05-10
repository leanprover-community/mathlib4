/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Tactic.ElabTerm
import Lean.Meta.Eval

/-!
# Defines the `trace` tactic.
-/

open Lean Meta Elab Tactic

/-- Evaluates a term to a string (when possible), and prints it as a trace message. -/
elab (name := Lean.Parser.Tactic.trace) tk:"trace " val:term : tactic => do
  let e ← elabTerm (← `(toString $val)) (some (mkConst `String))
  logInfoAt tk <|← unsafe evalExpr String (mkConst `String) e
