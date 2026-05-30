/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Meta.Eval

/-!
# Defines the `trace` tactic.
-/

public meta section

open Lean Meta Elab Tactic

@[tactic_alt Lean.Parser.Tactic.traceMessage]
elab (name := Lean.Parser.Tactic.trace) tk:"trace " val:term : tactic => do
  let e ← elabTerm (← `(toString $val)) (some (mkConst `String))
  logInfoAt tk <|← unsafe evalExpr String (mkConst `String) e

/--
`msg` can be a literal string, or a term that evaluates to a string.
-/
tactic_extension Lean.Parser.Tactic.traceMessage
