/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Init

/-!
# `elabTermWithoutNewMVars`

-/

open Lean Elab Tactic

/-- Elaborates a term with `errToSorry = false` and ensuring it has no metavariables. -/
def elabTermWithoutNewMVars (tactic : Name) (t : Term) : TacticM Expr := Term.withoutErrToSorry do
  let (e, mvars) ← elabTermWithHoles t none tactic
  unless mvars.isEmpty do
    throwErrorAt t "Argument passed to {tactic} has metavariables:{indentD e}"
  return e
