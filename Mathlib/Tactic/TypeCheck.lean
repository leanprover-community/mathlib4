/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Lean.Elab.Tactic.Basic

/-!
# The `type_check` tactic
Define the `type_check` tactic: it type checks a given expression, and traces its type.
-/

open Lean Meta

/-- Type check the given expression, and trace its type. -/
elab tk:"type_check " e:term : tactic => do
  let e ← Lean.Elab.Term.elabTerm e none
  check e
  let type ← inferType e
  Lean.logInfoAt tk f!"{← Lean.instantiateMVars type}"
