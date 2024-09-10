/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Init
import Lean.Elab.Tactic.Basic
import Lean.Elab.SyntheticMVars

/-!
# The `type_check` tactic
Define the `type_check` tactic: it type checks a given expression, and traces its type.
-/

open Lean Elab Meta

/-- Type check the given expression, and trace its type. -/
elab tk:"type_check " e:term : tactic => do
  Tactic.withMainContext do
    let e ← Term.elabTermAndSynthesize e none
    check e
    let type ← inferType e
    Lean.logInfoAt tk m!"{← Lean.instantiateMVars type}"
