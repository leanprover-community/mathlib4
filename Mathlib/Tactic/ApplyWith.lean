/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Eval
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# The `applyWith` tactic
The `applyWith` tactic is like `apply`, but allows passing a custom configuration to the underlying
`apply` operation.
-/

public meta section

namespace Mathlib.Tactic
open Lean Parser Meta Elab Tactic Term

/-- Elaborator for the configuration in `apply (config := cfg)` syntax. -/
declare_config_elab elabApplyConfig ApplyConfig

/--
* `apply (config := cfg) e` allows for additional configuration (see `Lean.Meta.ApplyConfig`):
  * `newGoals` controls which new goals are added by `apply`, in which order.
  * `-synthAssignedInstances` will not synthesize instance implicit arguments if they have been
    assigned by `isDefEq`.
  * `+allowSynthFailures` will create new goals when instance synthesis fails, rather than erroring.
  * `+approx` enables `isDefEq` approximations (see `Lean.Meta.approxDefEq`).
-/
tactic_extension Lean.Parser.Tactic.apply

@[tactic_alt Lean.Parser.Tactic.apply]
elab (name := applyWith) "apply" cfg:optConfig ppSpace e:term : tactic => do
  let cfg ← elabApplyConfig cfg
  evalApplyLikeTactic (·.apply · cfg) e

end Mathlib.Tactic
