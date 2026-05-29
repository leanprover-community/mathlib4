/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Eval
public meta import Lean.Elab.Tactic.ElabTerm
public import Lean.Elab.Tactic.Config

/-!
# The `applyWith` tactic
The `applyWith` tactic is like `apply`, but allows passing a custom configuration to the underlying
`apply` operation.
-/

public meta section

namespace Mathlib.Tactic
open Lean Parser Meta Elab Tactic Term

/-- At least one configuration option for tactics.

If a configuration elaborator is defined as `declare_config_elab elabMyConfig MyConfigStruct`,
a `manyConfig` syntax item ```cfg : TSyntax ``manyConfig``` can be passed to it using
`elabMyConfig (optConfigOf cfg)`.

`optConfig` allows zero or more options, `manyConfig` requires at least one option.
-/
syntax manyConfig := (colGt configItem)+

/--
Extracts the items from a tactic configuration,
either a `Mathlib.Tactic.manyConfig`, `Lean.Parser.Tactic.optConfig`, `Lean.Parser.Tactic.config`,
or these wrapped in null nodes.
-/
def getManyConfigItems (c : Syntax) : TSyntaxArray ``configItem :=
  if c.isOfKind nullKind then
    c.getArgs.flatMap getConfigItems
  else
    match c with
    | `(manyConfig| $items:configItem*) => items
    | `(optConfig| $items:configItem*) => items
    | `(config| (config := $_)) => #[⟨c⟩] -- handled by mkConfigItemViews
    | _ => #[]

/-- Convert `manyConfig`, `optConfig` or `config` syntax into `optConfig`,
for use in a `declare_config_elab` elaborator. -/
def optConfigOf (c : Syntax) : TSyntax ``optConfig :=
  mkOptConfig (getManyConfigItems c)

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
-- We have to use `manyConfig` instead of `optConfig` to avoid ambiguous parses.
elab (name := applyWith) "apply" cfg:manyConfig ppSpace e:term : tactic => do
  let cfg ← elabApplyConfig (optConfigOf cfg)
  evalApplyLikeTactic (·.apply · cfg) e

end Mathlib.Tactic
