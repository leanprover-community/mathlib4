/-
Copyright (c) 2025 LEAN FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
import Lean

/-!
# `set_default_numeral_type` command

This file provides a command to set the default type for numeric literals
without needing to know the instance name.

## Main declarations

* `set_default_numeral_type α`: Sets numeric literals to default to type `α` by finding
  the appropriate `OfNat` instance and marking it with the `default_instance` attribute.

## Example

```lean
set_default_numeral_type Rat

#check 1  -- 1 : Rat
```
-/

open Lean Elab Command Meta

namespace Mathlib.Tactic.DefaultNumeralType

/-- Syntax for the `set_default_numeral_type` command. -/
syntax (name := setDefaultNumeralType) "set_default_numeral_type " term : command

/--
`set_default_numeral_type α` sets numeric literals to default to type `α`.

This command finds the `OfNat` instance for type `α` and marks it with the
`default_instance` attribute, so that numeric literals like `1`, `42`, etc.
will be interpreted as having type `α` by default.

Example:
```lean
set_default_numeral_type Rat

#check 1  -- 1 : Rat
```

This is equivalent to manually writing:
```lean
attribute [default_instance] Rat.instOfNat
```
but you don't need to know the instance name.

Note: You can reset to the default behavior by running `set_default_numeral_type Nat`.
-/
@[command_elab setDefaultNumeralType]
def elabSetDefaultNumeralType : CommandElab := fun stx => do
  match stx with
  | `(set_default_numeral_type $typ) => do
    -- Elaborate the type
    let α ← liftTermElabM do
      Term.elabType typ

    -- Try to synthesize an OfNat instance for this type
    -- The instance type is: ∀ (n : Nat), OfNat α n
    let ofNatType ← liftTermElabM do
      withLocalDeclD `n (mkConst ``Nat) fun n => do
        let body ← mkAppM ``OfNat #[α, n]
        mkForallFVars #[n] body

    let inst ← liftTermElabM do
      try
        synthInstance ofNatType
      catch e =>
        throwError "Could not find OfNat instance for type {α}\nError: {e.toMessageData}"

    -- Extract the instance name from the synthesized instance
    -- The instance should be a constant or an application of a constant
    let instName := inst.getAppFn.constName?.getD default

    if instName.isAnonymous then
      throwError "Could not determine instance name for OfNat instance of {α}"

    -- Add the default_instance attribute to this instance by running an attribute command
    let attrCmd ← `(command| attribute [default_instance] $(mkIdent instName))
    elabCommand attrCmd

  | _ => throwUnsupportedSyntax

end Mathlib.Tactic.DefaultNumeralType
