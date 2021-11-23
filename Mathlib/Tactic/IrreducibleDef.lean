/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import Lean

/-!
# Irreducible definitions

This file defines an `irreducible_def` command,
which works almost like the `def` command
except that the introduced definition
does not reduce to the value.
Instead, the command
adds a `_def` lemma
which can be used for rewriting.

```
irreducible_def frobnicate (a b : Nat) :=
  a + b

example : frobnicate a 0 = a := by
  simp [frobnicate_def]
```

-/

namespace Lean.Elab.Command

open Term Meta

/-- `delta% t` elaborates to a head-delta reduced version of `t`. -/
elab "delta% " t:term : term <= expectedType => do
  let t ← elabTerm t expectedType
  synthesizeSyntheticMVars
  let t ← instantiateMVars t
  let some t ← delta? t | throwError "cannot delta reduce {t}"
  t

/- `eta_helper f = (· + 3)` elabs to `∀ x, f x = x + 3` -/
local elab "eta_helper " t:term : term => do
  let t ← elabTerm t none
  let some (_, lhs, rhs) ← t.eq? | throwError "not an equation: {t}"
  synthesizeSyntheticMVars
  let rhs ← instantiateMVars rhs
  lambdaLetTelescope rhs fun xs rhs => do
    let lhs := (← mkAppN lhs xs).headBeta
    mkForallFVars xs <|<- mkEq lhs rhs

/-- `value_proj x` elabs to `@x.value` -/
local elab "value_proj" e:term : term => do
  let e ← elabTerm e none
  mkProjection e `value

/--
Executes the commands,
and stops after the first error.
In short, S-A-F-E.
-/
local syntax "stop_at_first_error" command* : command
open Command in elab_rules : command
  | `(stop_at_first_error $[$cmds]*) => do
    for cmd in cmds do
      elabCommand cmd
      if (← get).messages.hasErrors then break

/--
Introduces an irreducible definition.
`irreducible_def foo := 42` generates
a constant `foo : Nat` as well as
a theorem `foo_def : foo = 42`.
-/
syntax declModifiers "irreducible_def" declId optDeclSig " :=\n" term : command
macro_rules
| `($mods:declModifiers irreducible_def $n:ident $declSig:optDeclSig := $val) =>
  let n_def := mkIdent <| (·.review) <|
    let scopes := extractMacroScopes n.getId
    { scopes with name := scopes.name.appendAfter "_def" }
  `(stop_at_first_error
    def definition $declSig:optDeclSig := $val
    structure Wrapper where
      value : type_of% @definition
      prop : Eq @value @(delta% @definition)
    constant wrapped : Wrapper := ⟨_, rfl⟩
    $mods:declModifiers def $n := value_proj @wrapped
    theorem $n_def : eta_helper Eq @$n:ident @(delta% @definition) := by
      intros
      simp only [$n:ident]
      rw [wrapped.prop])
