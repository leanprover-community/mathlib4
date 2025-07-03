/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.Algebra.MvPolynomial.Basic

/-!
The command `name_variables` names variables in
`MvPolynomial (Fin n) R` for the appropriate value of `n`.
The notation introduced by this command is local.

Usage:

```lean
variable (R : Type) [CommRing R]

name_variables X, Y, Z over R

#check Y -- Y : MvPolynomial (Fin 3) R
```
-/

open Lean Elab Command

namespace Mathlib.Tactic

/--
The command `name_variables` names variables in
`MvPolynomial (Fin n) R` for the appropriate value of `n`.
The notation introduced by this command is local.

Usage:

```lean
variable (R : Type) [CommRing R]

name_variables X, Y, Z over R

#check Y -- Y : MvPolynomial (Fin 3) R
```
-/
syntax (name := nameVariablesOver) "name_variables " ident,+ " over " term : command

@[command_elab nameVariablesOver, inherit_doc nameVariablesOver]
def elabNameVariablesOver : CommandElab
| `(command|name_variables $vars:ident,* over $R:term) => do
  let vars := vars.getElems
  let size := vars.size
  let sizeStx : TSyntax `term := quote size
  for h : idx in [:size] do
    let var := vars[idx]
    let var := quote s!"{var.getId}"
    let hidx : idx < size := Membership.get_elem_helper h rfl
    let idx : TSyntax `term ← `(Fin.mk $(quote idx) (by decide))
    let cmd ← `(command|local notation3 $var:str =>
      MvPolynomial.X (R := $R) (σ := Fin $sizeStx) $idx)
    elabCommand cmd
| _ => throwUnsupportedSyntax

end Mathlib.Tactic
