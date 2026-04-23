/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic  -- shake: keep (tactic dependency)
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.SetLike

/-!
The command `name_poly_vars` names variables in
`MvPolynomial (Fin n) R` for the appropriate value of `n`.
The notation introduced by this command is local.

Usage:

```lean
variable (R : Type) [CommRing R]

name_poly_vars X, Y, Z over R

#check Y -- Y : MvPolynomial (Fin 3) R
```
-/

public meta section

open Lean Elab Command

namespace Mathlib.Tactic

/--
The command `name_poly_vars` names variables in
`MvPolynomial (Fin n) R` for the appropriate value of `n`.
The notation introduced by this command is local.

Usage:

```lean
variable (R : Type) [CommRing R]

name_poly_vars X, Y, Z over R

#check Y -- Y : MvPolynomial (Fin 3) R
```
-/
syntax (name := namePolyVarsOver) "name_poly_vars" (ppSpace ident),+ " over " term : command

@[command_elab namePolyVarsOver, inherit_doc namePolyVarsOver]
def elabNameVariablesOver : CommandElab
| `(command|name_poly_vars $vars:ident,* over $R:term) => do
  let vars := vars.getElems
  let size := vars.size
  let sizeStx : TSyntax `term := quote size
  for h : idx in [:size] do
    let var := vars[idx]
    let var := quote s!"{var.getId}"
    let idx : TSyntax `term ← `(($(quote idx) : Fin $sizeStx))
    let cmd ← `(command|local notation3 $var:str =>
      MvPolynomial.X (R := $R) (σ := Fin $sizeStx) $idx)
    elabCommand cmd
| _ => throwUnsupportedSyntax

end Mathlib.Tactic
