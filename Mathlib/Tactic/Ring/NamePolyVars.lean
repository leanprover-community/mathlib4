/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Basic

/-!
The command `name_poly_vars` names variables in
`MvPolynomial (Fin n) R` for the appropriate value of `n`,
or `Polynomial (Polynomial (... R))` stacked appropriately.
The notation introduced by this command is local.

Usage:

```lean
variable (R : Type) [CommRing R]

name_poly_vars R[X,Y,Z]
name_poly_vars R[s][t][u]

#check Y -- Y : MvPolynomial (Fin 3) R
#check t -- t : Polynomial (Polynomial (Polynomial R))
```
-/

open Lean Elab Command

namespace Mathlib.Tactic

/--
A variable that can be in the head position of a `name_poly_vars` command.
This is either an identifier or a term enclosed in parentheses.
-/
syntax polyVarsHead := ident <|> ("(" term ")")

/--
Convert a `polyVarsHead` to a term.
-/
def polyVarsHeadToTerm? (stx : TSyntax ``polyVarsHead) : Option Term :=
  match stx with
  | `(polyVarsHead| $k:ident) => some { raw := k.raw }
  | `(polyVarsHead| ($u:term)) => some u
  | _ => none

/--
The command `name_poly_vars` names variables in
`MvPolynomial (Fin n) R` for the appropriate value of `n`.
The notation introduced by this command is local.

For `Polynomial (Polynomial (...))`, use the syntax `name_poly_vars R[X][Y][Z]`.

Usage:

```lean
variable (R : Type) [CommRing R]

name_poly_vars R[X,Y,Z]

#check Y -- Y : MvPolynomial (Fin 3) R
```
-/
syntax (name := nameMvPolyVars) "name_poly_vars " polyVarsHead "[" ident,+ "]" : command

/--
The command `name_poly_vars` names variables in `Polynomial (Polynomial (... R))` stacked
appropriately many times. The notation introduced by this command is local.

For `MvPolynomial (Fin n) R`, use the syntax `name_poly_vars R[X,Y,Z]`.

Usage:

```lean
variable (R : Type) [CommRing R]

name_poly_vars R[X][Y][Z]

#check Y -- Y : Polynomial (Polynomial (Polynomial R))
```
-/
syntax (name := namePolyVars) "name_poly_vars " polyVarsHead "[" sepBy(ident, "][") "]" : command

@[command_elab nameMvPolyVars, inherit_doc namePolyVars]
def elabNameMvVariables : CommandElab
| `(command|name_poly_vars $R:polyVarsHead [$vars:ident,*]) => do
  let some R := polyVarsHeadToTerm? R | throwUnsupportedSyntax
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

@[command_elab namePolyVars, inherit_doc namePolyVars]
def elabNamePolyVariables : CommandElab
| `(command|name_poly_vars $R:polyVarsHead [$vars:ident][*]) => do
  let some R := polyVarsHeadToTerm? R | throwUnsupportedSyntax
  let vars := vars.getElems.reverse
  let size := vars.size
  let type : Term ← size.rec (return R) fun _ S ↦ do
    let S' ← S
    `(Polynomial $S')
  let mut term : Term ← `(Polynomial.X)
  for h : idx in [:size] do
    let var := vars[idx]
    let var := quote s!"{var.getId}"
    let cmd ← `(command|local notation3 $var:str => ($term : $type))
    elabCommand cmd
    term ← `(Polynomial.C $term)
  return ()
| _ => throwUnsupportedSyntax

end Mathlib.Tactic
