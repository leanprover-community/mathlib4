import Mathlib.Algebra.MvPolynomial.Basic

open Lean Elab Command

namespace Mathlib.Tactic

syntax (name := nameVariablesOver)
  "name_variables " ident,+ " over " term : command

@[command_elab nameVariablesOver]
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
