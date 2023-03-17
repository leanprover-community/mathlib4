/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean

/-!
# Helper functions for using the simplifier.
-/

open Lean Elab.Tactic

namespace Lean.Meta

/-- Construct a `SimpTheorems` from a list of names. (i.e. as with `simp only`). -/
def simpTheoremsOfNames (lemmas : List Name) : MetaM SimpTheorems := do
  lemmas.foldlM (·.addConst ·) (← simpOnlyBuiltins.foldlM (·.addConst ·) {})

/-- Simplify an expression using only a list of lemmas specified by name. -/
-- TODO We need to write a `mkSimpContext` in `MetaM`
-- that supports all the bells and whistles in `simp`.
-- It should generalize this, and another partial implementation in `Tactic.Simps.Basic`.
def simpOnlyNames (lemmas : List Name) (e : Expr) (config : Simp.Config := {}) :
    MetaM Simp.Result := do
  (·.1) <$> simp e
    { simpTheorems := #[← simpTheoremsOfNames lemmas], congrTheorems := ← getSimpCongrTheorems,
      config := config }

/--
Given a simplifier `S : Expr → MetaM Simp.Result`,
and an expression `e : Expr`, run `S` on the type of `e`, and then
convert `e` into that simplified type, using a combination of type hints and `Eq.mp`.
-/
def simpType (S : Expr → MetaM Simp.Result) (e : Expr) : MetaM Expr := do
  match (← S (← inferType e)) with
  | ⟨ty', none, _⟩ => mkExpectedTypeHint e ty'
  -- We use `mkExpectedTypeHint` in this branch as well, in order to preserve the binder types.
  | ⟨ty', some prf, _⟩ => mkExpectedTypeHint (← mkEqMP prf e) ty'

/-- Independently simplify both the left-hand side and the right-hand side
of the equality given by `type`.
The equality is allowed to be under binders.
Returns the simplified equality and a proof of it. -/
def simpEq (S : Expr → MetaM Simp.Result) (type pf : Expr) : MetaM (Expr × Expr) := do
  forallTelescope type fun fvars type => do
    let .app (.app (.app (.const `Eq [u]) α) lhs) rhs := type | throwError "simpEq expecting Eq"
    let ⟨lhs', lhspf?, _⟩ ← S lhs
    let ⟨rhs', rhspf?, _⟩ ← S rhs
    let mut pf' := mkAppN pf fvars
    if let some lhspf := lhspf? then
      pf' ← mkEqTrans (← mkEqSymm lhspf) pf'
    if let some rhspf := rhspf? then
      pf' ← mkEqTrans pf' rhspf
    let type' := mkApp3 (mkConst ``Eq [u]) α lhs' rhs'
    guard <| ← isDefEq type' (← inferType pf')
    return (← mkForallFVars fvars type', ← mkLambdaFVars fvars pf')

end Lean.Meta
