/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Echelon.Rat

public meta import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# The `ℤ√d` model for the Bareiss elimination

The computable model of the quadratic extensions `ℤ√d`: values are pairs `(a, b)`
denoting `a + b√d`, with the multiplication reduced by `√d * √d = d` and exact division
by conjugation. Entries are `⟨a, b⟩` literals, `√d`, or numerals.

## Main definitions

- `zsqrtdProducer`: the `ℤ√d` model.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Echelon

/-- Evaluate an entry or component of the `ℤ√d` model to an integer. -/
def evalInt (e : Expr) : MetaM Int := do
  let v ← evalEntry true e
  unless v.den == 1 do
    throwError "the value does not evaluate to an integer numeral{indentExpr e}"
  return v.num

/-- Evaluate a `ℤ√d` entry to its pair of integer components: a `⟨a, b⟩` literal, `√d`
itself, or an entry without `√d` content evaluating through `norm_num`. -/
def evalZsqrtdEntry (e : Expr) : MetaM (Int × Int) := do
  match_expr e with
  | Zsqrtd.mk _ a b => return (← evalInt a, ← evalInt b)
  | Zsqrtd.sqrtd _ => return (0, 1)
  | _ => return (← evalInt e, 0)

/-- The `ℤ√d` model, for `d` the value of the integer literal `dQ`: values are pairs
`(a, b)` denoting `a + b√d`, and the elimination runs on integer pairs. -/
def zsqrtdProducer (dQ : Q(ℤ)) (d : Int) : Producer :=
  let ops : RingOps (Int × Int) := {
    zero := (0, 0)
    one := (1, 0)
    mul := fun (a, b) (c, e) => (a * c + d * b * e, a * e + b * c)
    sub := fun (a, b) (c, e) => (a - c, b - e)
    divExact := fun (a, b) (c, e) =>
      -- multiply by the conjugate `c - e√d` and divide by the norm, exactly
      let norm := c * c - d * e * e
      ((a * c - d * b * e) / norm, (b * c - a * e) / norm)
    isZero := fun (a, b) => pure (a == 0 && b == 0) }
  let prepare (entries : Array (Array Expr)) :
      MetaM (Array (Array (Int × Int)) ×
        (BareissData (Int × Int) → BareissData (Int × Int))) := do
    let values ← entries.mapM (·.mapM evalZsqrtdEntry)
    return (values, id)
  let render : Int × Int → MetaM Expr := fun (a, b) =>
    return q((⟨$(mkIntLitQ a), $(mkIntLitQ b)⟩ : Zsqrtd $dQ))
  mkProducer ops prepare render

/-- The `ℤ√d` model registration: handles `Zsqrtd d` for an integer literal `d`. -/
@[bareiss_ext] def zsqrtdExt : BareissExt where
  producer? R := do
    let_expr Zsqrtd dE := R | return none
    let some d ← getIntValue? dE | return none
    have dQ : Q(ℤ) := dE
    return some (zsqrtdProducer dQ d)

end Mathlib.Tactic.Echelon
