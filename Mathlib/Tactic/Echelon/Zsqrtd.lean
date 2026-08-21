/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Echelon.Core
public import Mathlib.Tactic.NormNum.Basic

public meta import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# The `ℤ√d` model for the Bareiss elimination

The computable model of the quadratic extensions `ℤ√d`: the elimination runs on `ℤ√d`
values with the ring's own arithmetic, with exact division by conjugation. Entries are
`⟨a, b⟩` literals, `√d`, or numerals.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Echelon

/-- Evaluate an entry or component of the `ℤ√d` model to an integer, via `norm_num`. -/
def evalInt (e : Expr) : MetaM Int := do
  let ⟨_, _, eQ⟩ ← inferTypeQ' e
  let r ← try some <$> Meta.NormNum.derive eQ catch _ => pure none
  if let some v := r.bind (·.toRat) then
    if v.den == 1 then
      return v.num
  throwError "the following entry cannot be simplified to an integer numeral{indentExpr e}"

/-- Evaluate a `ℤ√d` entry to a `ℤ√d` value: a `⟨a, b⟩` literal, `√d` itself, or an
entry without `√d` content evaluating through `norm_num`. -/
def evalZsqrtdEntry (d : ℤ) (e : Expr) : MetaM (ℤ√d) := do
  match_expr e with
  | Zsqrtd.mk _ a b => return ⟨← evalInt a, ← evalInt b⟩
  | Zsqrtd.sqrtd _ => return .sqrtd
  | _ => return ⟨← evalInt e, 0⟩

/-- The `ℤ√d` model, for `d` the value of the integer literal `dQ`: the elimination runs
on `ℤ√d` values with the ring's own arithmetic. -/
def zsqrtdProducer (dQ : Q(ℤ)) (d : Int) : Producer :=
  let ops : RingOps (ℤ√d) := {
    zero := 0
    one := 1
    mul := (· * ·)
    sub := (· - ·)
    divExact := fun x y =>
      let z := x * star y
      let n := y.norm
      ⟨z.re / n, z.im / n⟩
    isZero := (· == 0) }
  let prepare (entries : Array (Array Expr)) :
      MetaM (Array (Array (ℤ√d)) × (BareissData (ℤ√d) → BareissData (ℤ√d))) := do
    let values ← entries.mapM (·.mapM (evalZsqrtdEntry d))
    return (values, id)
  let mkEntry : ℤ√d → MetaM Expr := fun v =>
    return q((⟨$(mkIntLitQ v.re), $(mkIntLitQ v.im)⟩ : Zsqrtd $dQ))
  mkProducer ops prepare mkEntry

/-- The `ℤ√d` model registration: handles `Zsqrtd d` for an integer literal `d`. -/
@[bareiss_ext] def zsqrtdExt : BareissExt where
  producer? R := do
    -- unfold reducible aliases such as `GaussianInt` before matching
    let R ← whnfR R
    let_expr Zsqrtd dE := R | return none
    let some d ← getIntValue? dE | return none
    have dQ : Q(ℤ) := dE
    return some (zsqrtdProducer dQ d)

end Mathlib.Tactic.Echelon
