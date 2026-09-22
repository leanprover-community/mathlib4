/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Echelon.Core
public import Mathlib.Tactic.NormNum.Basic

public meta import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# The `ℤ√d` model for the Bareiss elimination

The computable model of the quadratic extensions `ℤ√d`.
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

/-- The arithmetic of `ℤ√d`, with exact division by conjugation. -/
def zsqrtdOps (d : ℤ) : RingOps (ℤ√d) where
  zero := 0
  one := 1
  mul := (· * ·)
  sub := (· - ·)
  divExact x y :=
    let z := x * star y
    let n := y.norm
    ⟨z.re / n, z.im / n⟩
  isZero := (· == 0)

/-- The integer of a raw literal `Int.ofNat n` or `Int.negOfNat n`. -/
def intOfRawLit (e : Expr) : ℤ :=
  match e with
  | .app (.const ``Int.ofNat _) (.lit (.natVal n)) => n
  | .app (.const ``Int.negOfNat _) (.lit (.natVal n)) => -n
  | _ => panic! "not a raw integer literal"

/-- The value of a literal `⟨re, im⟩ : ℤ√d` with raw integer components. -/
def zsqrtdOfRawLit (d : ℤ) (e : Expr) : ℤ√d :=
  match e with
  | .app (.app (.app (.const ``Zsqrtd.mk _) _) re) im => ⟨intOfRawLit re, intOfRawLit im⟩
  | _ => panic! "not a ℤ√d literal"

/-- The literal `⟨re, im⟩ : ℤ√d` of a value, with raw integer components, for `d` the value
of the integer literal `dQ`. -/
def mkZsqrtdRawLit (dQ : Q(ℤ)) {d : ℤ} (v : ℤ√d) : Expr :=
  mkApp3 (.const ``Zsqrtd.mk []) dQ (Meta.NormNum.mkRawIntLit v.re) (Meta.NormNum.mkRawIntLit v.im)

/-- The `ℤ√d` model, for `d` the value of the integer literal `dQ`: the elimination runs on
literals with raw integer components, computed with the arithmetic of `ℤ√d`. -/
def zsqrtdModel (dQ : Q(ℤ)) (d : ℤ) : Model where
  carrier := .expr
  ops := (zsqrtdOps d).lift (zsqrtdOfRawLit d) (mkZsqrtdRawLit dQ)
  prepare entries := do
    let values ← entries.mapM (·.mapM fun e => return mkZsqrtdRawLit dQ (← evalZsqrtdEntry d e))
    return (values, id)
  mkEntry e := do
    let v := zsqrtdOfRawLit d e
    return q((⟨$(mkIntLitQ v.re), $(mkIntLitQ v.im)⟩ : Zsqrtd $dQ))

/-- The `ℤ√d` model registration: handles `Zsqrtd d` for an integer literal `d`. -/
@[bareiss_ext] def zsqrtdExt : BareissExt where
  model? R := do
    -- unfold reducible aliases such as `GaussianInt` before matching
    let R ← whnfR R
    let_expr Zsqrtd dE := R | return none
    let some d ← getIntValue? dE | return none
    have dQ : Q(ℤ) := dE
    return some (zsqrtdModel dQ d)

end Mathlib.Tactic.Echelon
