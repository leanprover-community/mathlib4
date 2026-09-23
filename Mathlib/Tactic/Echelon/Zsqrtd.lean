/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.Tactic.Echelon.Core
public import Mathlib.Tactic.NormNum.Basic
public meta import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# The `ℤ√d` model for the Bareiss elimination

The computable model of the quadratic extensions `ℤ√d`.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Echelon

/-- Evaluate an entry or component of the `ℤ√d` model to an integer, via `norm_num`. -/
def evalInt (e : Expr) : MetaM ℤ := do
  let ⟨_, _, eQ⟩ ← inferTypeQ' e
  let r ← try some <$> Mathlib.Meta.NormNum.derive eQ catch _ => pure none
  if let some v := r.bind (·.toRat) then
    if v.den == 1 then
      return v.num
  throwError "the following entry cannot be simplified to an integer numeral{indentExpr e}"

/-- Evaluate a `ℤ√d` entry to its value. The entry is a `⟨re, im⟩` literal, `√d` itself, or
an entry without `√d` content, which `norm_num` evaluates. -/
def evalZsqrtdEntry (d : ℤ) (e : Expr) : MetaM (ℤ√d) := do
  match_expr e with
  | Zsqrtd.mk _ re im => return ⟨← evalInt re, ← evalInt im⟩
  | Zsqrtd.sqrtd _ => return .sqrtd
  | _ => return ⟨← evalInt e, 0⟩

/-- The arithmetic of `ℤ√d`, with exact division by conjugation. -/
def zsqrtdOps (d : ℤ) : RingOps (ℤ√d) where
  zero := 0
  one := 1
  mul := Mul.mul
  sub := Sub.sub
  divExact x y :=
    let z := x * star y
    let n := y.norm
    ⟨z.re / n, z.im / n⟩
  isZero x := x == 0

/-- The integer of a raw literal `Int.ofNat n` or `Int.negOfNat n`. -/
def intOfRawLit? (e : Expr) : Option ℤ :=
  match_expr e with
  | Int.ofNat n => n.rawNatLit?
  | Int.negOfNat n => n.rawNatLit?.map fun k => -k
  | _ => none

/-- The value of a literal `⟨re, im⟩ : ℤ√d` with raw integer components. -/
def zsqrtdOfRawLit? (d : ℤ) (e : Expr) : Option (ℤ√d) :=
  match_expr e with
  | Zsqrtd.mk _ re im => do return ⟨← intOfRawLit? re, ← intOfRawLit? im⟩
  | _ => none

/-- The literal `⟨re, im⟩ : ℤ√d` of a value, with raw integer components. `d` is the value of
the integer literal `dQ`. -/
def mkZsqrtdRawLit (dQ : Q(ℤ)) {d : ℤ} (v : ℤ√d) : Q(Zsqrtd $dQ) :=
  q(⟨$(Mathlib.Meta.NormNum.mkRawIntLit v.re), $(Mathlib.Meta.NormNum.mkRawIntLit v.im)⟩)

/-- The `ℤ√d` model. The elimination runs on literals with raw integer components, computed
with the arithmetic of `ℤ√d`. `d` is the value of the integer literal `dQ`. -/
def zsqrtdModel (dQ : Q(ℤ)) (d : ℤ) : (c : Carrier) × Model c.type :=
  let ops := (zsqrtdOps d).lift (zsqrtdOfRawLit? d) (mkZsqrtdRawLit dQ)
  ⟨.expr, {
    ops
    evalEntry := fun e => return (mkZsqrtdRawLit dQ (← evalZsqrtdEntry d e), none)
    mkEntry := fun e => do
      let some v := zsqrtdOfRawLit? d e
        | throwError "expected a `ℤ√d` literal with raw integer components{indentExpr e}"
      return q((⟨$(mkIntLitQ v.re), $(mkIntLitQ v.im)⟩ : Zsqrtd $dQ)) }⟩

/-- The registration of the `ℤ√d` model for `Zsqrtd d` with an integer literal `d`.
Equality in `ℤ√d` is settled by `decide`, so the model has no entry certifier. -/
@[bareiss_ext] def zsqrtdExt : BareissExt where
  model? R := do
    -- unfold reducible aliases such as `GaussianInt` before matching
    let R ← whnfR R
    let_expr Zsqrtd dE := R | return none
    let some d ← getIntValue? dE | return none
    have dQ : Q(ℤ) := dE
    return some (zsqrtdModel dQ d)

end Mathlib.Tactic.Echelon
