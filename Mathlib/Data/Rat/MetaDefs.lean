/-
Copyright (c) 2019 Robert Y. Lewis . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

! This file was ported from Lean 3 source module data.rat.meta_defs
! leanprover-community/mathlib commit c18a48e9f71115845326e03443913f0c3694c153
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Core
import Qq

/-!
# Meta operations on ℚ

This file defines functions for dealing with rational numbers as expressions.

They are not defined earlier in the hierarchy, in the `tactic` or `meta` folders, since we do not
want to import `data.rat.basic` there.

## Main definitions

* `rat.mk_numeral` embeds a rational `q` as a numeral expression into a type supporting the needed
  operations. It does not need a tactic state.
* `rat.reflect` specializes `rat.mk_numeral` to `ℚ`.
* `expr.of_rat` behaves like `rat.mk_numeral`, but uses the tactic state to infer the needed
  structure on the target type.

* `expr.to_rat` evaluates a normal numeral expression as a rat.
* `expr.eval_rat` evaluates a numeral expression with arithmetic operations as a rat.

-/

open Qq

/-- `Int.toExprQ α _ z _` embeds `q` as a numeral expression inside a type with `OfNat` and `-`.
-/
def Int.toExprQ {u : Lean.Level} (α : Q(Type u)) (_ : Q(Neg $α)) (z : ℤ)
  (_ : let zna := z.natAbs; by exact Q(OfNat $α $zna)) : Q($α) :=
  letI zna := z.natAbs; by exact
    if 0 ≤ z then q(OfNat.ofNat $zna : $α) else q(-OfNat.ofNat $zna : $α)

/-- `Rat.toExprQ α _ _ q _ _` embeds `q` as a numeral expression inside a type with `OfNat`, `-`, and `/`.
-/
def Rat.toExprQ {u : Lean.Level} (α : Q(Type u)) (_ : Q(Neg $α)) (_ : Q(Div $α)) (q : ℚ)
  (_ : let qnna := q.num.natAbs; by exact Q(OfNat $α $qnna))
  (i3 : let qd := q.den; by exact Q(OfNat $α $qd)) : Q($α) :=
  let num : ℤ := q.num
  let den : ℕ := q.den
  let nume := Int.toExprQ α ‹_› num ‹_›
  if q.den = 1
    then nume
    else
      let dene : Q($α) := q(@OfNat.ofNat $α $den $i3 : $α)
      q($nume / $dene)
#align rat.mk_numeral Rat.toExprQₓ

section


/-- `Lean.toExpr q` represents the rational number `q` as a numeral expression of type `ℚ`. -/
instance Rat.instToExpr : Lean.ToExpr ℚ where
  toTypeExpr := q(ℚ)
  toExpr q := @Rat.toExprQ Lean.Level.zero
    q(ℚ) q(inferInstance) q(inferInstance) q q(inferInstance) q(inferInstance)

#align rat.reflect Rat.instToExprₓ

end

/-
`rat.to_pexpr q` creates a `pexpr` that will evaluate to `q`.
The `pexpr` does not hold any typing information:
`to_expr ``((%%(rat.to_pexpr (3/4)) : K))` will create a native `K` numeral `(3/4 : K)`.
-/
#noalign rat.to_pexpr

partial def Qq.toNat {u : Lean.Level} {α : Q(Type u)} : Q($α) → Lean.MetaM ℕ
  | ~q(@Zero.zero _ (_)) => pure 0
  | ~q(@One.one _ (_)) => pure 1
  | ~q(@OfNat.ofNat _ $n (_)) => match n with
    | .lit (.natVal n) => pure n
    | _ => failure
  | _ => failure

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Evaluates an expression as a rational number,
      if that expression represents a numeral or the quotient of two numerals. -/
partial def Qq.toNonnegRat {u : Lean.Level} {α : Q(Type u)} : Q($α) → Lean.MetaM ℚ
  | ~q(@HDiv.hDiv $α $α _ (_) $e₁ $e₂) => do
    let m ← Qq.toNat e₁
    let n ← Qq.toNat e₂
    if c : Nat.coprime m n then
      if h : 1 < n then return ⟨m, n, (Nat.zero_lt_one.trans h).ne', c⟩ else failure
      else failure
  | e => do let n ← Qq.toNat e return n
#align expr.to_nonneg_rat Qq.toNonnegRatₓ

/-- Evaluates an expression as a rational number,
if that expression represents a numeral, the quotient of two numerals,
the negation of a numeral, or the negation of the quotient of two numerals. -/
protected unsafe def Qq.toRat {u : Lean.Level} {α : Q(Type u)} : Q($α) → Lean.MetaM ℚ
  | ~q(@Neg.neg _ (_) $(e)) => do
    let q ← Qq.toNonnegRat e
    pure (-q)
  | e => Qq.toNonnegRat e
#align expr.to_rat Qq.toRat

/-- Evaluates an expression into a rational number, if that expression is built up from
numerals, +, -, *, /, ⁻¹  -/
partial def Qq.evalRat {u : Lean.Level} {α : Q(Type u)} : Q($α) → Lean.MetaM ℚ
  | ~q(@Zero.zero _ (_)) => pure 0
  | ~q(@One.one _ (_)) => pure 1
  | ~q(@OfNat.ofNat _ $n (_)) => match n with
    | .lit (.natVal n) => pure n
    | _ => failure
  | ~q(@HAdd.hAdd $α $α _ (_) $a $b) => (· + ·) <$> Qq.evalRat a <*> Qq.evalRat b
  | ~q(@HSub.hSub $α $α _ (_) $a $b) => (· - ·) <$> Qq.evalRat a <*> Qq.evalRat b
  | ~q(@HMul.hMul $α $α _ (_) $a $b) => (· * ·) <$> Qq.evalRat a <*> Qq.evalRat b
  | ~q(@HDiv.hDiv $α $α _ (_) $a $b) => (· / ·) <$> Qq.evalRat a <*> Qq.evalRat b
  | ~q(@Neg.neg _ (_) $a) => Neg.neg <$> Qq.evalRat a
  | ~q(@Inv.inv _ (_) $a) => Inv.inv <$> Qq.evalRat a
  | _ => failure
#align expr.eval_rat Qq.evalRatₓ

-- /-- `expr.of_rat α q` embeds `q` as a numeral expression inside the type `α`.
-- Lean will try to infer the correct type classes on `α`, and the tactic will fail if it cannot.
-- This function is similar to `rat.mk_numeral` but it takes fewer hypotheses and is tactic valued.
-- -/
def Qq.ofRat {u : Lean.Level} (α : Q(Type u)) : ℚ → Lean.MetaM Q($α)
  | ⟨(n : ℕ), d, _h, _c⟩ => do
    let _i : Q(OfNat $α $n) ← synthInstanceQ q(OfNat $α $n)
    let e₁ := q(OfNat.ofNat $n : $α)
    if d = 1
      then pure e₁
      else do
        let _i ← synthInstanceQ q(OfNat $α $d)
        let _i ← synthInstanceQ q(Div $α)
        let e₂ : Q($α) := q(OfNat.ofNat $d : $α)
        pure q($e₁ / $e₂)
  | ⟨Int.negSucc n, d, _h, _c⟩ => do
    let nSucc : ℕ := n.succ
    let _i ← synthInstanceQ q(OfNat $α $nSucc)
    let e₁ := q(OfNat.ofNat $nSucc : $α)
    let e ← if d = 1
        then pure e₁
        else do
          let _i ← synthInstanceQ q(OfNat $α $d)
          let _i ← synthInstanceQ q(Div $α)
          let e₂ : Q($α) := q(OfNat.ofNat $d : $α)
          pure q($e₁ / $e₂)
    let _i : Q(Neg $α) ← synthInstanceQ q(Neg $α)
    pure q(-$e)
#align expr.of_rat Qq.ofRatₓ

-- instance cache is no more
#noalign tactic.instance_cache.of_rat
