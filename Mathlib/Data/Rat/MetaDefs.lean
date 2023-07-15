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
  (_ : Q(OfNat $α $(z.natAbs))) : Q($α) :=
  if 0 ≤ z then q($z.natAbs : $α) else q(-$z.natAbs : $α)
/-- `Rat.toExprQ α _ _ q _ _` embeds `q` as a numeral expression inside a type with `OfNat`, `-`, and `/`.
-/
def Rat.toExprQ {u : Lean.Level} (α : Q(Type u)) (_ : Q(Neg $α)) (_ : Q(Div $α)) (q : ℚ)
  (_ : Q(OfNat $α $(q.num.natAbs)))
  (_ : Q(OfNat $α $(q.den))) : Q($α) :=
  let num : ℤ := q.num
  let nume := num.toExprQ α ‹_›
  if q.den = 1 then nume
  else
    let dene := q($(q.den) : $α)
    q($nume / $dene)
#align rat.mk_numeral rat.toExprQₓ

section


/-- `rat.reflect q` represents the rational number `q` as a numeral expression of type `ℚ`. -/
instance Rat.instToExpr : Lean.ToExpr ℚ where
  toTypeExpr := q(ℚ)
  toExpr q := q.toExprQ q(ℚ) _ _

#align rat.reflect Rat.instToExpr

end

/-
`rat.to_pexpr q` creates a `pexpr` that will evaluate to `q`.
The `pexpr` does not hold any typing information:
`to_expr ``((%%(rat.to_pexpr (3/4)) : K))` will create a native `K` numeral `(3/4 : K)`.
-/
#noalign rat.to_pexpr

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Evaluates an expression as a rational number,
      if that expression represents a numeral or the quotient of two numerals. -/
    protected
    unsafe
  def
    expr.to_nonneg_rat
    : expr → Option ℚ
    |
        q( $ ( e₁ ) / $ ( e₂ ) )
        =>
        do
          let m ← e₁ . toNat
            let n ← e₂ . toNat
            if
              c
              :
              m n
              then
              if h : 1 < n then return ⟨ m , n , lt_trans zero_lt_one h , c ⟩ else none
              else
              none
      | e => do let n ← e . toNat return n
#align expr.to_nonneg_rat expr.to_nonneg_rat

/-- Evaluates an expression as a rational number,
if that expression represents a numeral, the quotient of two numerals,
the negation of a numeral, or the negation of the quotient of two numerals. -/
protected unsafe def expr.to_rat : expr → Option ℚ
  | q(Neg.neg $(e)) => do
    let q ← e.to_nonneg_rat
    some (-q)
  | e => e.to_nonneg_rat
#align expr.to_rat expr.to_rat

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Evaluates an expression into a rational number, if that expression is built up from
        numerals, +, -, *, /, ⁻¹  -/
    protected
    unsafe
  def
    expr.eval_rat
    : expr → Option ℚ
    | q( Zero.zero ) => some 0
      | q( One.one ) => some 1
      | q( bit0 $ ( q ) ) => ( · * · ) 2 <$> q . eval_rat
      | q( bit1 $ ( q ) ) => ( · + · ) 1 <$> ( · * · ) 2 <$> q . eval_rat
      | q( $ ( a ) + $ ( b ) ) => ( · + · ) <$> a . eval_rat <*> b . eval_rat
      | q( $ ( a ) - $ ( b ) ) => Sub.sub <$> a . eval_rat <*> b . eval_rat
      | q( $ ( a ) * $ ( b ) ) => ( · * · ) <$> a . eval_rat <*> b . eval_rat
      | q( $ ( a ) / $ ( b ) ) => ( · / · ) <$> a . eval_rat <*> b . eval_rat
      | q( - $ ( a ) ) => Neg.neg <$> a . eval_rat
      | q( $ ( a ) ⁻¹ ) => Inv.inv <$> a . eval_rat
      | _ => none
#align expr.eval_rat expr.eval_rat

/-- `expr.of_rat α q` embeds `q` as a numeral expression inside the type `α`.
Lean will try to infer the correct type classes on `α`, and the tactic will fail if it cannot.
This function is similar to `rat.mk_numeral` but it takes fewer hypotheses and is tactic valued.
-/
protected unsafe def expr.of_rat (α : expr) : ℚ → tactic expr
  | ⟨(n : ℕ), d, h, c⟩ => do
    let e₁ ← expr.of_nat α n
    if d = 1 then return e₁
      else do
        let e₂ ← expr.of_nat α d
        tactic.mk_app `` Div.div [e₁, e₂]
  | ⟨-[n+1], d, h, c⟩ => do
    let e₁ ← expr.of_nat α (n + 1)
    let e ←
      if d = 1 then return e₁
        else do
          let e₂ ← expr.of_nat α d
          tactic.mk_app `` Div.div [e₁, e₂]
    tactic.mk_app `` Neg.neg [e]
#align expr.of_rat expr.of_rat

namespace Tactic

namespace InstanceCache

/-- `c.of_rat q` embeds `q` as a numeral expression inside the type `α`.
Lean will try to infer the correct type classes on `c.α`, and the tactic will fail if it cannot.
This function is similar to `rat.mk_numeral` but it takes fewer hypotheses and is tactic valued.
-/
protected unsafe def of_rat (c : instance_cache) : ℚ → tactic (instance_cache × expr)
  | ⟨(n : ℕ), d, _, _⟩ =>
    if d = 1 then c.ofNat n
    else do
      let (c, e₁) ← c.ofNat n
      let (c, e₂) ← c.ofNat d
      c `` Div.div [e₁, e₂]
  | ⟨-[n+1], d, _, _⟩ => do
    let (c, e) ←
      if d = 1 then c.ofNat (n + 1)
        else do
          let (c, e₁) ← c.ofNat (n + 1)
          let (c, e₂) ← c.ofNat d
          c `` Div.div [e₁, e₂]
    c `` Neg.neg [e]
#align tactic.instance_cache.of_rat tactic.instance_cache.of_rat

end InstanceCache

end Tactic
