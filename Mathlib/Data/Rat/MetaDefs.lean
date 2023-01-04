/-
Copyright (c) 2019 Robert Y. Lewis . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

! This file was ported from Lean 3 source module data.rat.meta_defs
! leanprover-community/mathlib commit 44b58b42794e5abe2bf86397c38e26b587e07e59
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Rat.Defs
import Mathbin.Tactic.Core

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


/-- `rat.mk_numeral q` embeds `q` as a numeral expression inside a type with 0, 1, +, -, and /

`type`: an expression representing the target type. This must live in Type 0.
`has_zero`, `has_one`, `has_add`: expressions of the type `has_zero %%type`, etc.

This function is similar to `expr.of_rat` but takes more hypotheses and is not tactic valued.
 -/
unsafe def rat.mk_numeral (type has_zero has_one has_add has_neg has_div : expr) : ℚ → expr
  | ⟨Num, denom, _, _⟩ =>
    let nume := Num.mk_numeral type Zero One Add Neg
    if denom = 1 then nume
    else
      let dene := denom.mk_numeral type Zero One Add
      q(@Div.div.{0} $(type) $(Div) $(nume) $(dene))
#align rat.mk_numeral rat.mk_numeral

section

-- Note that here we are disabling the "safety" of reflected, to allow us to reuse `rat.mk_numeral`.
-- The usual way to provide the required `reflected` instance would be via rewriting to prove that
-- the expression we use here is equivalent.
attribute [local semireducible] reflected

/-- `rat.reflect q` represents the rational number `q` as a numeral expression of type `ℚ`. -/
unsafe instance rat.reflect : has_reflect ℚ :=
  rat.mk_numeral q(ℚ) q((by infer_instance : Zero ℚ)) q((by infer_instance : One ℚ))
    q((by infer_instance : Add ℚ)) q((by infer_instance : Neg ℚ)) q((by infer_instance : Div ℚ))
#align rat.reflect rat.reflect

end

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      `rat.to_pexpr q` creates a `pexpr` that will evaluate to `q`.
      The `pexpr` does not hold any typing information:
      `to_expr ``((%%(rat.to_pexpr (3/4)) : K))` will create a native `K` numeral `(3/4 : K)`.
      -/
    unsafe
  def
    rat.to_pexpr
    ( q : ℚ ) : pexpr
    :=
      let
        n := q . num
        let
          d := q . denom
          if d = 1 then n . to_pexpr else ` `( $ ( n . to_pexpr ) / $ ( d . to_pexpr ) )
#align rat.to_pexpr rat.to_pexpr

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

