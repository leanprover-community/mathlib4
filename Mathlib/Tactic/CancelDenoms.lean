/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

! This file was ported from Lean 3 source module tactic.cancel_denoms
! leanprover-community/mathlib commit eaa771fc4f5f356afeacac4ab92e0cbf10b0b1df
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Rat.MetaDefs
import Mathbin.Tactic.NormNum
import Mathbin.Data.Tree
import Mathbin.Meta.Expr

/-!
# A tactic for canceling numeric denominators

This file defines tactics that cancel numeric denominators from field expressions.

As an example, we want to transform a comparison `5*(a/3 + b/4) < c/3` into the equivalent
`5*(4*a + 3*b) < 4*c`.

## Implementation notes

The tooling here was originally written for `linarith`, not intended as an interactive tactic.
The interactive version has been split off because it is sometimes convenient to use on its own.
There are likely some rough edges to it.

Improving this tactic would be a good project for someone interested in learning tactic programming.
-/


namespace CancelFactors

/-! ### Lemmas used in the procedure -/


theorem mul_subst {α} [CommRing α] {n1 n2 k e1 e2 t1 t2 : α} (h1 : n1 * e1 = t1) (h2 : n2 * e2 = t2)
    (h3 : n1 * n2 = k) : k * (e1 * e2) = t1 * t2 := by
  rw [← h3, mul_comm n1, mul_assoc n2, ← mul_assoc n1, h1, ← mul_assoc n2, mul_comm n2, mul_assoc,
    h2]
#align cancel_factors.mul_subst CancelFactors.mul_subst

theorem div_subst {α} [Field α] {n1 n2 k e1 e2 t1 : α} (h1 : n1 * e1 = t1) (h2 : n2 / e2 = 1)
    (h3 : n1 * n2 = k) : k * (e1 / e2) = t1 := by
  rw [← h3, mul_assoc, mul_div_left_comm, h2, ← mul_assoc, h1, mul_comm, one_mul]
#align cancel_factors.div_subst CancelFactors.div_subst

theorem cancel_factors_eq_div {α} [Field α] {n e e' : α} (h : n * e = e') (h2 : n ≠ 0) :
    e = e' / n :=
  eq_div_of_mul_eq h2 <| by rwa [mul_comm] at h
#align cancel_factors.cancel_factors_eq_div CancelFactors.cancel_factors_eq_div

theorem add_subst {α} [Ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) :
    n * (e1 + e2) = t1 + t2 := by simp [left_distrib, *]
#align cancel_factors.add_subst CancelFactors.add_subst

theorem sub_subst {α} [Ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) :
    n * (e1 - e2) = t1 - t2 := by simp [left_distrib, *, sub_eq_add_neg]
#align cancel_factors.sub_subst CancelFactors.sub_subst

theorem neg_subst {α} [Ring α] {n e t : α} (h1 : n * e = t) : n * -e = -t := by simp [*]
#align cancel_factors.neg_subst CancelFactors.neg_subst

theorem cancel_factors_lt {α} [LinearOrderedField α] {a b ad bd a' b' gcd : α} (ha : ad * a = a')
    (hb : bd * b = b') (had : 0 < ad) (hbd : 0 < bd) (hgcd : 0 < gcd) :
    (a < b) = (1 / gcd * (bd * a') < 1 / gcd * (ad * b')) :=
  by
  rw [mul_lt_mul_left, ← ha, ← hb, ← mul_assoc, ← mul_assoc, mul_comm bd, mul_lt_mul_left]
  exact mul_pos had hbd
  exact one_div_pos.2 hgcd
#align cancel_factors.cancel_factors_lt CancelFactors.cancel_factors_lt

theorem cancel_factors_le {α} [LinearOrderedField α] {a b ad bd a' b' gcd : α} (ha : ad * a = a')
    (hb : bd * b = b') (had : 0 < ad) (hbd : 0 < bd) (hgcd : 0 < gcd) :
    (a ≤ b) = (1 / gcd * (bd * a') ≤ 1 / gcd * (ad * b')) :=
  by
  rw [mul_le_mul_left, ← ha, ← hb, ← mul_assoc, ← mul_assoc, mul_comm bd, mul_le_mul_left]
  exact mul_pos had hbd
  exact one_div_pos.2 hgcd
#align cancel_factors.cancel_factors_le CancelFactors.cancel_factors_le

theorem cancel_factors_eq {α} [LinearOrderedField α] {a b ad bd a' b' gcd : α} (ha : ad * a = a')
    (hb : bd * b = b') (had : 0 < ad) (hbd : 0 < bd) (hgcd : 0 < gcd) :
    (a = b) = (1 / gcd * (bd * a') = 1 / gcd * (ad * b')) :=
  by
  rw [← ha, ← hb, ← mul_assoc bd, ← mul_assoc ad, mul_comm bd]
  ext; constructor
  · rintro rfl
    rfl
  · intro h
    simp only [← mul_assoc] at h
    refine' mul_left_cancel₀ (mul_ne_zero _ _) h
    apply mul_ne_zero
    apply div_ne_zero
    all_goals apply ne_of_gt <;> first |assumption|exact zero_lt_one
#align cancel_factors.cancel_factors_eq CancelFactors.cancel_factors_eq

open Tactic Expr

/-! ### Computing cancelation factors -/


open Tree

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      `find_cancel_factor e` produces a natural number `n`, such that multiplying `e` by `n` will
      be able to cancel all the numeric denominators in `e`. The returned `tree` describes how to
      distribute the value `n` over products inside `e`.
      -/
    unsafe
  def
    find_cancel_factor
    : expr → ℕ × Tree ℕ
    |
        q( $ ( e1 ) + $ ( e2 ) )
        =>
        let
          ( v1 , t1 ) := find_cancel_factor e1
          let ( v2 , t2 ) := find_cancel_factor e2 let lcm := v1 . lcm v2 ( lcm , node lcm t1 t2 )
      |
        q( $ ( e1 ) - $ ( e2 ) )
        =>
        let
          ( v1 , t1 ) := find_cancel_factor e1
          let ( v2 , t2 ) := find_cancel_factor e2 let lcm := v1 . lcm v2 ( lcm , node lcm t1 t2 )
      |
        q( $ ( e1 ) * $ ( e2 ) )
        =>
        let
          ( v1 , t1 ) := find_cancel_factor e1
          let ( v2 , t2 ) := find_cancel_factor e2 let pd := v1 * v2 ( pd , node pd t1 t2 )
      |
        q( $ ( e1 ) / $ ( e2 ) )
        =>
        match
          e2 . to_nonneg_rat
          with
          |
              some q
              =>
              let
                ( v1 , t1 ) := find_cancel_factor e1
                let
                  n := v1 . lcm q . num . natAbs
                  ( n , node n t1 ( node q . num . natAbs Tree.nil Tree.nil ) )
            | none => ( 1 , node 1 Tree.nil Tree.nil )
      | q( - $ ( e ) ) => find_cancel_factor e
      | _ => ( 1 , node 1 Tree.nil Tree.nil )
#align cancel_factors.find_cancel_factor cancel_factors.find_cancel_factor

/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      `mk_prod_prf n tr e` produces a proof of `n*e = e'`, where numeric denominators have been
      canceled in `e'`, distributing `n` proportionally according to `tr`.
      -/
    unsafe
  def
    mk_prod_prf
    : ℕ → Tree ℕ → expr → tactic expr
    |
        v , node _ lhs rhs , q( $ ( e1 ) + $ ( e2 ) )
        =>
        do
          let v1 ← mk_prod_prf v lhs e1
            let v2 ← mk_prod_prf v rhs e2
            mk_app ` ` add_subst [ v1 , v2 ]
      |
        v , node _ lhs rhs , q( $ ( e1 ) - $ ( e2 ) )
        =>
        do
          let v1 ← mk_prod_prf v lhs e1
            let v2 ← mk_prod_prf v rhs e2
            mk_app ` ` sub_subst [ v1 , v2 ]
      |
        v , node n ( lhs @ ( node ln _ _ ) ) rhs , q( $ ( e1 ) * $ ( e2 ) )
        =>
        do
          let tp ← infer_type e1
            let v1 ← mk_prod_prf ln lhs e1
            let v2 ← mk_prod_prf ( v / ln ) rhs e2
            let ln' ← tp . ofNat ln
            let vln' ← tp . ofNat ( v / ln )
            let v' ← tp . ofNat v
            let ntp ← to_expr ` `( $ ( ln' ) * $ ( vln' ) = $ ( v' ) )
            let ( _ , npf ) ← solve_aux ntp sorry
            mk_app ` ` mul_subst [ v1 , v2 , npf ]
      |
        v , node n lhs rhs @ ( node rn _ _ ) , q( $ ( e1 ) / $ ( e2 ) )
        =>
        do
          let tp ← infer_type e1
            let v1 ← mk_prod_prf ( v / rn ) lhs e1
            let rn' ← tp . ofNat rn
            let vrn' ← tp . ofNat ( v / rn )
            let n' ← tp . ofNat n
            let v' ← tp . ofNat v
            let ntp ← to_expr ` `( $ ( rn' ) / $ ( e2 ) = 1 )
            let ( _ , npf ) ← solve_aux ntp sorry
            let ntp2 ← to_expr ` `( $ ( vrn' ) * $ ( n' ) = $ ( v' ) )
            let ( _ , npf2 ) ← solve_aux ntp2 sorry
            mk_app ` ` div_subst [ v1 , npf , npf2 ]
      | v , t , q( - $ ( e ) ) => do let v' ← mk_prod_prf v t e mk_app ` ` neg_subst [ v' ]
      |
        v , _ , e
        =>
        do
          let tp ← infer_type e
            let v' ← tp . ofNat v
            let e' ← to_expr ` `( $ ( v' ) * $ ( e ) )
            mk_app `eq.refl [ e' ]
#align cancel_factors.mk_prod_prf cancel_factors.mk_prod_prf

/--
Given `e`, a term with rational division, produces a natural number `n` and a proof of `n*e = e'`,
where `e'` has no division. Assumes "well-behaved" division.
-/
unsafe def derive (e : expr) : tactic (ℕ × expr) :=
  let (n, t) := find_cancel_factor e
  Prod.mk n <$> mk_prod_prf n t e <|>
    throwError
      "cancel_factors.derive failed to normalize {← e}. Are you sure this is well-behaved division?"
#align cancel_factors.derive cancel_factors.derive

/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Given `e`, a term with rational divison, produces a natural number `n` and a proof of `e = e' / n`,
      where `e'` has no divison. Assumes "well-behaved" division.
      -/
    unsafe
  def
    derive_div
    ( e : expr ) : tactic ( ℕ × expr )
    :=
      do
        let ( n , p ) ← derive e
          let tp ← infer_type e
          let n' ← tp . ofNat n
          let tgt ← to_expr ` `( $ ( n' ) ≠ 0 )
          let ( _ , pn ) ← solve_aux tgt sorry
          Prod.mk n
            <$>
            mk_mapp ` ` cancel_factors_eq_div [ none , none , n' , none , none , p , pn ]
#align cancel_factors.derive_div cancel_factors.derive_div

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      `find_comp_lemma e` arranges `e` in the form `lhs R rhs`, where `R ∈ {<, ≤, =}`, and returns
      `lhs`, `rhs`, and the `cancel_factors` lemma corresponding to `R`.
      -/
    unsafe
  def
    find_comp_lemma
    : expr → Option ( expr × expr × Name )
    | q( $ ( a ) < $ ( b ) ) => ( a , b , ` ` cancel_factors_lt )
      | q( $ ( a ) ≤ $ ( b ) ) => ( a , b , ` ` cancel_factors_le )
      | q( $ ( a ) = $ ( b ) ) => ( a , b , ` ` cancel_factors_eq )
      | q( $ ( a ) ≥ $ ( b ) ) => ( b , a , ` ` cancel_factors_le )
      | q( $ ( a ) > $ ( b ) ) => ( b , a , ` ` cancel_factors_lt )
      | _ => none
#align cancel_factors.find_comp_lemma cancel_factors.find_comp_lemma

/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
/-- `cancel_denominators_in_type h` assumes that `h` is of the form `lhs R rhs`,
where `R ∈ {<, ≤, =, ≥, >}`.
It produces an expression `h'` of the form `lhs' R rhs'` and a proof that `h = h'`.
Numeric denominators have been canceled in `lhs'` and `rhs'`.
-/
unsafe def cancel_denominators_in_type (h : expr) : tactic (expr × expr) := do
  let some (lhs, rhs, lem) ← return <| find_comp_lemma h |
    fail "cannot kill factors"
  let (al, lhs_p) ← derive lhs
  let (ar, rhs_p) ← derive rhs
  let gcd := al.gcd ar
  let tp ← infer_type lhs
  let al ← tp.ofNat al
  let ar ← tp.ofNat ar
  let gcd ← tp.ofNat gcd
  let al_pos ← to_expr ``(0 < $(al))
  let ar_pos ← to_expr ``(0 < $(ar))
  let gcd_pos ← to_expr ``(0 < $(gcd))
  let (_, al_pos) ← solve_aux al_pos sorry
  let (_, ar_pos) ← solve_aux ar_pos sorry
  let (_, gcd_pos) ← solve_aux gcd_pos sorry
  let pf ← mk_app lem [lhs_p, rhs_p, al_pos, ar_pos, gcd_pos]
  let pf_tp ← infer_type pf
  return ((find_comp_lemma pf_tp).elim default (Prod.fst ∘ Prod.snd), pf)
#align cancel_factors.cancel_denominators_in_type cancel_factors.cancel_denominators_in_type

end CancelFactors

/-! ### Interactive version -/


/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
open Tactic Expr CancelFactors

/-- `cancel_denoms` attempts to remove numerals from the denominators of fractions.
It works on propositions that are field-valued inequalities.

```lean
variables {α : Type} [linear_ordered_field α] (a b c : α)

example (h : a / 5 + b / 4 < c) : 4*a + 5*b < 20*c :=
begin
  cancel_denoms at h,
  exact h
end

example (h : a > 0) : a / 5 > 0 :=
begin
  cancel_denoms,
  exact h
end
```
-/
unsafe def tactic.interactive.cancel_denoms (l : parse location) : tactic Unit := do
  let locs ← l.get_locals
  tactic.replace_at cancel_denominators_in_type locs l >>= guardb <|>
      fail "failed to cancel any denominators"
  tactic.interactive.norm_num [simp_arg_type.symm_expr ``(mul_assoc)] l
#align tactic.interactive.cancel_denoms tactic.interactive.cancel_denoms

add_tactic_doc
  { Name := "cancel_denoms"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.cancel_denoms]
    tags := ["simplification"] }

