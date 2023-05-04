/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import Mathlib.Tactic.NormNum
import Mathlib.Util.SynthesizeUsing
import Mathlib.Data.Tree

/-!
# A tactic for canceling numeric denominators

This file defines tactics that cancel numeric denominators from field Expressions.

As an example, we want to transform a comparison `5*(a/3 + b/4) < c/3` into the equivalent
`5*(4*a + 3*b) < 4*c`.

## Implementation notes

The tooling here was originally written for `linarith`, not intended as an interactive tactic.
The interactive version has been split off because it is sometimes convenient to use on its own.
There are likely some rough edges to it.

Improving this tactic would be a good project for someone interested in learning tactic programming.
-/

open Lean Parser Tactic Mathlib Meta NormNum Qq

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
    (a < b) = (1 / gcd * (bd * a') < 1 / gcd * (ad * b')) := by
  rw [mul_lt_mul_left, ← ha, ← hb, ← mul_assoc, ← mul_assoc, mul_comm bd, mul_lt_mul_left]
  exact mul_pos had hbd
  exact one_div_pos.2 hgcd
#align cancel_factors.cancel_factors_lt CancelFactors.cancel_factors_lt

theorem cancel_factors_le {α} [LinearOrderedField α] {a b ad bd a' b' gcd : α} (ha : ad * a = a')
    (hb : bd * b = b') (had : 0 < ad) (hbd : 0 < bd) (hgcd : 0 < gcd) :
    (a ≤ b) = (1 / gcd * (bd * a') ≤ 1 / gcd * (ad * b')) := by
  rw [mul_le_mul_left, ← ha, ← hb, ← mul_assoc, ← mul_assoc, mul_comm bd, mul_le_mul_left]
  exact mul_pos had hbd
  exact one_div_pos.2 hgcd
#align cancel_factors.cancel_factors_le CancelFactors.cancel_factors_le

theorem cancel_factors_eq {α} [LinearOrderedField α] {a b ad bd a' b' gcd : α} (ha : ad * a = a')
    (hb : bd * b = b') (had : 0 < ad) (hbd : 0 < bd) (hgcd : 0 < gcd) :
    (a = b) = (1 / gcd * (bd * a') = 1 / gcd * (ad * b')) := by
  rw [← ha, ← hb, ← mul_assoc bd, ← mul_assoc ad, mul_comm bd]
  ext; constructor
  · rintro rfl
    rfl
  · intro h
    simp only [← mul_assoc] at h
    refine' mul_left_cancel₀ (mul_ne_zero _ _) h
    apply mul_ne_zero
    apply div_ne_zero
    all_goals apply ne_of_gt ; first |assumption|exact zero_lt_one
#align cancel_factors.cancel_factors_eq CancelFactors.cancel_factors_eq

/-! ### Computing cancelation factors -/

/--
`findCancelFactor e` produces a natural number `n`, such that multiplying `e` by `n` will
be able to cancel all the numeric denominators in `e`. The returned `Tree` describes how to
distribute the value `n` over products inside `e`.
-/
partial def findCancelFactor (e : Expr) : ℕ × Tree ℕ :=
match e.getAppFnArgs with
| (`HAdd.hAdd, #[_, _, _, _, e1, e2]) | (`HSub.hSub, #[_, _, _, _, e1, e2]) =>
  let (v1, t1) := findCancelFactor e1
  let (v2, t2) := findCancelFactor e2
  let lcm := v1.lcm v2
  (lcm, .node lcm t1 t2)
| (`HMul.hMul, #[_, _, _, _, e1, e2]) =>
  let (v1, t1) := findCancelFactor e1
  let (v2, t2) := findCancelFactor e2
  let pd := v1 * v2
  (pd, .node pd t1 t2)
| (`HDiv.hDiv, #[_, _, _, _, e1, e2]) =>
  match isRatLit e2 with
  | some q =>
    let (v1, t1) := findCancelFactor e1
    let n := v1.lcm q.num.natAbs
    (n, .node n t1 <| .node q.num.natAbs .nil .nil)
  | none => (1, .node 1 .nil .nil)
| (`Neg.neg, #[_, _, e]) => findCancelFactor e
| _ => (1, .node 1 .nil .nil)

def norm_num_done : Elab.Tactic.TacticM Unit := do
  Lean.Elab.Tactic.evalTactic (←`(tactic| norm_num; done))

/--
`mkProdPrf n tr e` produces a proof of `n*e = e'`, where numeric denominators have been
canceled in `e'`, distributing `n` proportionally according to `tr`.
-/
partial def mkProdPrf (α : Q(Type u)) (_sα : Q(Field $α)) (v : ℕ) (t : Tree ℕ)
  (e : Q($α)) : MetaM Expr :=
match t, e with
| .node _ lhs rhs, ~q($e1 + $e2) => do
  let v1 ← mkProdPrf α _sα v lhs e1
  let v2 ← mkProdPrf α _sα v rhs e2
  mkAppM `CancelFactors.add_subst #[v1, v2]
| .node _ lhs rhs, ~q($e1 - $e2) => do
  let v1 ← mkProdPrf α _sα v lhs e1
  let v2 ← mkProdPrf α _sα v rhs e2
  mkAppM `CancelFactors.sub_subst #[v1, v2]
| .node _ lhs@(.node ln _ _) rhs, ~q($e1 * $e2) => do
  let v1 ← mkProdPrf α _sα ln lhs e1
  let v2 ← mkProdPrf α _sα (v / ln) rhs e2
  have ln' := (← mkOfNat α _sα <| mkRawNatLit ln).1
  have vln' := (← mkOfNat α _sα <| mkRawNatLit (v/ln)).1
  have v' := (← mkOfNat α _sα <| mkRawNatLit v).1
  let ntp : Q(Prop) := q($ln' * $vln' = $v')
  let npf ← synthesizeUsing ntp norm_num_done
  mkAppM `CancelFactors.mul_subst #[v1, v2, npf]
| .node n lhs (.node rn _ _), ~q($e1 / $e2) => do
  let v1 ← mkProdPrf α _sα (v / rn) lhs e1
  have rn' := (← mkOfNat α _sα <| mkRawNatLit v).1
  have vrn' := (← mkOfNat α _sα <| mkRawNatLit <| v / rn).1
  have n' := (← mkOfNat α _sα <| mkRawNatLit <| n).1
  have v' := (← mkOfNat α _sα <| mkRawNatLit <| v).1
  let ntp : Q(Prop) := q($rn' / $e2 = 1)
  let npf ← synthesizeUsing ntp norm_num_done
  let ntp2 : Q(Prop) := q($vrn' * $n' = $v')
  let npf2 ← synthesizeUsing ntp2 norm_num_done
  mkAppM `CancelFactors.div_subst #[v1, npf, npf2]
| t, ~q(-$e) => do
  let v ← mkProdPrf α _sα v t e
  mkAppM `CancelFactors.neg_subst #[v]
| _, _ => do
  let ⟨v, _⟩ ← mkOfNat α _sα <| mkRawNatLit v
  let e' ← mkAppM `Mul.mul #[v, e]
  mkAppM `Eq.refl #[e']

/--
Given `e`, a term with rational division, produces a natural number `n` and a proof of `n*e = e'`,
where `e'` has no division. Assumes "well-behaved" division.
-/
def derive (e : Expr) : MetaM (ℕ × Expr) := do
let (n, t) := findCancelFactor e
let tp : Q(Type) ← inferType e
let stp ← synthInstance q(Field $tp)
try
  return (n, ← mkProdPrf tp stp n t e)
catch E => do
  dbg_trace (← E.toMessageData.toString)
  throwError
    "CancelFactors.derive failed to normalize {e}. Are you sure this is well-behaved division?"

/--
`findCompLemma e` arranges `e` in the form `lhs R rhs`, where `R ∈ {<, ≤, =}`, and returns
`lhs`, `rhs`, and the `cancel_factors` lemma corresponding to `R`.
-/
def findCompLemma (e : Expr) : Option (Expr × Expr × Name) :=
match e.getAppFnArgs with
| (`LT.lt, #[_, _, a, b]) => (a, b, ``cancel_factors_lt)
| (`LE.le, #[_, _, a, b]) => (a, b, ``cancel_factors_le)
| (`Eq, #[_, a, b]) => (a, b, ``cancel_factors_eq)
| (`GE.ge, #[_, _, a, b]) => (b, a, ``cancel_factors_le)
| (`GT.gt, #[_, _, a, b]) => (b, a, ``cancel_factors_lt)
| _ => none

/--
`cancelDenominatorsInType h` assumes that `h` is of the form `lhs R rhs`,
where `R ∈ {<, ≤, =, ≥, >}`.
It produces an Expression `h'` of the form `lhs' R rhs'` and a proof that `h = h'`.
Numeric denominators have been canceled in `lhs'` and `rhs'`.
-/
def cancelDenominatorsInType (h : Expr) : MetaM (Expr × Expr) :=
do let some (lhs, rhs, lem) := findCompLemma h | throwError "cannot kill factors"
   let (al, lhs_p) ← derive lhs
   let α : Q(Type) ← inferType lhs_p
   let sα : Q(LinearOrderedField $α) ← synthInstance q(LinearOrderedField $α)
   let (ar, rhs_p) ← derive rhs
   let gcd := al.gcd ar
   have al := (← mkOfNat α sα <| mkRawNatLit al).1
   have ar := (← mkOfNat α sα <| mkRawNatLit ar).1
   have gcd := (← mkOfNat α sα <| mkRawNatLit gcd).1
   let al_pos : Q(Prop) := q(0 < $al)
   let ar_pos : Q(Prop) := q(0 < $ar)
   let gcd_pos : Q(Prop) := q(0 < $gcd)
   let al_pos ← synthesizeUsing al_pos norm_num_done
   let ar_pos ← synthesizeUsing ar_pos norm_num_done
   let gcd_pos ← synthesizeUsing gcd_pos norm_num_done
   let pf ← mkAppM lem #[lhs_p, rhs_p, al_pos, ar_pos, gcd_pos]
   let pf_tp ← inferType pf
   return ((findCompLemma pf_tp).elim default (Prod.fst ∘ Prod.snd), pf)

end CancelFactors

/--
`cancel_denoms` attempts to remove numerals from the denominators of fractions.
It works on propositions that are field-valued inequalities.

```lean
variable [LinearOrderedField α] (a b c : α)

example (h : a / 5 + b / 4 < c) : 4*a + 5*b < 20*c := by
  cancel_denoms at h
  exact h

example (h : a > 0) : a / 5 > 0 := by
  cancel_denoms
  exact h
```
-/
syntax (name := cancelDenoms) "cancel_denoms" (ppSpace location)? : tactic

open Elab Tactic

def cancelDenominatorsAt (fvar: FVarId) : TacticM Unit := do
  let t := (← fvar.getDecl).type
  let (new, eqPrf) ← CancelFactors.cancelDenominatorsInType t
  let goal ← getMainGoal
  let _ ← goal.replaceLocalDecl fvar new eqPrf
  return

def cancelDenominatorsTarget : TacticM Unit := do
  let goal ← getMainTarget
  let (new, eqPrf) ← CancelFactors.cancelDenominatorsInType goal
  let _ ← (← getMainGoal).replaceTargetEq new eqPrf
  return

def cancelDenominators (loc : Location) : TacticM Unit := do
  withLocation loc cancelDenominatorsAt cancelDenominatorsTarget
    (λ _ => throwError "Failed to cancel any denominators")

elab "cancel_denoms" loc:(location)? : tactic => do
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  cancelDenominators loc
  Lean.Elab.Tactic.evalTactic (←`(tactic| norm_num [←mul_assoc]))

variable [LinearOrderedField α] (a b c : α)

example (h : a / 5 + b / 4 < c) : 4*a + 5*b < 20*c := by
  cancel_denoms at h
  exact h

example (h : a > 0) : a / 5 > 0 := by
  cancel_denoms
  exact h
