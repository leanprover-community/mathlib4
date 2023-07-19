/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Data.Polynomial.Degree.Definitions

/-!

# `compute_degree_le` a tactic for computing degrees of polynomials

This file defines the tactic `compute_degree_le`.

Using `compute_degree_le` when the goal is of the form `natDegree f ≤ d` or `degree f ≤ d`,
tries to solve the goal.
It leaves a side-goal of the form `d' ≤ d`, in case it is not entirely successful.

See the doc-string for more details.

##  Future work

* Deal with equalities, instead of inequalities (i.e. implement `compute_degree`).
* Add support for proving goals of the from `natDegree f ≠ 0` and `degree f ≠ 0`.
* Make sure that `degree` and `natDegree` are equally supported.

##  Implementation details

We start with a goal of the form `natDegree f ≤ d` or `degree f ≤ d`.
Recurse into `f` breaking apart sums, products and powers.  Take care of numerals,
`C a, X (^ n), monomial a n` separately.

The recursion into `f` first converts `f` to a term of Type `DegInfo`.
This conversion preserves enough information of `f` to guide `compute_degree_le` into a proof.
-/

open Polynomial

namespace Mathlib.Tactic.ComputeDegree

section leaf_lemmas
/-!
###  Simple lemmas about `natDegree`

The lemmas in this section all have the form `natDegree <some form of cast> ≤ 0`.
Their proofs are weakenings of the stronger lemmas `natDegree <same> = 0`.
These are the lemmas called by `compute_degree_le` on (almost) all the leaves of its recursion.
-/

variable {R : Type _}

section semiring
variable [Semiring R]

theorem natDegree_C_le (a : R) : natDegree (C a) ≤ 0 := (natDegree_C a).le
theorem natDegree_nat_cast_le (n : ℕ) : natDegree (n : R[X]) ≤ 0 := (natDegree_nat_cast _).le
theorem natDegree_zero_le : natDegree (0 : R[X]) ≤ 0 := natDegree_zero.le
theorem natDegree_one_le : natDegree (1 : R[X]) ≤ 0 := natDegree_one.le

end semiring

variable [Ring R] in
theorem natDegree_int_cast_le (n : ℤ) : natDegree (n : R[X]) ≤ 0 := (natDegree_int_cast _).le

end leaf_lemmas

section Tactic

open Lean Elab Tactic Meta

/-- `isDegLE e` checks whether `e` is an `Expr`ession representing an inequality whose LHS is
the `natDegree/degree` of a polynomial with coefficients in a semiring `R`.
If `e` represents
*  `natDegree f ≤ d`, then it returns `(true,  f)`;
*  `degree f ≤ d`,    then it returns `(false, f)`;
*  anything else, then it throws an error.
-/
def isDegLE (e : Expr) : CoreM (Bool × Expr) := do
  match e.consumeMData.getAppFnArgs with
    -- check that the target is an inequality `≤`...
    | (``LE.le, #[_, _, lhs, _rhs]) => match lhs.getAppFnArgs with
      -- and that the LHS is `natDegree ...` or `degree ...`
      | (``degree, #[_R, _iSR, pol])    => return (false, pol)
      | (``natDegree, #[_R, _iSR, pol]) => return (true, pol)
      | (na, _) => throwError (m!"Expected an inequality of the form\n\n" ++
        f!"  'f.natDegree ≤ d'  or  'f.degree ≤ d',\n\ninstead, {na} appears on the LHS")
    | (na, _)  => throwError m!"Expected an inequality instead of '{na}', '{e}'"

/-- `computeDegreeLECore pol mv π` takes as input
* an `Expr`ession `pol` representing a polynomial;
* an `MVarId` `mv`;
* a function `π : Name × Name → Name`, typically
* * `pi = Prod.fst` if the goal is `natDegree f ≤ d`,
* * `pi = Prod.snd` if the goal is `degree f ≤ d`.

It recurses into `pol` matching each step with the appropriate pair of lemmas:
the first if the goal involves `natDegree`, the second if it involves `degree`.
It applies the lemma at each stage and continues until it reaches a "leaf":
either the final goal asks for the degree of a "cast" of some sort, of `X`, of `monomial n r`
or of an `fvar`.
In each case it closes the goal, assuming that the goal is `natDegree f ≤ natDegree f` or
`degree f ≤ degree f`, in the case of an `fvar`.
-/
partial
def computeDegreeLECore (pol : Expr) (mv : MVarId) (π : Name × Name → Name) :
    MetaM (List (Expr × MVarId)) := do
let (fg, names) := match pol.numeral? with
-- can I avoid the tri-splitting `n = 0`, `n = 1`, and generic `n`?
| some 0 => ([], (``natDegree_zero_le, ``degree_zero_le))
| some 1 => ([], (``natDegree_one_le, ``degree_one_le))
| some _ => ([], (``natDegree_nat_cast_le, ``degree_nat_cast_le))
| none => match pol.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, f, g]) =>
    ([f, g], (``natDegree_add_le_of_le, ``degree_add_le_of_le))
  | (``HSub.hSub, #[_, _, _, _, f, g]) =>
    ([f, g], (``natDegree_sub_le_of_le, ``degree_sub_le_of_le))
  | (``HMul.hMul, #[_, _, _, _, f, g]) =>
    ([f, g], (``natDegree_mul_le_of_le, ``degree_mul_le_of_le))
  | (``HPow.hPow, #[_, _, _, _, f, _]) =>
    ([f], (``natDegree_pow_le_of_le, ``degree_pow_le_of_le))
  | (``Neg.neg,   #[_, _, f]) =>
    ([f], (``natDegree_neg_le_of_le, ``degree_neg_le_of_le))
  | (``Polynomial.X, _) =>
    ([], (``natDegree_X_le, ``degree_X_le))
  | (``Nat.cast, _) =>
    ([], (``natDegree_nat_cast_le, ``degree_nat_cast_le))
  | (``NatCast.natCast, _) =>
    ([], (``natDegree_nat_cast_le, ``degree_nat_cast_le))
  | (``Int.cast, _) =>
    ([], (``natDegree_int_cast_le, ``degree_int_cast_le))
  | (``IntCast.intCast, _) =>
    ([], (``natDegree_int_cast_le, ``degree_int_cast_le))
  | (``FunLike.coe, #[_, _, _, _, polFun, _]) => match polFun.getAppFnArgs with
    | (``Polynomial.monomial, #[_, _, _]) =>
      ([], (``natDegree_monomial_le, ``degree_monomial_le))
    | (``Polynomial.C, _) =>
      ([], (``natDegree_C_le, ``degree_C_le))
    | _ =>
      ([polFun], (.anonymous, .anonymous))
  | _ => ([], (``le_rfl, ``le_rfl))
if π names == .anonymous then
  throwError m!"'compute_degree_le' is not implemented for {← ppExpr fg[0]!}"
return (← (fg.zip (← mv.applyConst (π names))).mapM fun (p, m) => computeDegreeLECore p m π).join

/-- Allows the syntax expression `compute_degree_le !`, with optional `!`. -/
syntax (name := computeDegreeLE) "compute_degree_le" "!"? : tactic

/-- Allows writing `compute_degree_le!` with no space preceding `!`. -/
macro "compute_degree_le!" : tactic => `(tactic| compute_degree_le !)

open Elab.Tactic in
/--
`compute_degree_le` is a tactic to solve goals of the form `natDegree f ≤ d` or `degree f ≤ d`.

The tactic first replaces `natDegree f ≤ d` with `d' ≤ d`,
where `d'` is an internally computed guess for which the tactic proves the inequality
`natDegree f ≤ d'`.

Next, it applies `norm_num` to `d'`, in the hope of closing also the `d' ≤ d` goal.

The variant `compute_degree_le!` first applies `compute_degree_le`.
Then it uses `norm_num` on the whole inequality `d' ≤ d` and tries `assumption`.
-/
elab_rules : tactic | `(tactic| compute_degree_le $[!%$str]?) => focus do
  let (isNatDeg?, lhs) := ← isDegLE (← getMainTarget)
  let π := if isNatDeg? then Prod.fst else Prod.snd
  -- if the goal is `natDegree f ≤ d`, then `le_goals = [natDegree f ≤ ?m,  ?m ≤ d,  ℕ]`
  -- if the goal is `degree f ≤ d`,    then `le_goals = [degree f ≤ ?m,     ?m ≤ d,  WithBot ℕ]`
  let le_goals := ← (← getMainGoal).applyConst ``le_trans
  let prf := ← computeDegreeLECore lhs (le_goals[0]!) π
  guard (prf == []) <|> throwError m!"'compute_degree_le' should have closed {prf}"
  setGoals [le_goals[1]!]
  if str.isSome then evalTactic (← `(tactic| norm_num <;> try assumption))
  else evalTactic (← `(tactic| conv_lhs => norm_num))

end Tactic

end Mathlib.Tactic.ComputeDegree
