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
It may leave a side-goal of the form `d' ≤ d`, in case it is not entirely successful.

See the doc-string for more details.

##  Future work

* Deal with equalities, instead of inequalities (i.e. implement `compute_degree`).
* Add functionality to deal with (some) exponents that are not closed natural numbers.
* Add support for proving goals of the from `natDegree f ≠ 0` and `degree f ≠ 0`.
* Make sure that `degree` and `natDegree` are equally supported.

##  Implementation details

We start with a goal of the form `natDegree f ≤ d` or `degree f ≤ d`.
Recurse into `f` breaking apart sums, products and powers.  Take care of numerals,
`C a, X (^ n), monomial a n` separately.
-/

section Tactic

open Polynomial

namespace Mathlib.Tactic.ComputeDegree

section mylemmas

/-!
###  Simple lemmas about `natDegree`

The lemmas in this section deduce inequalities of the form `natDegree f ≤ d`, using
inequalities of the same shape.
This allows a recursive application of the `compute_degree_le` tactic on a goal,
and on all the resulting subgoals.
-/

variable {R : Type _}

section semiring
variable [Semiring R]

theorem add {a b : Nat} {f g : R[X]} (hf : natDegree f ≤ a) (hg : natDegree g ≤ b) :
    natDegree (f + g) ≤ max a b :=
(f.natDegree_add_le g).trans $ max_le_max ‹_› ‹_›

theorem mul {a b : Nat} {f g : R[X]} (hf : natDegree f ≤ a) (hg : natDegree g ≤ b) :
    natDegree (f * g) ≤ a + b :=
(f.natDegree_mul_le).trans $ add_le_add ‹_› ‹_›

theorem pow {a : Nat} (b : Nat) {f : R[X]} (hf : natDegree f ≤ a) :
    natDegree (f ^ b) ≤ b * a :=
natDegree_pow_le.trans (Nat.mul_le_mul rfl.le ‹_›)

theorem C_le (a : R) : natDegree (C a) ≤ 0 := (natDegree_C a).le
theorem nat_cast_le (n : Nat) : natDegree (n : R[X]) ≤ 0 := (natDegree_nat_cast _).le
theorem zero_le : natDegree (↑0 : R[X]) ≤ 0 := natDegree_zero.le
theorem one_le : natDegree (↑1 : R[X]) ≤ 0 := natDegree_one.le

end semiring

section ring
variable [Ring R]

theorem neg {a : Nat} {f : R[X]} (hf : natDegree f ≤ a) : natDegree (- f) ≤ a :=
(natDegree_neg f).le.trans ‹_›

theorem sub {a b : Nat} {f g : R[X]} (hf : natDegree f ≤ a) (hg : natDegree g ≤ b) :
    natDegree (f - g) ≤ max a b :=
(f.natDegree_sub_le g).trans $ max_le_max ‹_› ‹_›

theorem int_cast_le (n : Int) : natDegree (n : R[X]) ≤ 0 := (natDegree_int_cast _).le

end ring

end mylemmas

open Lean Meta Elab.Tactic

/-!
Four helper lemmas to build `Expr`essions: `mkMax, mkPow, mkNatDegree, mkDegree`.
-/

/-- Return `max a b` using `Max.max`. This method assumes `a` and `b` have the same type. -/
def mkMax (a b : Expr) : MetaM Expr := mkAppM ``Max.max #[a, b]

/-- Return `a ^ b` using `HPow.hPow`. -/
def mkPow (a b : Expr) : MetaM Expr := mkAppM ``HPow.hPow #[a, b]

/-- Returns `natDegree pol`. -/
def mkNatDegree (pol : Expr) : MetaM Expr := mkAppM ``natDegree #[pol]

/-- Returns `degree pol`. -/
def mkDegree (pol : Expr) : MetaM Expr := mkAppM ``degree #[pol]

/-- `isDegLE e` checks whether `e` is an `Expr`ession is an inequality whose LHS is
the `natDegree/degree` of a polynomial with coefficients in a semiring `R`.
If `e` represents
*  `natDegree f ≤ d`, then it returns `(true,  f, d, R, instSemiRing)`;
*  `degree f ≤ d`,    then it returns `(false, f, d, R, instSemiRing)`;
*  anything else, then it throws an error.

Returning `R` and its `Semiring` instance is useful for simplifying `cDegCore`.
-/
def isDegLE (e : Expr) : CoreM (Bool × Expr × Expr × Expr × Expr) := do
  match e.consumeMData.getAppFnArgs with
    -- check that the target is an inequality `≤`...
    | (``LE.le, #[_, _, lhs, rhs]) => match lhs.getAppFnArgs with
      -- and that the LHS is `natDegree ...` or `degree ...`
      | (``degree, #[R, iSR, pol])    => return (false, pol, rhs, R, iSR)
      | (``natDegree, #[R, iSR, pol]) => return (true, pol, rhs, R, iSR)
      | (na, _) => throwError (f!"Expected an inequality of the form\n\n" ++
        f!"  'f.natDegree ≤ d'  or  'f.degree ≤ d',\n\ninstead, {na} appears on the LHS")
    | _ => throwError m!"Expected an inequality instead of '{e.getAppFnArgs.1}'"

open Lean Elab Term MVarId

/-- `cDegCore pol R iSR iR` takes as input `Expr`essions
*  `pol` representing a polynomial;
*  `R` representing the semiring of coefficients of `pol`;
*  `iSR` representing the Semiring instance on `R`;

and `iR : Option Expr`, representing the Ring instance on `R`, if there is one.
`cDegCore` recurses into `pol` producing an `Exp`ression representing a proof of
`natDegree f ≤ d`, where `d` is an appropriately constructed natural number.

Hopefully, the tactic should not really fail when the inputs are as specified.
-/
partial
def cDegCore (pol R iSR : Expr) (iR : Option Expr) : MetaM Expr := do
match pol.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, f, g]) => do
    mkAppOptM ``add #[R, iSR, none, none, none, none, ← cDegCore f R iSR iR, ← cDegCore g R iSR iR]
  | (``HSub.hSub, #[_, _, _, _, f, g]) => do
    mkAppOptM ``sub #[R, iR, none, none, none, none, ← cDegCore f R iSR iR, ← cDegCore g R iSR iR]
  | (``HMul.hMul, #[_, _, _, _, f, g]) => do
    mkAppOptM ``mul #[R, iSR, none, none, none, none, ← cDegCore f R iSR iR, ← cDegCore g R iSR iR]
  | (``HPow.hPow, #[_, (.const ``Nat []), _, _, f, n]) => do
    mkAppOptM ``pow #[R, iSR, none, n, none, ← cDegCore f R iSR iR]
  | (``Neg.neg,   #[_, _, f]) => do
    mkAppOptM ``neg #[R, iR, none, none, ← cDegCore f R iSR iR]
  | (``Polynomial.X, _) => do
    mkAppOptM ``natDegree_X_le #[R, iSR]
  -- can I avoid splitting `n = 0` from generic `n`?
  | (``OfNat.ofNat, #[_, (.lit (.natVal 0)), _]) => do
    mkAppOptM ``zero_le #[R, iSR]
  | (``OfNat.ofNat, #[_, n, _]) => do
    mkAppOptM ``nat_cast_le #[R, iSR, n]
  | (``Nat.cast, #[_, _, n]) => do
    mkAppOptM ``nat_cast_le #[R, iSR, n]
  | (``NatCast.natCast, #[_, _, n]) => do
    (mkAppOptM ``nat_cast_le #[R, iSR, n])
  | (``Int.cast, #[_, _, n]) => do
    mkAppOptM ``int_cast_le #[R, iR, n]
  | (``IntCast.intCast, #[_, _, n]) => do
    mkAppOptM ``int_cast_le #[R, iR, n]
  -- deal with `monomial` and `C`
  | (``FunLike.coe, #[_, _, _, _, polFun, c]) => match polFun.getAppFnArgs with
    | (``Polynomial.monomial, #[_, _, n]) => do
      mkAppOptM ``natDegree_monomial_le #[R, iSR, c, n]
    | (``Polynomial.C, _) => do
      mkAppOptM ``C_le #[R, iSR, c]
    | _ => do let ppP ← ppExpr polFun;
              throwError m!"'compute_degree_le' is not implemented for {ppP}"
  -- possibly, all that's left is the case where `pol` is an `fvar` and its `Name` is `.anonymous`
  | _ => mkAppOptM ``le_rfl #[none, none, ← mkNatDegree pol]

/--
`compute_degree_le` is a tactic to solve goals of the form `natDegree f ≤ d` or `degree f ≤ d`.

The tactic first replaces `natDegree f ≤ d` with `d' ≤ d`,
where `d'` is an internally computed guess for which the tactic proves the inequality
`natDegree f ≤ d'`.

Next, it applies `norm_num` to `d'`, in the hope of closing also the `d' ≤ d` goal.

The variant `compute_degree_le!` first applies `compute_degree_le`.
Then it uses `norm_num` on the whole inequality `d' ≤ d` and tries `assumption`.
-/
elab (name := computeDegreeLE) "compute_degree_le" : tactic => focus do
  let tgt := ← getMainTarget
  let (isNatDeg?, lhs, rhs, R, instSR) := ← isDegLE tgt
  let goal := ← getMainGoal
  let natDegGoal := ← match isNatDeg? with
    | true => do pure [goal]
    | false => do goal.apply (← mkAppM ``Iff.mp #[(← mkAppOptM ``natDegree_le_iff_degree_le
      #[R, instSR, lhs, ← mkAppM ``WithBot.unbot' #[(mkNatLit 0), rhs]])])
  guard (natDegGoal.length = 1) <|> throwError
    f!"'compute_degree_le': unexpected number of goals -- {natDegGoal.length} instead of 1!"
  let RR := ← mkAppM ``Ring #[R]
  let new := match ← trySynthInstance RR with | .some inst => some inst | _=> none
  let nfle_pf := ← cDegCore (← instantiateMVars lhs) R instSR new
  let nfle_typ := ← inferType nfle_pf
  let hDeg := ← getUnusedUserName `hDeg
  let newMVarId := ← (natDegGoal[0]!).assert hDeg nfle_typ nfle_pf
  let (ineq, new) := ← newMVarId.introN 1 [hDeg]
  -- `new` is a list of three `MVarId`s with goals `⊢ natDegree f ≤ ?_`, `⊢ ?_ ≤ d` and `⊢ ℕ`
  let new := ← new.apply (← mkConstWithFreshMVarLevels ``le_trans)
  -- the first `MVarId` unifies with `ineq`; this also assigns `⊢ ℕ`
  let ineq1 := ← new[0]!.withContext ineq[0]!.findDecl?
  let _ := ← (new[0]!).apply ineq1.get!.toExpr
  -- in the remaining goal, carried around by `new[1]`, we find and clear the hypothesis `ineq`
  let ineq := ← new[1]!.withContext ineq[0]!.findDecl?
  setGoals [← (new[1]!).clear ineq.get!.fvarId]
  evalTactic (← `(tactic| conv_lhs => norm_num))

@[inherit_doc computeDegreeLE]
elab (name := computeDegreeLE!) "compute_degree_le!" : tactic => focus do
  evalTactic (← `(tactic| compute_degree_le <;> norm_num <;> try assumption))

end Mathlib.Tactic.ComputeDegree
